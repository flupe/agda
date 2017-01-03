{
{-# OPTIONS_GHC -fno-warn-deprecated-flags   #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-tabs               #-}
{-# OPTIONS_GHC -fno-warn-unused-imports     #-}

{-# LANGUAGE BangPatterns #-}

{-| The lexer is generated by Alex (<http://www.haskell.org/alex>) and is an
    adaptation of GHC's lexer. The main lexing function 'lexer' is called by
    the "Agda.Syntax.Parser.Parser" to get the next token from the input.
-}
module Agda.Syntax.Parser.Lexer
    ( -- * The main function
      lexer
      -- * Lex states
    , normal, code
    , layout, empty_layout, bol, imp_dir
      -- * Alex generated functions
    , AlexReturn(..), alexScanUser
    ) where

-- -- import Data.List

import Agda.Syntax.Parser.Alex
import Agda.Syntax.Parser.Comments
#ifndef __HADDOCK__
import {-# SOURCE #-} Agda.Syntax.Parser.Layout
import {-# SOURCE #-} Agda.Syntax.Parser.LexActions
#endif
import Agda.Syntax.Parser.Monad
import Agda.Syntax.Parser.StringLiterals
import Agda.Syntax.Parser.Tokens
import Agda.Syntax.Literal

}

-- Unicode is not handled by the following regular expressions.
-- Instead, unicode characters are translated to 7-bit ASCII
-- by Agda.Syntax.Parser.LexActions.foolAlex in a preprocessing pass.

$digit       = 0-9
$hexdigit    = [ $digit a-f A-F ]
$alpha       = [ A-Z a-z _ ]
$op          = [ \- \! \# \$ \% \& \* \+ \/ \< \= \> \^ \| \~ \? \` \[ \] \, \: ]
$idstart     = [ $digit $alpha $op ]
$idchar      = [ $idstart ' \\ ]
$nonalpha    = $idchar # $alpha
$nonalphanum = $nonalpha # $digit
$white_notab = $white # \t
$white_nonl  = $white_notab # \n

@number      = $digit+ | "0x" $hexdigit+
@integer     = [\-]? @number
@exponent    = [eE] [\-\+]? @number
@float       = @integer \. @number @exponent? | @number @exponent

-- A name can't start with \x (to allow \x -> x).
-- Bug in alex: [ _ op ]+ doesn't seem to work!
@start = ($idstart # [_]) | \\ [ $nonalpha ]
@ident = @start $idchar* | [_] $idchar+

@namespace  = (@ident \.)*
@q_ident    = @namespace @ident

tokens :-

-- White space
<0,code,bol_,layout_,empty_layout_,imp_dir_>
    $white_nonl+    ;

<pragma_> $white_notab ;

-- Pragmas
<0,code>    "{-#"                      { begin pragma }
<pragma_>   "{-#"                      { symbol SymOpenPragma }
<pragma_>   "#-}"                      { endWith $ symbol SymClosePragma }
<pragma_>   "BUILTIN"                  { keyword KwBUILTIN }
<pragma_>   "CATCHALL"                 { keyword KwCATCHALL }
<pragma_>   "COMPILED"                 { keyword KwCOMPILED }
<pragma_>   "COMPILED_DATA"            { keyword KwCOMPILED_DATA }
<pragma_>   "COMPILED_DATA_UHC"        { keyword KwCOMPILED_DATA_UHC }
<pragma_>   "COMPILED_DECLARE_DATA"    { keyword KwCOMPILED_DECLARE_DATA }
<pragma_>   "COMPILED_EPIC"            { keyword KwCOMPILED_EPIC }
<pragma_>   "COMPILED_EXPORT"          { keyword KwCOMPILED_EXPORT }
<pragma_>   "COMPILED_JS"              { keyword KwCOMPILED_JS }
<pragma_>   "COMPILED_TYPE"            { keyword KwCOMPILED_TYPE }
<pragma_>   "COMPILED_UHC"             { keyword KwCOMPILED_UHC }
<pragma_>   "HASKELL"                  { keyword KwHASKELL }
<pragma_>   "DISPLAY"                  { keyword KwDISPLAY }
<pragma_>   "IMPORT"                   { keyword KwIMPORT }
<pragma_>   "IMPORT_UHC"               { keyword KwIMPORT_UHC }
<pragma_>   "IMPOSSIBLE"               { keyword KwIMPOSSIBLE }
<pragma_>   "INJECTIVE"                { keyword KwINJECTIVE }
<pragma_>   "INLINE"                   { keyword KwINLINE }
<pragma_>   "LINE"                     { keyword KwLINE }
<pragma_>   "MEASURE"                  { keyword KwMEASURE }
<pragma_>   "NO_POSITIVITY_CHECK"      { keyword KwNO_POSITIVITY_CHECK }
<pragma_>   "NO_TERMINATION_CHECK"     { keyword KwNO_TERMINATION_CHECK }
<pragma_>   "NON_TERMINATING"          { keyword KwNON_TERMINATING }
<pragma_>   "OPTIONS"                  { keyword KwOPTIONS }
<pragma_>   "POLARITY"                 { keyword KwPOLARITY }
<pragma_>   "REWRITE"                  { keyword KwREWRITE }
<pragma_>   "STATIC"                   { keyword KwSTATIC }
<pragma_>   "TERMINATING"              { keyword KwTERMINATING }
<pragma_>   . # [ $white ] +           { withInterval $ TokString }

-- Comments
    -- We need to rule out pragmas here. Usually longest match would take
    -- precedence, but in some states pragmas aren't valid but comments are.
<0,code,bol_,layout_,empty_layout_,imp_dir_>
    "{-" / { not' (followedBy '#') }    { nestedComment }
    -- A misplaced end-comment, like in @f {x-} = x-@ gives a parse error.
    "-}"                                { symbol SymEndComment }
    @ident "-}"                         { symbol SymEndComment }

-- Dashes followed by a name symbol should be parsed as a name.
<0,code,bol_,layout_,empty_layout_,imp_dir_>
   "--" .* / { keepComments .&&. (followedBy '\n' .||. eof) }
             { withInterval TokComment }
<0,code,bol_,layout_,empty_layout_,imp_dir_>
  "--" .* / { followedBy '\n' .||. eof } ;

-- We need to check the offside rule for the first token on each line.  We
-- should not check the offside rule for the end of file token or an
-- '\end{code}'
<0,code,imp_dir_> \n    { begin bol_ }
<bol_>
    {
        \n                  ;
--      ^ \\ "end{code}"    { end }
        () / { not' eof }       { offsideRule }
    }

-- After a layout keyword there is either an open brace (no layout) or the
-- indentation of the first token decides the column of the layout block.
<layout_>
    {   \n      ;
--      \{      { endWith openBrace }
        ()      { endWith newLayoutContext }
    }

-- The only rule for the empty_layout state. Generates a close brace.
<empty_layout_> ()              { emptyLayout }

-- Keywords
<0,code> let            { keyword KwLet }
<0,code> in             { keyword KwIn }
<0,code> where          { keyword KwWhere }
<0,code> field          { keyword KwField }
<0,code> with           { keyword KwWith }
<0,code> rewrite        { keyword KwRewrite }
<0,code> postulate      { keyword KwPostulate }
<0,code> primitive      { keyword KwPrimitive }
<0,code> open           { keyword KwOpen }
<0,code> import         { keyword KwImport }
<0,code> module         { keyword KwModule }
<0,code> data           { keyword KwData }
<0,code> codata         { keyword KwCoData }
<0,code> record         { keyword KwRecord }
<0,code> constructor    { keyword KwConstructor }
<0,code> inductive      { keyword KwInductive }
<0,code> coinductive    { keyword KwCoInductive }
<0,code> "eta-equality"    { keyword KwEta }
<0,code> "no-eta-equality" { keyword KwNoEta }
<0,code> infix          { keyword KwInfix }
<0,code> infixl         { keyword KwInfixL }
<0,code> infixr         { keyword KwInfixR }
<0,code> mutual         { keyword KwMutual }
<0,code> abstract       { keyword KwAbstract }
<0,code> private        { keyword KwPrivate }
<0,code> instance       { keyword KwInstance }
<0,code> overlap        { keyword KwOverlap }
<0,code> macro          { keyword KwMacro }
<0,code> Set            { keyword KwSet }
<0,code> forall         { keyword KwForall }
<0,code> Set @number    { withInterval' (read . drop 3) TokSetN }
<0,code> quoteGoal      { keyword KwQuoteGoal }
<0,code> quoteContext   { keyword KwQuoteContext }
<0,code> quote          { keyword KwQuote }
<0,code> quoteTerm      { keyword KwQuoteTerm }
<0,code> unquote        { keyword KwUnquote }
<0,code> unquoteDecl    { keyword KwUnquoteDecl }
<0,code> unquoteDef     { keyword KwUnquoteDef  }
<0,code> tactic         { keyword KwTactic }
<0,code> syntax         { keyword KwSyntax }
<0,code> pattern        { keyword KwPatternSyn }

-- The parser is responsible to put the lexer in the imp_dir_ state when it
-- expects an import directive keyword. This means that if you run the
-- tokensParser you will never see these keywords.
<0,code> using      { keyword KwUsing }
<0,code> hiding     { keyword KwHiding }
<0,code> renaming   { keyword KwRenaming }
<imp_dir_> to       { endWith $ keyword KwTo }
<0,code> public     { keyword KwPublic }

-- Holes
<0,code> "{!"           { hole }

-- Special symbols
<0,code> "..."          { symbol SymEllipsis }
<0,code> ".."           { symbol SymDotDot }
<0,code> "."            { symbol SymDot }
<0,code> ";"            { symbol SymSemi }
<0,code> ":"            { symbol SymColon }
<0,code> "="            { symbol SymEqual }
<0,code> "_"            { symbol SymUnderscore }
<0,code> "?"            { symbol SymQuestionMark }
<0,code> "|"            { symbol SymBar }
<0,code> "(|" /[$white] { symbol SymOpenIdiomBracket }
<0,code> "|)"           { symbol SymCloseIdiomBracket }
<0,code> "("            { symbol SymOpenParen }
<0,code> ")"            { symbol SymCloseParen }
<0,code> "->"           { symbol SymArrow }
<0,code> "\"            { symbol SymLambda } -- "
<0,code> "@"            { symbol SymAs }
<0,code> "{{" /[^!]             { symbol SymDoubleOpenBrace }
-- We don't lex '}}' into a SymDoubleCloseBrace. Instead, we lex it as
-- two SymCloseBrace's. When the parser is looking for a double
-- closing brace, it will also accept two SymCloseBrace's, after
-- verifying that they are immediately next to each other.
-- This trick allows us to keep "record { a = record {}}" working
-- properly.
-- <0,code> "}}"                { symbol SymDoubleCloseBrace }
<0,code> "{"            { symbol SymOpenBrace }     -- you can't use braces for layout
<0,code> "}"            { symbol SymCloseBrace }

-- Literals
<0,code> \'             { litChar }
<0,code> \"             { litString }
<0,code> @integer       { literal LitNat }
<0,code> @float         { literal LitFloat }

-- Identifiers
<0,code,imp_dir_> @q_ident      { identifier }
-- Andreas, 2013-02-21, added identifiers to the 'imp_dir_' state.
-- This is to fix issue 782: 'toz' should not be lexed as 'to'
-- (followed by 'z' after leaving imp_dir_).
-- With identifiers in state imp_dir_, 'toz' should be lexed as
-- identifier 'toz' in imp_dir_ state, leading to a parse error later.

{

-- | This is the initial state for parsing a regular, non-literate file.
normal :: LexState
normal = 0


{-| The layout state. Entered when we see a layout keyword ('withLayout') and
    exited either when seeing an open brace ('openBrace') or at the next token
    ('newLayoutContext').

    Update: we don't use braces for layout anymore.
-}
layout :: LexState
layout = layout_


{-| The state inside a pragma.
-}
pragma :: LexState
pragma = pragma_

{-| We enter this state from 'newLayoutContext' when the token following a
    layout keyword is to the left of (or at the same column as) the current
    layout context. Example:

    > data Empty : Set where
    > foo : Empty -> Nat

    Here the second line is not part of the @where@ clause since it is has the
    same indentation as the @data@ definition. What we have to do is insert an
    empty layout block @{}@ after the @where@. The only thing that can happen
    in this state is that 'emptyLayout' is executed, generating the closing
    brace. The open brace is generated when entering by 'newLayoutContext'.
-}
empty_layout :: LexState
empty_layout = empty_layout_


-- | This state is entered at the beginning of each line. You can't lex
--   anything in this state, and to exit you have to check the layout rule.
--   Done with 'offsideRule'.
bol :: LexState
bol = bol_


-- | This state can only be entered by the parser. In this state you can only
--   lex the keywords @using@, @hiding@, @renaming@ and @to@. Moreover they are
--   only keywords in this particular state. The lexer will never enter this
--   state by itself, that has to be done in the parser.
imp_dir :: LexState
imp_dir = imp_dir_


-- | Return the next token. This is the function used by Happy in the parser.
--
--   @lexer k = 'lexToken' >>= k@
lexer :: (Token -> Parser a) -> Parser a
lexer k = lexToken >>= k

-- | Do not use this function; it sets the 'ParseFlags' to
-- 'undefined'.
alexScan :: AlexInput -> Int -> AlexReturn (LexAction Token)

-- | This is the main lexing function generated by Alex.
alexScanUser :: ([LexState], ParseFlags) -> AlexInput -> Int -> AlexReturn (LexAction Token)

}

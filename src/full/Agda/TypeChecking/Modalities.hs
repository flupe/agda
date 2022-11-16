module Agda.TypeChecking.Modalities
  ( checkModality'
  , checkModality
  ) where

import Control.Monad.Except

import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Lens

import Agda.Interaction.Options

import Agda.Syntax.Common
-- import Agda.Syntax.Abstract
import Agda.Syntax.Abstract.Name

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Pretty

-- | The second argument is the definition of the first.
--   Returns 'Nothing' if ok, otherwise the error message.
checkRelevance' :: (MonadConversion m) => QName -> Definition -> m (Maybe TypeError)
checkRelevance' x def = do
  case getRelevance def of
    Relevant -> return Nothing -- relevance functions can be used in any context.
    drel -> do
      -- Andreas,, 2018-06-09, issue #2170
      -- irrelevant projections are only allowed if --irrelevant-projections
      ifM (return (isJust $ isProjection_ $ theDef def) `and2M`
           (not .optIrrelevantProjections <$> pragmaOptions)) {-then-} needIrrProj {-else-} $ do
        rel <- asksTC getRelevance
        reportSDoc "tc.irr" 50 $ vcat
          [ "declaration relevance =" <+> text (show drel)
          , "context     relevance =" <+> text (show rel)
          ]
        return $ if (drel `moreRelevant` rel) then Nothing else Just $ DefinitionIsIrrelevant x
  where
  needIrrProj = Just . GenericDocError <$> do
    sep [ "Projection " , prettyTCM x, " is irrelevant."
        , " Turn on option --irrelevant-projections to use it (unsafe)."
        ]

-- | The second argument is the definition of the first.
--   Returns 'Nothing' if ok, otherwise the error message.
checkQuantity' :: (MonadConversion m) => QName -> Definition -> m (Maybe TypeError)
checkQuantity' x def = do
  case getQuantity def of
    dq@Quantityω{} -> do
      reportSDoc "tc.irr" 50 $ vcat
        [ "declaration quantity =" <+> text (show dq)
        -- , "context     quantity =" <+> text (show q)
        ]
      return Nothing -- Abundant definitions can be used in any context.
    dq -> do
      q <- asksTC getQuantity
      reportSDoc "tc.irr" 50 $ vcat
        [ "declaration quantity =" <+> text (show dq)
        , "context     quantity =" <+> text (show q)
        ]
      return $ if (dq `moreQuantity` q) then Nothing else Just $ DefinitionIsErased x

-- | The second argument is the definition of the first.
--   Returns 'Nothing' if ok, otherwise the error message.
checkCohesion' :: (MonadConversion m) => QName -> Definition -> m (Maybe TypeError)
checkCohesion' x def = do
  let dc = getCohesion def
  c <- asksTC getCohesion
  reportSDoc "tc.mod.coh" 50 $ vcat
    [ "declaration cohesion =" <+> text (show dc)
    , "context     cohesion =" <+> text (show c)
    ]
  return $ if (dc `moreCohesion` c) then Nothing else Just $ DefinitionHasWrongCohesion x dc

-- | The second argument is the definition of the first.
--   Returns 'Nothing' if ok, otherwise the error message.
checkPolarity' :: (MonadConversion m) => QName -> Definition -> m (Maybe TypeError)
checkPolarity' x def = do
  let dp = getModalPolarity def
  p <- asksTC $ getModalPolarity
  reportSDoc "tc.mod.pol" 50 $ vcat
    [ "declaration polarity =" <+> text (show dp)
    , "context     polarity =" <+> text (show p)
    ]
  return $ if (dp `morePolarity` p) then Nothing else Just $ DefinitionHasWrongPolarity x dp p

-- | The second argument is the definition of the first.
checkModality' :: (MonadConversion m) => QName -> Definition -> m (Maybe TypeError)
checkModality' x def = do
  relOk <- checkRelevance' x def
  quantOk <- maybe (checkQuantity' x def) (return . Just) relOk
  cohOk <- maybe (checkCohesion' x def) (return . Just) quantOk
  maybe (checkPolarity' x def) (return . Just) cohOk

-- | The second argument is the definition of the first.
checkModality :: (MonadConversion m) => QName -> Definition -> m ()
checkModality x def = justToError $ checkModality' x def
  where
  justToError m = maybe (return ()) typeError =<< m

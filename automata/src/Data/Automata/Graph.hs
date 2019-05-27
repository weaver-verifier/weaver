{-# LANGUAGE
    BlockArguments,
    ExistentialQuantification,
    PatternSynonyms,
    RankNTypes,
    ScopedTypeVariables,
    TypeApplications,
    UndecidableInstances,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Data.Automata.Graph where

import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (execStateT, get, modify, put, runState)
import Data.Functor.Identity (Identity (..))
import Data.Finite.Class (Finitary (..), memoizeF, Fun (..), size)
import Data.Finite.Internal (Finite (..))
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.Map ((!), empty, member, insert)
import Data.Vector.Sized (index, withSizedList)

data GraphM m e = ∀ q. Finitary q ⇒ UnfoldM (q → m (e q)) q

type Graph = GraphM Identity

pattern Unfold ∷ () ⇒ Finitary q ⇒ (q → e q) → q → Graph e
pattern Unfold next root ← UnfoldM (fmap runIdentity → next) root
  where Unfold next root = UnfoldM (fmap Identity      next) root
{-# COMPLETE Unfold #-}

raise ∷ Applicative m ⇒ Graph e → GraphM m e
raise (UnfoldM next root) = UnfoldM (fmap (pure . runIdentity) next) root

lower ∷ Applicative m ⇒ GraphM m e → m (Graph e)
lower (UnfoldM next root) = (`UnfoldM` root) . getFun <$> traverse (fmap Identity) (Fun next)

memoize ∷ MonadIO m ⇒ GraphM m e → m (GraphM m e)
memoize (UnfoldM next root) = do
  Fun next' ← sequence (Fun \state → do
    thunk ← liftIO (newIORef Nothing)
    return do
      entry ← liftIO (readIORef thunk)
      case entry of
        Just edge → return edge
        Nothing   → do edge ← next state
                       liftIO (writeIORef thunk (Just edge))
                       return edge)
  return (UnfoldM next' root)

optimize ∷ (Foldable e, Functor e) ⇒ Graph e → Graph e
optimize = runIdentity . optimizeM

optimizeM ∷ (Monad m, Foldable e, Functor e) ⇒ GraphM m e → m (Graph e)
optimizeM (UnfoldM next root) = unfoldM next root

unfold ∷ (Foldable e, Functor e, Ord q) ⇒ (q → e q) → q → Graph e
unfold next = runIdentity . unfoldM (Identity . next)

unfoldM ∷ (Monad m, Foldable e, Functor e, Ord q) ⇒ (q → m (e q)) → q → m (Graph e)
unfoldM next root = do
  let explore state = do
        (cache, edges) ← get
        unless (member state cache) do
          edge ← lift (next state)
          put (insert state (length cache) cache, edge:edges)
          mapM_ explore edge

  (cache, edges) ← execStateT (explore root) (empty, [])
  withSizedList (reverse edges) \vec →
    let indexOf state = Finite (fromIntegral (cache ! state))
        next' = fmap (fmap indexOf) vec
        root' = indexOf root
    in pure (Unfold (index next') root')

data Annot r e q = Annot r (e q)

annot ∷ Annot r e q → r
annot (Annot x _) = x

fix ∷ (Foldable e, Eq r) ⇒ (∀ q. Finitary q ⇒ (q → r) → e q → r) → r → Graph e → Graph (Annot r e)
fix acc seed = fixCut acc seed (const False)
{-# INLINE fix #-}

fixCut ∷ (Foldable e, Eq r) ⇒ (∀ q. Finitary q ⇒ (q → r) → e q → r) → r → (r → Bool) → Graph e → Graph (Annot r e)
fixCut acc seed cut (Unfold next root) =
  let loop first table =
        let (table', updated) = runState (memoizeF calc) False
            calc state = do
              let edge = next  state
                  old  = table state
                  new  = acc (snd . find) edge
                  diff = first || (any (fst . find) edge && snd old /= new)
                  find child | state < child = table' child
                             | otherwise     = table  child
              modify (|| diff)
              pure (diff, if diff then new else snd old)
        in if not (cut (snd (table root))) && updated
             then loop False table'
             else table
      annots = loop True (\_ → (False, seed))
  in Unfold (\q → Annot (snd (annots q)) (next q)) root
{-# INLINE fixCut #-}

fold ∷ (Foldable e, Eq r) ⇒ (∀ q. Finitary q ⇒ (q → r) → e q → r) → r → Graph e → r
fold acc seed = foldCut acc seed (const False)
{-# INLINE fold #-}

foldCut ∷ (Foldable e, Eq r) ⇒ (∀ q. Finitary q ⇒ (q → r) → e q → r) → r → (r → Bool) → Graph e → r
foldCut acc seed cut graph =
  case fixCut acc seed cut graph of
    Unfold next root → annot (next root)
{-# INLINE foldCut #-}

vertices ∷ Integral a ⇒ GraphM m e → a
vertices (UnfoldM _ (_ ∷ q)) = size @q

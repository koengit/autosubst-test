module Main where

import Test.QuickCheck
import Control.Monad( liftM2 )
import Data.List (nub, sort)

-- | de Bruijn variables
data Var
  = Z  -- here
  | S Var -- suc
  | LookupR Ren Var -- _⍟ᵣ_
  deriving (Eq, Show, Ord)

arbVar :: Int -> Gen Var
arbVar n = frequency
  [ (1, return Z)
  , (n, fmap S (arbVar n1))
  , (n, liftM2 LookupR (arbRen n2) (arbVar n2))
  ]
 where
  n1 = n-1
  n2 = n `div` 2

instance Arbitrary Var where
  arbitrary = sized arbVar

  shrink (S v)         = [ v ]
  shrink (LookupR r v) = [ v ]
                      ++ [ LookupR r' v | r' <- shrink r ]
                      ++ [ LookupR r v' | v' <- shrink v ]  
  shrink _             = []

-- | Expressions, with explicit renaming and substitution
data Expr
  = VarE Var -- `_
  | Lam   Expr -- λx_
  | App   Expr Expr -- _·_
  | RenE Expr Ren -- _⋯ᵣ_
  | SubE Expr Sub -- _⋯ₛ_
  | LookupS Sub Var -- _⍟ₛ_
  deriving (Eq, Show, Ord)

arbExpr :: Int -> Gen Expr
arbExpr n = frequency
  [ (1, fmap VarE (arbVar n))
  , (n, fmap Lam (arbExpr n1))
  , (n, liftM2 App (arbExpr n2) (arbExpr n2))
  , (n, liftM2 SubE (arbExpr n2) (arbSub n2))
  , (n, liftM2 LookupS (arbSub n2) (arbVar n))
  ]
 where
  n1 = n-1
  n2 = n `div` 2

instance Arbitrary Expr where
  arbitrary = sized arbExpr

  shrink (VarE v)   = [ VarE v' | v' <- shrink v ]
  shrink (Lam e)    = [ e ]
                   ++ [ Lam e' | e' <- shrink e ]
  shrink (App a b)  = [ a, b ]
                   ++ [ App a' b | a' <- shrink a ]
                   ++ [ App a b' | b' <- shrink b ]
  shrink (RenE a r) = [ a ]
                   ++ [ RenE a' r | a' <- shrink a ]
                   ++ [ RenE a r' | r' <- shrink r ]
  shrink (SubE a s) = [ a ]
                   ++ [ SubE a' s | a' <- shrink a ]
                   ++ [ SubE a s' | s' <- shrink s ]
  shrink (LookupS s v) = expr s
                   ++ [ LookupS s' v | s' <- shrink s ]
                   ++ [ LookupS s v' | v' <- shrink v ]
   where
    expr (ConsS e s)  = e : expr s
    expr (CompRS _ s) = expr s
    expr (CompSR s _) = expr s
    expr (CompSS s t) = expr s ++ expr t
    expr _            = []


-- | Renamings
data Ren
  = IdR -- idᵣ
  | WkR -- wkᵣ
  | ConsR Var Ren -- _∷ᵣ_
  | CompRR Ren Ren -- _⨟ᵣᵣ_
  deriving (Eq, Show, Ord)

arbRen :: Int -> Gen Ren
arbRen n = frequency
  [ (1, return IdR)
  , (1, return WkR)
  , (n, liftM2 ConsR (arbVar n2) (arbRen n2))
  , (n, liftM2 CompRR (arbRen n2) (arbRen n2))
  ]
 where
  n1 = n-1
  n2 = n `div` 2

instance Arbitrary Ren where
  arbitrary = sized arbRen

  shrink IdR          = []
  shrink WkR          = [ IdR ]
  shrink (ConsR v r)  = [ r ]
                     ++ [ ConsR v' r | v' <- shrink v ]
                     ++ [ ConsR v r' | r' <- shrink r ]
  shrink (CompRR r u)  = [ r, u ]
                     ++ [ CompRR r' u | r' <- shrink r ]
                     ++ [ CompRR r u' | u' <- shrink u ]

-- | Substitutions
data Sub
  = IdS -- idₛ
  | ConsS Expr Sub -- _∷ₛ_
  | CompRS Ren Sub -- _⨟ᵣₛ_
  | CompSR Sub Ren -- _⨟ₛᵣ_
  | CompSS Sub Sub -- _⨟ₛₛ_
  deriving (Eq, Show, Ord)

arbSub :: Int -> Gen Sub
arbSub n = frequency
  [ (1, return IdS)
  , (n, liftM2 ConsS  (arbExpr n2) (arbSub n2))
  , (n, liftM2 CompRS (arbRen n) (arbSub n2))
  , (n, liftM2 CompSR (arbSub n2) (arbRen n))
  , (n, liftM2 CompSS (arbSub n2) (arbSub n2))
  ]
 where
  n1 = n-1
  n2 = n `div` 2

instance Arbitrary Sub where
  arbitrary = sized arbSub

  shrink IdS          = []
  shrink (ConsS e s)  = [ s ]
                     ++ [ ConsS e' s | e' <- shrink e ]
                     ++ [ ConsS e s' | s' <- shrink s ]
  shrink (CompRS r u)  = [ u ]
                     ++ [ CompRS r' u | r' <- shrink r ]
                     ++ [ CompRS r u' | u' <- shrink u ]
  shrink (CompSR r u)  = [ r ]
                     ++ [ CompSR r' u | r' <- shrink r ]
                     ++ [ CompSR r u' | u' <- shrink u ]
  shrink (CompSS r u)  = [ r, u ]
                     ++ [ CompSS r' u | r' <- shrink r ]
                     ++ [ CompSS r u' | u' <- shrink u ]

-- | Wrapper for any term
data Term
  = TE Expr
  | TR Ren
  | TS Sub
  deriving (Eq, Show, Ord)

main = quickCheckWith stdArgs{ maxSuccess = 10000 } prop_Confluent

prop_Terminates e =
  whenFail (
    do printTrace (TE e)
  ) $ fuel 10000 (TE e)
 where
  fuel n t = case step t of
               []   -> True
               t':_ -> if n > 0 then fuel (n-1) t' else False

printTrace t = go 1 t
 where
  go n t = do putStrLn (show n ++ ": " ++ show t)
              case step t of
                t':_ -> do putStrLn "-->"
                           go (n+1) t'
                []   -> return ()

data Fork = Fork [Term] deriving ( Eq, Ord )

instance Arbitrary Fork where
  arbitrary =
    do e <- arbitrary
       tr <- arbTrace (TE e)
       return (Fork tr)
   where
    arbTrace t =
      case step t of
        [] -> return [t]
        ts -> do t' <- elements ts
                 (t:) `fmap` arbTrace t'

  shrink (Fork [TE e,_]) =
    [ Fork [t1',t2']
    | e' <- shrink e ++ [ e' | TE e' <- step (TE e) ]
    , let t1' = TE e'
    , t2' <- drop 1 $ step t1'
    ]

  shrink (Fork ts) =
    [ Fork (take (k+1) ts)
    , Fork (drop k ts)
    ]
   where
    k = length ts `div` 2

prop_Confluent (Blind (Fork ts)) =
  whenFail (
    do putStrLn "==TRACE#1=="
       printTrace (head ts)

       putStrLn "==TRACE#2=="
       putStrLn ("0: " ++ show (head ts))
       putStrLn "-->"
       printTrace (last ts)
  ) (norm (head ts) == norm (last ts))
 where
  norm t = case step t of
             []   -> t
             t':_ -> norm t'

  arbNorm t =
    case step t of
      [] -> return t
      ts -> do t' <- elements ts
               arbNorm t'

-- | Compute all one-step rewrites for a term, including contextual rewrites
step :: Term -> [Term]
step t = nub $ stepTop t ++ stepContext t

-- | Create stepTop function that tries all rules
stepTop :: Term -> [Term]
stepTop t = concat [
    -- ⋯ᵣ-def₁ : (` x) ⋯ᵣ ρ ≡ ` (ρ ⍟ᵣ x)
    tryRenVar t,
    -- ⋯ᵣ-def₂ : (λx e) ⋯ᵣ ρ ≡ λx (e ⋯ᵣ (ρ ↑ᵣ _))
    tryRenLam t,
    -- ⋯ᵣ-def₃ : (e₁ · e₂) ⋯ᵣ ρ ≡ (e₁ ⋯ᵣ ρ) · (e₂ ⋯ᵣ ρ)
    tryRenApp t,
    -- ⋯ₛ-def₁ : (` x) ⋯ₛ σ ≡ (σ ⍟ₛ x)
    trySubVar t,
    -- ⋯ₛ-def₂ : (λx e) ⋯ₛ σ ≡ λx (e ⋯ₛ (σ ↑ₛ _))
    trySubLam t,
    -- ⋯ₛ-def₃ : (e₁ · e₂) ⋯ₛ σ ≡ (e₁ ⋯ₛ σ) · (e₂ ⋯ₛ σ)
    trySubApp t,
    -- ⍟ᵣ-def₁ : (ρ : n →ᵣ m) → (x ∷ᵣ ρ) ⍟ᵣ (zero) ≡ x
    tryLookupRConsZ t,
    -- ⍟ᵣ-def₂ : (ρ : n →ᵣ m) → (x ∷ᵣ ρ) ⍟ᵣ (suc x') ≡ ρ ⍟ᵣ x'
    tryLookupRConsS t,
    -- idᵣ-def : (x : Fin n) → idᵣ ⍟ᵣ x ≡ x
    tryLookupRId t,
    -- wkᵣ-def : (x : Fin n) → (wkᵣ {s = s'}) ⍟ᵣ x ≡ suc x
    tryLookupRWk t,
    -- ∷ᵣ-def₁ : (x : Fin m) (ρ : n →ᵣ m) → (x ∷ᵣ ρ) ⍟ᵣ (zero) ≡ x
    tryConsRDef1 t,
    -- ∷ᵣ-def₂ : (x : Fin m) (x' : s' ∈ n) (ρ : n →ᵣ m) → (x ∷ᵣ ρ) ⍟ᵣ (suc x') ≡ ρ ⍟ᵣ x'
    tryConsRDef2 t,
    -- ⍟ₛ-def₁ : (σ : n →ₛ m) → (t ∷ₛ σ) ⍟ₛ (zero) ≡ t
    tryLookupSConsZ t,
    -- ⍟ₛ-def₂ : (σ : n →ₛ m) → (t ∷ₛ σ) ⍟ₛ (suc x) ≡ σ ⍟ₛ x
    tryLookupSConsS t,
    -- idₛ-def : (x : Fin n) → idₛ ⍟ₛ x ≡ ` x
    tryLookupSId t,
    -- ∷ₛ-def₁ : (e : Expr m) (σ : n →ₛ m) → (e ∷ₛ σ) ⍟ₛ (zero) ≡ T
    tryConsSDef1 t,
    -- ∷ₛ-def₂ : (e : Expr m) (x : s' ∈ n) (σ : n →ₛ m) → (e ∷ₛ σ) ⍟ₛ (suc x) ≡ σ ⍟ₛ x
    tryConsSDef2 t,
    -- ⨟ᵣᵣ-def : (ρ₁ : n →ᵣ m) (ρ₂ : m →ᵣ k) (x : Fin n) → (ρ₁ ⨟ᵣᵣ ρ₂) ⍟ᵣ x ≡ ρ₂ ⍟ᵣ (ρ₁ ⍟ᵣ x)
    tryCompRRDef t,
    -- ⨟ᵣₛ-def : (ρ₁ : n →ᵣ m) (σ₂ : m →ₛ k) (x : Fin n) → (ρ₁ ⨟ᵣₛ σ₂) ⍟ₛ x ≡ σ₂ ⍟ₛ (ρ₁ ⍟ᵣ x)
    tryCompRSDef t,
    -- ⨟ₛᵣ-def : (σ₁ : n →ₛ m) (ρ₂ : m →ᵣ k) (x : Fin n) → (σ₁ ⨟ₛᵣ ρ₂) ⍟ₛ x ≡ (σ₁ ⍟ₛ x) ⋯ᵣ ρ₂
    tryCompSRDef t,
    -- ⨟ₛₛ-def : (σ₁ : n →ₛ m) (σ₂ : m →ₛ k) (x : Fin n) → (σ₁ ⨟ₛₛ σ₂) ⍟ₛ x ≡ (σ₁ ⍟ₛ x) ⋯ₛ σ₂
    tryCompSSDef t,
    -- interactᵣ : (x : Fin m) (ρ : n →ᵣ m) → wkᵣ ⨟ᵣᵣ (x ∷ᵣ ρ) ≡ ρ
    tryInteractR t,
    -- interactₛ : (e : Expr m) (σ : n →ₛ m) → wkᵣ ⨟ᵣₛ (e ∷ₛ σ) ≡ σ
    tryInteractS t,
    -- η-idᵣ : _∷ᵣ_ {s = s} {n = S} (zero) wkᵣ ≡ idᵣ
    tryEtaIdR t,
    -- η-idₛ : _∷ₛ_ {s = s} {n = S} (` zero) (wkᵣ ⨟ᵣₛ idₛ) ≡ idₛ
    tryEtaIdS t,
    -- η-lawᵣ : (ρ : (suc n) →ᵣ m) → (ρ ⍟ᵣ (zero)) ∷ᵣ (wkᵣ ⨟ᵣᵣ ρ) ≡ ρ
    tryEtaLawR t,
    -- η-lawₛ : (σ : (suc n) →ₛ m) → (σ ⍟ₛ (zero)) ∷ₛ (wkᵣ ⨟ᵣₛ σ) ≡ σ
    tryEtaLawS t,
    -- distributivityᵣᵣ : (x : Fin m) (ρ₁ : n →ᵣ m) (ρ₂ : m →ᵣ k) → (x ∷ᵣ ρ₁) ⨟ᵣᵣ ρ₂ ≡ (ρ₂ ⍟ᵣ x) ∷ᵣ (ρ₁ ⨟ᵣᵣ ρ₂)
    tryDistRR t,
    -- distributivityᵣₛ : (x : Fin m) (ρ₁ : n →ᵣ m) (σ₂ : m →ₛ k) → (x ∷ᵣ ρ₁) ⨟ᵣₛ σ₂ ≡ (σ₂ ⍟ₛ x) ∷ₛ (ρ₁ ⨟ᵣₛ σ₂)
    tryDistRS t,
    -- distributivityₛᵣ : (e : Expr m) (σ₁ : n →ₛ m) (ρ₂ : m →ᵣ k) → (e ∷ₛ σ₁) ⨟ₛᵣ ρ₂ ≡ (e ⋯ᵣ ρ₂) ∷ₛ (σ₁ ⨟ₛᵣ ρ₂)
    tryDistSR t,
    -- distributivityₛₛ : (e : Expr m) (σ₁ : n →ₛ m) (σ₂ : m →ₛ k) → (e ∷ₛ σ₁) ⨟ₛₛ σ₂ ≡ (e ⋯ₛ σ₂) ∷ₛ (σ₁ ⨟ₛₛ σ₂)
    tryDistSS t,
    -- ⋯idᵣ : (e : Expr n) → e ⋯ᵣ idᵣ ≡ e 
    tryRenId t,
    -- ⋯idₛ : (e : Expr n) → e ⋯ₛ idₛ ≡ e 
    trySubId t,
    -- left-idᵣᵣ : (ρ : n →ᵣ m) → idᵣ ⨟ᵣᵣ ρ ≡ ρ 
    tryLeftIdRR t,
    -- right-idᵣᵣ : (ρ : n →ᵣ m) → ρ ⨟ᵣᵣ idᵣ ≡ ρ
    tryRightIdRR t,
    -- left-idᵣₛ : (σ : n →ₛ m) → idᵣ ⨟ᵣₛ σ ≡ σ
    tryLeftIdRS t,
    -- left-idₛᵣ : (ρ : n →ᵣ m) → idₛ ⨟ₛᵣ ρ ≡ ρ ⨟ᵣₛ idₛ
    tryLeftIdSR t,
    -- left-idₛₛ : (σ : n →ₛ m) → idₛ ⨟ₛₛ σ ≡ σ
    tryLeftIdSS t,
    -- right-idₛᵣ : (σ : n →ₛ m) → σ ⨟ₛᵣ idᵣ ≡ σ
    tryRightIdSR t,
    -- right-idₛₛ : (σ : n →ₛ m) → σ ⨟ₛₛ idₛ ≡ σ 
    tryRightIdSS t,
    -- compositionalityᵣᵣ : (ρ₁ : n →ᵣ m) (ρ₂ : m →ᵣ k) (e : Expr n) → (e ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ e ⋯ᵣ (ρ₁ ⨟ᵣᵣ ρ₂)
    tryCompRR t,
    -- compositionalityᵣₛ : (ρ₁ : n →ᵣ m) (σ₂ : m →ₛ k) (e : Expr n) → (e ⋯ᵣ ρ₁) ⋯ₛ σ₂ ≡ e ⋯ₛ (ρ₁ ⨟ᵣₛ σ₂)
    tryCompRS t,
    -- compositionalityₛᵣ : (σ₁ : n →ₛ m) (ρ₂ : m →ᵣ k) (e : Expr n) → (e ⋯ₛ σ₁) ⋯ᵣ ρ₂ ≡ e ⋯ₛ (σ₁ ⨟ₛᵣ ρ₂)
    tryCompSR t,
    -- compositionalityₛₛ : (σ₁ : n →ₛ m) (σ₂ : m →ₛ k) (e : Expr n) → (e ⋯ₛ σ₁) ⋯ₛ σ₂ ≡ e ⋯ₛ (σ₁ ⨟ₛₛ σ₂)
    tryCompSS t,
    -- associativityᵣᵣᵣ : (ρ₁ : n →ᵣ m) (ρ₂ : m →ᵣ k) (ρ₃ : k →ᵣ S₄) → (ρ₁ ⨟ᵣᵣ ρ₂) ⨟ᵣᵣ ρ₃ ≡ ρ₁ ⨟ᵣᵣ (ρ₂ ⨟ᵣᵣ ρ₃)
    tryAssocRRR t,
    -- associativityᵣᵣₛ : (ρ₁ : n →ᵣ m) (ρ₂ : m →ᵣ k) (σ₃ : k →ₛ S₄) → (ρ₁ ⨟ᵣᵣ ρ₂) ⨟ᵣₛ σ₃ ≡ ρ₁ ⨟ᵣₛ (ρ₂ ⨟ᵣₛ σ₃)
    tryAssocRRS t,
    -- associativityᵣₛᵣ : (ρ₁ : n →ᵣ m) (σ₂ : m →ₛ k) (ρ₃ : k →ᵣ S₄) → (ρ₁ ⨟ᵣₛ σ₂) ⨟ₛᵣ ρ₃ ≡ ρ₁ ⨟ᵣₛ (σ₂ ⨟ₛᵣ ρ₃)
    tryAssocRSR t,
    -- associativityᵣₛₛ : (ρ₁ : n →ᵣ m) (σ₂ : m →ₛ k) (σ₃ : k →ₛ S₄) → (ρ₁ ⨟ᵣₛ σ₂) ⨟ₛₛ σ₃ ≡ ρ₁ ⨟ᵣₛ (σ₂ ⨟ₛₛ σ₃)
    tryAssocRSS t,
    -- associativityₛᵣᵣ : (σ₁ : n →ₛ m) (ρ₂ : m →ᵣ k) (ρ₃ : k →ᵣ S₄) → (σ₁ ⨟ₛᵣ ρ₂) ⨟ₛᵣ ρ₃ ≡ σ₁ ⨟ₛᵣ (ρ₂ ⨟ᵣᵣ ρ₃)
    tryAssocSRR t,
    -- associativityₛᵣₛ : (σ₁ : n →ₛ m) (ρ₂ : m →ᵣ k) (σ₃ : k →ₛ S₄) → (σ₁ ⨟ₛᵣ ρ₂) ⨟ₛₛ σ₃ ≡ σ₁ ⨟ₛₛ (ρ₂ ⨟ᵣₛ σ₃)
    tryAssocSRS t,
    -- associativityₛₛᵣ : (σ₁ : n →ₛ m) (σ₂ : m →ₛ k) (ρ₃ : k →ᵣ S₄) → (σ₁ ⨟ₛₛ σ₂) ⨟ₛᵣ ρ₃ ≡ σ₁ ⨟ₛₛ (σ₂ ⨟ₛᵣ ρ₃)
    tryAssocSSR t,
    -- associativityₛₛₛ : (σ₁ : n →ₛ m) (σ₂ : m →ₛ k) (σ₃ : k →ₛ S₄) → (σ₁ ⨟ₛₛ σ₂) ⨟ₛₛ σ₃ ≡ σ₁ ⨟ₛₛ (σ₂ ⨟ₛₛ σ₃)
    tryAssocSSS t,
    -- coincidence : (ρ : n →ᵣ m) (e : Expr n) → e ⋯ₛ (ρ ⨟ᵣₛ idₛ) ≡ e ⋯ᵣ ρ
    tryCoincidence t
  ]

-- | Rule implementations
tryRenVar :: Term -> [Term]
tryRenVar (TE (RenE (VarE x) r)) = [TE (VarE (LookupR r x))]
tryRenVar _ = []

tryRenLam :: Term -> [Term]
tryRenLam (TE (RenE (Lam e) r)) = [TE (Lam (RenE e (liftRen r)))]
tryRenLam _ = []

tryRenApp :: Term -> [Term]
tryRenApp (TE (RenE (App e1 e2) r)) = [TE (App (RenE e1 r) (RenE e2 r))]
tryRenApp _ = []

trySubVar :: Term -> [Term]
trySubVar (TE (SubE (VarE x) s)) = [TE (LookupS s x)]
trySubVar _ = []

trySubLam :: Term -> [Term]
trySubLam (TE (SubE (Lam e) s)) = [TE (Lam (SubE e (liftSub s)))]
trySubLam _ = []

trySubApp :: Term -> [Term]
trySubApp (TE (SubE (App e1 e2) s)) = [TE (App (SubE e1 s) (SubE e2 s))]
trySubApp _ = []

tryLookupRConsZ :: Term -> [Term]
tryLookupRConsZ (TE (VarE (LookupR (ConsR x _) Z))) = [TE (VarE x)]
tryLookupRConsZ _ = []

tryLookupRConsS :: Term -> [Term]
tryLookupRConsS (TE (VarE (LookupR (ConsR _ r) (S x')))) = [TE (VarE (LookupR r x'))]
tryLookupRConsS _ = []

tryLookupRId :: Term -> [Term]
tryLookupRId (TE (VarE (LookupR IdR x))) = [TE (VarE x)]
tryLookupRId _ = []

tryLookupRWk :: Term -> [Term]
tryLookupRWk (TE (VarE (LookupR WkR x))) = [TE (VarE (S x))]
tryLookupRWk _ = []

tryConsRDef1 :: Term -> [Term]
tryConsRDef1 (TE (VarE (LookupR (ConsR x _) Z))) = [TE (VarE x)]
tryConsRDef1 _ = []

tryConsRDef2 :: Term -> [Term]
tryConsRDef2 (TE (VarE (LookupR (ConsR _ r) (S x')))) = [TE (VarE (LookupR r x'))]
tryConsRDef2 _ = []

tryLookupSConsZ :: Term -> [Term]
tryLookupSConsZ (TE (LookupS (ConsS t _) Z)) = [TE t]
tryLookupSConsZ _ = []

tryLookupSConsS :: Term -> [Term]
tryLookupSConsS (TE (LookupS (ConsS _ s) (S x))) = [TE (LookupS s x)]
tryLookupSConsS _ = []

tryLookupSId :: Term -> [Term]
tryLookupSId (TE (LookupS IdS x)) = [TE (VarE x)]
tryLookupSId _ = []

tryConsSDef1 :: Term -> [Term]
tryConsSDef1 (TE (LookupS (ConsS t _) Z)) = [TE t]
tryConsSDef1 _ = []

tryConsSDef2 :: Term -> [Term]
tryConsSDef2 (TE (LookupS (ConsS _ s) (S x))) = [TE (LookupS s x)]
tryConsSDef2 _ = []

tryCompRRDef :: Term -> [Term]
tryCompRRDef (TE (VarE (LookupR (CompRR r1 r2) x))) = [TE (VarE (LookupR r2 (LookupR r1 x)))]
tryCompRRDef _ = []

tryCompRSDef :: Term -> [Term]
tryCompRSDef (TE (LookupS (CompRS r1 s2) x)) = [TE (LookupS s2 (LookupR r1 x))]
tryCompRSDef _ = []

tryCompSRDef :: Term -> [Term]
tryCompSRDef (TE (LookupS (CompSR s1 r2) x)) = [TE (RenE (LookupS s1 x) r2)]
tryCompSRDef _ = []

tryCompSSDef :: Term -> [Term]
tryCompSSDef (TE (LookupS (CompSS s1 s2) x)) = [TE (SubE (LookupS s1 x) s2)]
tryCompSSDef _ = []

tryInteractR :: Term -> [Term]
tryInteractR (TR (CompRR WkR (ConsR _ r))) = [TR r]
tryInteractR _ = []

tryInteractS :: Term -> [Term]
tryInteractS (TS (CompRS WkR (ConsS _ s))) = [TS s]
tryInteractS _ = []

tryEtaIdR :: Term -> [Term]
tryEtaIdR (TR (ConsR Z WkR)) = [TR IdR]
tryEtaIdR _ = []

tryEtaIdS :: Term -> [Term]
tryEtaIdS (TS (ConsS (VarE Z) (CompRS WkR IdS))) = [TS IdS]
tryEtaIdS _ = []

tryEtaLawR :: Term -> [Term]
tryEtaLawR (TR (ConsR (LookupR rho' Z) (CompRR WkR rho))) =  [TR rho | rho == rho']
tryEtaLawR _ = []

tryEtaLawS :: Term -> [Term]
tryEtaLawS (TS (ConsS (LookupS sigma' Z) (CompRS WkR sigma))) =  [TS sigma | sigma == sigma']
tryEtaLawS _ = []

tryDistRR :: Term -> [Term]
tryDistRR (TR (CompRR (ConsR x r1) r2)) = [TR (ConsR (LookupR r2 x) (CompRR r1 r2))]
tryDistRR _ = []

tryDistRS :: Term -> [Term]
tryDistRS (TS (CompRS (ConsR x r1) s2)) = [TS (ConsS (LookupS s2 x) (CompRS r1 s2))]
tryDistRS _ = []

tryDistSR :: Term -> [Term]
tryDistSR (TS (CompSR (ConsS t s1) r2)) = [TS (ConsS (RenE t r2) (CompSR s1 r2))]
tryDistSR _ = []

tryDistSS :: Term -> [Term]
tryDistSS (TS (CompSS (ConsS t s1) s2)) = [TS (ConsS (SubE t s2) (CompSS s1 s2))]
tryDistSS _ = []

tryRenId :: Term -> [Term]
tryRenId (TE (RenE e IdR)) = [TE e]
tryRenId _ = []

trySubId :: Term -> [Term]
trySubId (TE (SubE e IdS)) = [TE e]
trySubId _ = []

tryLeftIdRR :: Term -> [Term]
tryLeftIdRR (TR (CompRR IdR r)) = [TR r]
tryLeftIdRR _ = []

tryRightIdRR :: Term -> [Term]
tryRightIdRR (TR (CompRR r IdR)) = [TR r]
tryRightIdRR _ = []

tryLeftIdRS :: Term -> [Term]
tryLeftIdRS (TS (CompRS IdR s)) = [TS s]
tryLeftIdRS _ = []

tryLeftIdSR :: Term -> [Term]
tryLeftIdSR (TS (CompSR IdS r)) = [TS (CompRS r IdS)]
tryLeftIdSR _ = []

tryLeftIdSS :: Term -> [Term]
tryLeftIdSS (TS (CompSS IdS s)) = [TS s]
tryLeftIdSS _ = []

tryRightIdSR :: Term -> [Term]
tryRightIdSR (TS (CompSR s IdR)) = [TS s]
tryRightIdSR _ = []

tryRightIdSS :: Term -> [Term]
tryRightIdSS (TS (CompSS s IdS)) = [TS s]
tryRightIdSS _ = []

tryCompRR :: Term -> [Term]
tryCompRR (TE (RenE (RenE e r1) r2)) = [TE (RenE e (CompRR r1 r2))]
tryCompRR _ = []

tryCompRS :: Term -> [Term]
tryCompRS (TE (SubE (RenE e r1) s2)) = [TE (SubE e (CompRS r1 s2))]
tryCompRS _ = []

tryCompSR :: Term -> [Term]
tryCompSR (TE (RenE (SubE e s1) r2)) = [TE (SubE e (CompSR s1 r2))]
tryCompSR _ = []

tryCompSS :: Term -> [Term]
tryCompSS (TE (SubE (SubE e s1) s2)) = [TE (SubE e (CompSS s1 s2))]
tryCompSS _ = []

tryAssocRRR :: Term -> [Term]
tryAssocRRR (TR (CompRR (CompRR r1 r2) r3)) = [TR (CompRR r1 (CompRR r2 r3))]
tryAssocRRR _ = []

tryAssocRRS :: Term -> [Term]
tryAssocRRS (TS (CompRS (CompRR r1 r2) s3)) = [TS (CompRS r1 (CompRS r2 s3))]
tryAssocRRS _ = []

tryAssocRSR :: Term -> [Term]
tryAssocRSR (TS (CompSR (CompRS r1 s2) r3)) = [TS (CompRS r1 (CompSR s2 r3))]
tryAssocRSR _ = []

tryAssocRSS :: Term -> [Term]
tryAssocRSS (TS (CompSS (CompRS r1 s2) s3)) = [TS (CompRS r1 (CompSS s2 s3))]
tryAssocRSS _ = []

tryAssocSRR :: Term -> [Term]
tryAssocSRR (TS (CompSR (CompSR s1 r2) r3)) = [TS (CompSR s1 (CompRR r2 r3))]
tryAssocSRR _ = []

tryAssocSRS :: Term -> [Term]
tryAssocSRS (TS (CompSS (CompSR s1 r2) s3)) = [TS (CompSS s1 (CompRS r2 s3))]
tryAssocSRS _ = []

tryAssocSSR :: Term -> [Term]
tryAssocSSR (TS (CompSR (CompSS s1 s2) r3)) = [TS (CompSS s1 (CompSR s2 r3))]
tryAssocSSR _ = []

tryAssocSSS :: Term -> [Term]
tryAssocSSS (TS (CompSS (CompSS s1 s2) s3)) = [TS (CompSS s1 (CompSS s2 s3))]
tryAssocSSS _ = []

tryCoincidence :: Term -> [Term]
tryCoincidence (TE (SubE e (CompRS r IdS))) = [TE (RenE e r)]
tryCoincidence _ = []

-- | Compute rewrites in subterms (context closure)
stepContext :: Term -> [Term]
stepContext t = case t of
  -- Recursive cases for expressions
  TE (VarE Z) -> []
  TE (VarE (S v)) -> [TE (VarE (S v')) | v' <- stepVar v]
  TE (VarE (LookupR r x)) ->
    [TE (VarE (LookupR r' x)) | TR r' <- step (TR r)] ++
    [TE (VarE (LookupR r x')) | x' <- stepVar x]

  TE (Lam e) ->
    [TE (Lam e') | TE e' <- step (TE e)]

  TE (App e1 e2) ->
    [TE (App e1' e2) | TE e1' <- step (TE e1)] ++
    [TE (App e1 e2') | TE e2' <- step (TE e2)]

  TE (RenE e r) ->
    [TE (RenE e' r) | TE e' <- step (TE e)] ++
    [TE (RenE e r') | TR r' <- step (TR r)]

  TE (SubE e s) ->
    [TE (SubE e' s) | TE e' <- step (TE e)] ++
    [TE (SubE e s') | TS s' <- step (TS s)]

  TE (LookupS s x) ->
    [TE (LookupS s' x) | TS s' <- step (TS s)] ++
    [TE (LookupS s x') | x' <- stepVar x]

  -- Recursive cases for renamings
  TR IdR -> []
  TR WkR -> []

  TR (ConsR v r) ->
    [TR (ConsR v' r) | v' <- stepVar v] ++
    [TR (ConsR v r') | TR r' <- step (TR r)]

  TR (CompRR r1 r2) ->
    [TR (CompRR r1' r2) | TR r1' <- step (TR r1)] ++
    [TR (CompRR r1 r2') | TR r2' <- step (TR r2)]

  -- Recursive cases for substitutions
  TS IdS -> []

  TS (ConsS e s) ->
    [TS (ConsS e' s) | TE e' <- step (TE e)] ++
    [TS (ConsS e s') | TS s' <- step (TS s)]

  TS (CompRS r s) ->
    [TS (CompRS r' s) | TR r' <- step (TR r)] ++
    [TS (CompRS r s') | TS s' <- step (TS s)]

  TS (CompSR s r) ->
    [TS (CompSR s' r) | TS s' <- step (TS s)] ++
    [TS (CompSR s r') | TR r' <- step (TR r)]

  TS (CompSS s1 s2) ->
    [TS (CompSS s1' s2) | TS s1' <- step (TS s1)] ++
    [TS (CompSS s1 s2') | TS s2' <- step (TS s2)]

-- Helper function for context closure in variables
stepVar :: Var -> [Var]
stepVar v = case v of
  Z -> []
  S v' -> [S v'' | v'' <- stepVar v']
  LookupR r x ->
    [LookupR r' x | TR r' <- step (TR r)] ++
    [LookupR r x' | x' <- stepVar x]

-- Lifting for renamings and substitutions (↑ᵣ and ↑ₛ)
liftRen :: Ren -> Ren
liftRen r = ConsR Z (CompRR r WkR)

liftSub :: Sub -> Sub
liftSub s = ConsS (VarE Z) (CompSR s WkR)


-- | Debug function to trace reductions
--debugStep :: Term -> IO ()
--debugStep t = do
--  putStrLn $ "Analyzing term: " ++ show t
--  let topResults = stepTop t
--  let contextResults = stepContext t
--
--  putStrLn $ "Top-level reductions (" ++ show (length topResults) ++ "):"
--  mapM_ (\r -> putStrLn $ "  " ++ show r) topResults
--
--  putStrLn $ "Contextual reductions (" ++ show (length contextResults) ++ "):"
--  mapM_ (\r -> putStrLn $ "  " ++ show r) contextResults
--
--  let allResults = nub $ topResults ++ contextResults
--  putStrLn $ "All reductions (" ++ show (length allResults) ++ "):"
--  mapM_ (\r -> putStrLn $ "  " ++ show r) allResults
--
---- | Example that demonstrates multiple reductions in one step
--exampleTerm :: Term
--exampleTerm = TE (App
--                   (RenE (Lam (VarE Z)) IdR)           -- This can reduce via ⋯idᵣ
--                   (SubE (App (VarE Z) (VarE (S Z)))   -- This has multiple possible reductions:
--                          IdS))                        -- - The SubE with IdS can reduce via ⋯idₛ
--                                                       -- - The App inside can have its arguments transformed
--
---- | Enhanced example breakdown
--enhancedExample :: IO ()
--enhancedExample = do
--  putStrLn "Example term:"
--  putStrLn $ show exampleTerm
--
--  -- Break down the example and check each component
--  let (TE (App e1 e2)) = exampleTerm
--
--  putStrLn "\nExamining left component of application:"
--  debugStep (TE e1)
--
--  putStrLn "\nExamining right component of application:"
--  debugStep (TE e2)
--
--  putStrLn "\nChecking top-level application pattern match:"
--  -- Check if RenE matches a pattern in stepTop
--  let matchesRenELam = case e1 of
--        RenE (Lam _) IdR -> True
--        _ -> False
--  putStrLn $ "Left component is RenE (Lam _) IdR: " ++ show matchesRenELam
--
--  -- Check if SubE matches a pattern in stepTop
--  let matchesSubEApp = case e2 of
--        SubE (App _ _) IdS -> True
--        _ -> False
--  putStrLn $ "Right component is SubE (App _ _) IdS: " ++ show matchesSubEApp
--
--  putStrLn "\nFull reduction analysis:"
--  debugStep exampleTerm
--
---- | Modified runExample to include debugging
--enhancedExampleDebug :: IO ()
--enhancedExampleDebug = do
--  enhancedExample
--  putStrLn "\n-------------------\n"
--
--  putStrLn "Testing specific patterns:"
--  -- Test specific patterns that should match
--  let testLam = TE (RenE (Lam (VarE Z)) IdR)
--  let testApp = TE (SubE (App (VarE Z) (VarE (S Z))) IdS)
--
--  putStrLn "Lam with RenE and IdR:"
--  debugStep testLam
--
--  putStrLn "\nApp with SubE and IdS:"
--  debugStep testApp
--
--  putStrLn "\nOriginal results summary:"
--  let reductions = step exampleTerm
--  putStrLn $ "Total reductions: " ++ show (length reductions)
--  mapM_ (\(i, t) -> putStrLn $ show i ++ ". " ++ show t) (zip [1..] reductions)
--
---- | Extended examples for interesting reductions
--extendedExamples :: IO ()
--extendedExamples = do
--  -- Example 1: Nested compositions
--  let nested = TS (CompSS (CompSS IdS (CompSR IdS IdR)) (CompRS IdR IdS))
--  putStrLn "Example 1: Nested compositions of substitutions and renamings"
--  putStrLn $ "Term: " ++ show nested
--  let reductions = step nested
--  putStrLn $ "Number of reductions: " ++ show (length reductions)
--  mapM_ (\(i, r) -> putStrLn $ show i ++ ". " ++ show r) (zip [1..] reductions)
--
--  -- Example 2: EtaLaw example - this tries to match the η-law pattern
--  let etaExample = TR (ConsR (LookupR specialRho Z) (CompRR WkR specialRho))
--      specialRho = ConsR (S Z) (CompRR IdR WkR)
--  putStrLn "\nExample 2: EtaLaw with explicit rho"
--  putStrLn $ "Term: " ++ show etaExample
--  let etaReductions = step etaExample
--  putStrLn $ "Number of reductions: " ++ show (length etaReductions)
--  mapM_ (\(i, r) -> putStrLn $ show i ++ ". " ++ show r) (zip [1..] etaReductions)
--
--  -- Example 3: A term with both top-level and contextual reductions
--  let mixedTerm = TE (App
--                     (SubE (RenE (Lam (VarE Z)) IdR) IdS)
--                     (RenE (SubE (VarE Z) IdS) IdR))
--  putStrLn "\nExample 3: Mixed reductions (top-level and contextual)"
--  putStrLn $ "Term: " ++ show mixedTerm
--  let mixedReductions = step mixedTerm
--  putStrLn $ "Number of reductions: " ++ show (length mixedReductions)
--  putStrLn "Top-level:"
--  let topResults = stepTop mixedTerm
--  mapM_ (\(i, r) -> putStrLn $ show i ++ ". " ++ show r) (zip [1..] topResults)
--  putStrLn "Contextual:"
--  let contextResults = stepContext mixedTerm
--  mapM_ (\(i, r) -> putStrLn $ show i ++ ". " ++ show r) (zip [1..] contextResults)

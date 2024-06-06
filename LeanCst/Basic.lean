import Init.Prelude
import Mathlib.Tactic.DefEqTransformations

---- Auxiliary definitions ----
def η [Monad m] {A : Type} (a : A) : m A := pure a
def μ [Monad m] {A : Type} (a : m (m A)) : m A := a >>= id
notation "⟨" f:80 "×" g:80 "⟩" => Prod.map f g

def myswap : a × b × c → (a × b) × c := λ ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩
def myunswap : (a × b) × c → a × b × c := λ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
def swap : a × b → b × a := λ (a,b) ↦ (b,a)
-------------------------------

class CommutativeMonad (m : Type → Type) extends Monad m, LawfulMonad m where
  -- A morphism from a pair of "monadic values" into a monadic pair of values
  σ : m a × m b → m (a × b)
  -- Such that performing it on a `pure`'d Unit on the right and then taking the
  -- projection is the same as just performing the action on the left
  comm_l : let arr : m a × Unit → m a := Functor.map Prod.fst ∘ σ ∘ ⟨id × η⟩
           arr = Prod.fst
  -- The same for the left
  comm_r : let arr : Unit × m a → m a := Functor.map (f := m) Prod.snd ∘ σ ∘ ⟨η (m := m) × id⟩
           arr = Prod.snd
  -- And rearranging two of three paired monadic arguments does not affect
  -- the result
  assoc : let arrleft : m a × m b × m c → m (a × b × c) := σ ∘ ⟨id × σ⟩
          let arrright : m a × m b × m c → m (a × b × c) := Functor.map myunswap ∘ σ ∘ ⟨σ × id⟩ ∘ myswap
          arrleft = arrright
  -- and `pure`-ing a pair is the same as `pure`-ing each element then performing it
  relift : let arr : a × b → m (a × b) := σ ∘ ⟨η × η⟩
          arr = η
  -- and finally that performing it twice on a pair of nested monadic values
  -- then `join`-ing is the same as `join`-ing such a pair and then performing it
  rejoin : let arrleft : m (m a) × m (m b) → m (a × b) := μ ∘ Functor.map σ ∘ σ
           let arrright : m (m a) × m (m b) → m (a × b) := σ ∘ ⟨μ × μ⟩
           arrleft = arrright

def uncurry (f : A → B → C) : A × B → C := λ (a, b) ↦ f a b

lemma σ_swap [CommutativeMonad m] (ma : m A) (mb : m B) :
  σ = Functor.map (f := m) swap ∘ σ ∘ swap := sorry

def f' [CommutativeMonad m] (ma : m A) (mb : m B) : m (A × B) := do
  let a ← ma
  let b ← mb
  return (a, b)

def g' [CommutativeMonad m] (ma : m A) (mb : m B) : m (A × B) := do
  let b ← mb
  let a ← ma
  return (a, b)

theorem do_notation_equal' [CommutativeMonad m] {ma : m A} {mb : m B} : f' ma mb = g' ma mb := by
  unfold f'
  unfold g'
  rename_i inst
  change -- this line is redundunt but explains exactly what the `do` notation is doing
    (bind ma fun a => bind mb fun b => pure (a, b))
      =
    (bind mb fun b => bind ma fun a => pure (a, b))
  change (ma >>= λa ↦ mb >>= λ b ↦ pure (a, b)) = (mb >>= λb ↦ ma >>= λ a ↦ pure (a, b))
  reduce
  have a := @Bind.bind m inst.1.2


  sorry

-- instance : CommutativeMonad powerset where
--   pure a := {a}
  -- bind s f := ⋃ (x ∈ s) => f x

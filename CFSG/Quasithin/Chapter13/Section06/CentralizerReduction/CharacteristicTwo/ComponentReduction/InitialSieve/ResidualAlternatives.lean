module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface
public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# The residual alternatives in the first component sieve

This file records the exact source interface used at the last step of the
initial sieve (13.6.6, printed pp.926--927).  The statement of A.3.18 is kept
as a universal hypothesis: its three alternatives, the lower two-core quotient,
and the quotient `H/O_{p'}(H)` are all visible in `A318Case`.  The local theorem
then performs the rank split, transports the residual and projective cases to
the literal normalizer quotient, and rejects both cover subcases through the
centerless-image premise supplied by the caller.

The transport fields are deliberately hypotheses.  They are the mathematical
places where the preceding component/action proof supplies the actual maps;
they do not encode the desired disjunction in the A.3.18 contract.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Notation A.3.16
and Lemma A.3.18, printed pp.51--52; proof of 13.6.6, printed pp.926--927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve

open Subgroup Theory.GroupTheory A5Module
open Chapter1.Section02.LocalModels ClassificationModels
open CFSG.Quasithin

universe u

variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}

/-- The sign convention used in A.3.16 and A.3.18: `minus` is the unitary
sign.  The congruence is therefore `q ≡ 1` for `plus` and `q ≡ 2` for
`minus`. -/
inductive Sign
  | plus
  | minus
deriving DecidableEq

def Sign.unitary : Sign → Bool
  | .plus => false
  | .minus => true

def Sign.congruence (ε : Sign) (q : ℕ) : Prop :=
  q % 3 = if ε.unitary then 2 else 1

def Sign.torusOrder (ε : Sign) (q : ℕ) : ℕ :=
  match ε with
  | .plus => q ^ 2 + q + 1
  | .minus => q ^ 2 - q + 1

/-- The simple component model occurring in A.3.18(2), with the actual
projective linear/unitary carriers and the source field parameter retained. -/
def SignedComponentModel (Q : Type u) [Group Q] (ε : Sign) (q : ℕ) : Prop :=
  IsPSLSign Q ε.unitary 3 q

/-- The actual PGL/PGU carriers used for the ambient group in A.3.18(2). -/
def ActualProjectiveThree (Q : Type u) [Group Q] (ε : Sign) (q : ℕ) : Prop :=
  match ε with
  | .plus =>
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
        Nonempty (Q ≃* Matrix.ProjGenLinGroup (Fin 3) F)
  | .minus =>
      ∃ (F : Type) (_ : Field F) (_ : Finite F)
          (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F),
        Nat.card F = q ^ 2 ∧ (∀ x, J.conj x = x ^ q) ∧
          Nonempty (Q ≃* J.unitarySubgroup.map Matrix.ProjGenLinGroup.mk)

/-- The fixed-point subgroup of an automorphism.  This is the literal
centralizer of the order-three actor on the component quotient. -/
def actorFixedSubgroup (Q : Type u) [Group Q] (α : MulAut Q) : Subgroup Q where
  carrier := {x | α x = x}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change α (x * y) = x * y
    rw [map_mul]
    change α x = x at hx
    change α y = y at hy
    rw [hx, hy]
  inv_mem' := by
    intro x hx
    change α x⁻¹ = x⁻¹
    rw [map_inv]
    change α x = x at hx
    rw [hx]


/-- A concrete witness for the nonsplit extension in Notation A.3.16.

The carrier is a subgroup of `Aut(L)`, contains the inner automorphisms with
index three, and is identified with the group under consideration.  The
actor, centralizer, and conjugacy fields are the three outer-action clauses in
A.3.16/A.3.18; keeping them explicit prevents the extension from degenerating
to an unconnected family tag.
-/
structure A316Nonsplit (Q : Type u) [Group Q] (ε : Sign) (q : ℕ) : Type (u + 1) where
  base : Type u
  [base_group : Group base]
  model : SignedComponentModel base ε q
  carrier : Subgroup (MulAut base)
  inner_le : MulAut.innerSubgroup base ≤ carrier
  inner_index : ((MulAut.innerSubgroup base).subgroupOf carrier).index = 3
  iso : Nonempty (Q ≃* carrier)
  nonsplit : ¬ ∃ D : Subgroup carrier,
    Subgroup.IsComplement (D : Set carrier)
      ((MulAut.innerSubgroup base).subgroupOf carrier : Set carrier)
  actor : carrier
  actor_order : orderOf actor = 3
  actor_outer : (actor : MulAut base) ∉ MulAut.innerSubgroup base
  actor_parameter : q % 3 = (if ε.unitary then 2 else 1)
  notation_parameter :
    (∃ n : ℕ, ε = .plus ∧ q = 2 ^ (6 * n)) ∨
      (∃ n : ℕ, ε = .minus ∧ q = 2 ^ (3 * n))
  fixed_cyclic : IsCyclic (actorFixedSubgroup base (actor : MulAut base))
  fixed_order : Nat.card (actorFixedSubgroup base (actor : MulAut base)) =
    ε.torusOrder q
  conjugacy_of_outer_three : ∀ β : MulAut base, orderOf β = 3 →
    β ∉ MulAut.innerSubgroup base →
      ∃ y : base, β = MulAut.conj y * (actor : MulAut base) * (MulAut.conj y)⁻¹

/-- The two possibilities in the projective branch of A.3.18(2). -/
inductive ProjectiveThreeExtension (Q : Type u) [Group Q] (ε : Sign) (q : ℕ) : Prop
  | split (model : ActualProjectiveThree Q ε q)
  | nonsplit (model : A316Nonsplit Q ε q)

/-- The image of a component in `H* = H/O_{3'}(H)` used by the cover clause.
The source model list is the complete list `SL₃^ε(q), Â₆, Â₇, M̂₂₂`. -/
def A318CoverImage (H : Type u) [Group H] [Finite H]
    (K : Subgroup H) : Subgroup (H ⧸ pPrimeCore 3 H) :=
  K.map (QuotientGroup.mk' (pPrimeCore 3 H))

def A318CoverImageAlternative (H : Type u) [Group H] [Finite H]
    (K : Subgroup H) : Prop :=
  (∃ (ε : Bool) (q : ℕ), q % 3 = (if ε then 2 else 1) ∧
    IsSLSign (A318CoverImage H K) ε 3 q) ∨
  IsAlternatingCover (A318CoverImage H K) 6 ∨
  IsAlternatingCover (A318CoverImage H K) 7 ∨
  IsM22Cover (A318CoverImage H K)

/-- The diagonal order-three subcase in A.3.18(3b).  The fixed subgroup is
kept as an actual subgroup of the component quotient, with its cyclic order,
while the last field is the source conjugacy assertion for every outer
order-three actor. -/
structure A318DiagonalData (Q : Type u) [Group Q] (ε : Sign) (q : ℕ) : Type (u + 1) where
  model : IsPSLSign Q ε.unitary 3 q
  actor : MulAut Q
  actor_order : orderOf actor = 3
  diagonal_outer : actor ∉ MulAut.innerSubgroup Q
  fixed_cyclic : IsCyclic (actorFixedSubgroup Q actor)
  fixed_order : Nat.card (actorFixedSubgroup Q actor) =
    ε.torusOrder q
  conjugacy_assertion : ∀ β : MulAut Q, orderOf β = 3 →
    β ∉ MulAut.innerSubgroup Q →
      ∃ y : Q, β = MulAut.conj y * actor * (MulAut.conj y)⁻¹

/-- The two source subcases attached to the cover model in A.3.18(3).  The
first is `L = θ(H)`.  The second keeps the actual order-three diagonal actor,
its cyclic centralizer order, and the conjugacy assertion. -/
structure A318CoverData (H : Type u) [Group H] [Finite H]
    (K : Subgroup H) : Type (u + 1) where
  model : A318CoverImageAlternative H K
  theta_case : K = Chapter15.Section03.theta (⊤ : Subgroup H) ∨
    ∃ (ε : Sign) (q : ℕ) (x : H ⧸ pPrimeCore 3 H),
      Sign.congruence ε q ∧ orderOf x = 3 ∧
      x ∉ A318CoverImage H K ∧
      Nonempty (A318DiagonalData (A318CoverImage H K) ε q)
/-- The complete three-way source conclusion of A.3.18.  In the projective
branch `component_model` is the lower two-core quotient `L/O₂(L)` and
`ambient` is a subgroup of the literal `H* = H/O_{p'}(H)`. -/
inductive A318Case (H : Type u) [Group H] [Finite H]
    (K : Subgroup H) (p : ℕ) : Prop
  | residual (h : K = primeToResidual p H) : A318Case H K p
  | projective (hp : p = 3) (ε : Sign) (q : ℕ)
      (hq : Sign.congruence ε q)
      (component_model : SignedComponentModel (K ⧸ pCore 2 K) ε q)
      (ambient : Subgroup (H ⧸ pPrimeCore p H))
      (ambient_eq : ambient = primeToResidual 3 (H ⧸ pPrimeCore p H))
      (ambient_model : ProjectiveThreeExtension ambient ε q) :
      A318Case H K p
  | cover (hp : p = 3) (data : A318CoverData H K) : A318Case H K p

/-- Universal A.3.18, with every source hypothesis explicit. -/
def EarlierA318 (κ : GroupClass.{u}) : Prop :=
  ∀ (H : Type u) (_ : Group H) (_ : Finite H), IsSQTK κ H →
    ∀ (K : Subgroup H), IsComponent H K →
      IsQuasisimple (K ⧸ pCore 2 K) →
      ∀ (p : ℕ), p.Prime → Odd p → 1 < primeRank p K →
        A318Case H K p

/-- The literal subgroup `K*Lᵥ*` in `X* = N(K)/C(K)`. -/
def starResidual (s : Marking L V) (K : Subgroup (Gv (markedV s)))
    (_hN : ComponentReduction.residual s ≤ ComponentReduction.X K) :
    Subgroup (NormalizerAction.Star K) :=
  (ComponentReduction.residual s).subgroupOf (ComponentReduction.X K) |>.map
    (NormalizerAction.quotient K)

def starComponentResidual (s : Marking L V) (K : Subgroup (Gv (markedV s)))
    (hN : ComponentReduction.residual s ≤ ComponentReduction.X K) :
    Subgroup (NormalizerAction.Star K) :=
  NormalizerAction.componentImage K ⊔ starResidual s K hN

/-- The ambient image of `O^{3'}(E(Gᵥ))`, with the component layer embedded in
`Gᵥ`.  This is the source `O^{3'}` convention, rather than an `O_{3'}` core. -/
def ambientComponentResidual (s : Marking L V) : Subgroup (Gv (markedV s)) :=
  (primeToResidual 3 (componentLayer (Gv (markedV s)))).map
    (componentLayer (Gv (markedV s))).subtype

/-- The exact output alternatives after the field-indexed model sieve. -/
inductive ResidualAlternatives (s : Marking L V)
    (K : Subgroup (Gv (markedV s)))
    (a : ActionData s (T : Subgroup G) K) (m : ℕ) : Prop
  | residual (hres : ComponentReduction.residual s ≤ primeToResidual 3 (Gv (markedV s)))
      (hK : K = primeToResidual 3 (Gv (markedV s))) :
      ResidualAlternatives s K a m
  | rank_one (h : primeRank 3 K ≤ 1) : ResidualAlternatives s K a m
  | extension (ε : Sign)
      (hmodel : ProjectiveThreeExtension (starComponentResidual s K a.residual_normalizes)
        ε (2 ^ m))
      (hK : K = ambientComponentResidual s) : ResidualAlternatives s K a m

/-- The source-to-target transport supplied by the preceding component/action
branch.  It keeps the field parameter and all literal quotient maps visible. -/
structure A318Transport (s : Marking L V) (K : Subgroup (Gv (markedV s)))
    (a : ActionData s (T : Subgroup G) K) (m : ℕ) : Prop where
  hN : ComponentReduction.residual s ≤ ComponentReduction.X K
  residual : K = primeToResidual 3 (Gv (markedV s)) →
    ComponentReduction.residual s ≤ primeToResidual 3 (Gv (markedV s))
  projective_parameter : ∀ (ε : Sign) (q : ℕ),
    Sign.congruence ε q → SignedComponentModel (K ⧸ pCore 2 K) ε q → q = 2 ^ m
  projective : ∀ (ε : Sign) (q : ℕ), q = 2 ^ m →
    ∀ (A : Subgroup (Gv (markedV s) ⧸ pPrimeCore 3 (Gv (markedV s)))),
      A = primeToResidual 3 (Gv (markedV s) ⧸ pPrimeCore 3 (Gv (markedV s))) →
      ProjectiveThreeExtension A ε q →
      ∃ e : starComponentResidual s K hN ≃* A,
        Function.Injective e ∧
        ProjectiveThreeExtension (starComponentResidual s K hN) ε q
  ambient_eq : K = ambientComponentResidual s
  cover_centerless : IsSimpleGroup (K ⧸ center K)
  cover_image_equiv : Nonempty ((K ⧸ center K) ≃*
    A318CoverImage (Gv (markedV s)) K)
  cover_model_excluded : ∀ (hc : IsSimpleGroup (K ⧸ center K)),
    hc = cover_centerless →
    ∀ (e : (K ⧸ center K) ≃*
    A318CoverImage (Gv (markedV s)) K),
    Function.Injective e →
    A318CoverImageAlternative (Gv (markedV s)) K → False

/-- Specialization of the complete source lemma to the three alternatives of
13.6.6.  The cover branch is discharged by the centerless-image exclusion in
`A318Transport.cover_model_excluded`; both theta and diagonal subcases therefore
cannot survive. -/
theorem residual_alternatives_of_a318
    (_d : Setup κ T s) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K)
    (m : ℕ) (_hm : 1 < m)
    (_hmodel : BinaryModelAt (NormalizerAction.componentImage K) m)
    (_hE : EStar s K a.a_normalizes a.z_normalizes ≤
      NormalizerAction.componentImage K)
    (hsqtk : IsSQTK κ (Gv (markedV s)))
    (_hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (hQ : IsQuasisimple (K ⧸ pCore 2 K))
    (earlier : EarlierA318 κ)
    (tr : A318Transport s K a m) :
    ResidualAlternatives s K a m := by
  by_cases hrank : 2 ≤ primeRank 3 K
  · have hc := earlier (Gv (markedV s)) inferInstance inferInstance hsqtk K hK hQ
      3 Nat.prime_three (by decide) hrank
    cases hc with
    | residual h =>
        exact .residual (tr.residual h) h
    | projective hp ε q hq hmK A hAeq hA =>
        have hq' : q = 2 ^ m := tr.projective_parameter ε q hq hmK
        have ht := tr.projective ε q hq' A hAeq hA
        rcases ht with ⟨hcompat, htarget⟩
        exact .extension ε (by simpa [hq'] using htarget.2) tr.ambient_eq
    | cover hp data =>
        rcases tr.cover_image_equiv with ⟨e⟩
        exact (tr.cover_model_excluded tr.cover_centerless rfl e e.injective data.model).elim
  · exact .rank_one (by omega)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve

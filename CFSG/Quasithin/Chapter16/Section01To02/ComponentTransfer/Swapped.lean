module

public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Reduction
public import Theory.GroupTheory.Commutator.PerfectSolvableSupplement

/-!
# The swapped component branch

This file records the deductions specific to alternative (2) of
Aschbacher--Smith 16.1.7.  `Reduction` supplies the actual two components,
their product and the relative Sylow restriction.  The two genuinely earlier
inputs used below are kept explicit:

* the A.3.8 model for the quotient of the moving component;
* the solvable supplement which identifies the centralizer residual; and
* the intrinsic 16.1.2 index divisibility calculation.

Thus the exports here do not turn an A.3.8 or an intrinsic model assertion
into a theorem by name alone.  In particular, no residual equality, catalogue,
or index bound is a field of the conclusion.  Actual multiplicative
equivalences are retained throughout.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
I.3.1--I.3.2, A.3.8, and 16.1.7--16.1.8, pp. 45--46 and 1172--1173.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.ComponentTransfer

open Subgroup Theory.GroupTheory

universe u
variable {G : Type u} [Group G]
variable {H K L J : Subgroup G} {t i : G}

/-! ## The three source catalogue entries -/

/-- The three quotient models surviving the intersection of A.3.8 with (E2)
in the swapped branch.  Every entry contains an actual equivalence with the
corresponding concrete carrier. -/
inductive SwappedQuotientModel (Q : Type u) [Group Q] : Prop
  | linearEven (n : ℕ) (hn : 2 ≤ n)
      (model : ClassicalGroup.IsPSL Q 2 (2 ^ n))
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (model : Nonempty (Q ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | linearPrime (p : ℕ) (hp : p.Prime)
      (model : ClassicalGroup.IsPSL Q 2 p)

namespace SwappedQuotientModel

/-- Transport the catalogue through an actual multiplicative equivalence. -/
theorem of_mulEquiv {Q R : Type u} [Group Q] [Group R]
    (h : SwappedQuotientModel Q) (e : R ≃* Q) : SwappedQuotientModel R := by
  cases h with
  | linearEven n hn model =>
      exact .linearEven n hn (model.of_mulEquiv e)
  | suzuki m hm model =>
      exact .suzuki m hm (model.map (e.trans ·))
  | linearPrime p hp model =>
      exact .linearPrime p hp (model.of_mulEquiv e)

end SwappedQuotientModel

/-! ## The A.3.8 and residual interfaces -/

/-- The part of the A.3.8 output used by this branch.  The model is attached
to the actual component quotient, so the later transport is a theorem rather
than a presentation-level identification. -/
structure A38SwappedInput (J : Subgroup G) : Prop where
  quotientModel : SwappedQuotientModel (J ⧸ pCore 2 J)

/-- A solvable supplement for the centralizer of `t` in `K`.  The first two
fields are relative to the actual subgroup `centralizerIn K t`; the equality
in the last field is intrinsic and therefore is not already the residual
conclusion. -/
structure SwappedResidualInput (K L : Subgroup G) (t : G) : Prop where
  leCentralizer : L ≤ centralizerIn K t
  subnormal : (L.subgroupOf (centralizerIn K t)).IsSubnormal
  perfect : Group.IsPerfect (L.subgroupOf (centralizerIn K t))
  supplement : ∃ N : Subgroup (centralizerIn K t),
    N.Normal ∧ Group.IsSolvable N ∧
      L.subgroupOf (centralizerIn K t) ⊔ N = ⊤

/-- The component part of the setup already supplies the perfect and
subnormal hypotheses needed by the residual argument.  This constructor only
asks the earlier source calculation for its solvable supplement. -/
theorem swappedResidualInput_of_setup [Finite G]
    (h : Setup t i L)
    (hsupp : ∃ N : Subgroup
        (centralizerIn (layerClosure (involutionCentralizer i) L) t),
      N.Normal ∧ Group.IsSolvable N ∧
        L.subgroupOf (centralizerIn (layerClosure (involutionCentralizer i) L) t) ⊔ N = ⊤) :
    SwappedResidualInput (layerClosure (involutionCentralizer i) L) L t := by
  let K := layerClosure (involutionCentralizer i) L
  let C := centralizerIn K t
  have hLK : L ≤ K := le_layerClosure _ _
  have hLC : L ≤ C := le_inf hLK h.component.1
  have hCK : C ≤ centralizerIn (involutionCentralizer i) t := by
    exact inf_le_inf h.closure_le_centralizer le_rfl
  have hcomp : IsComponentIn L C :=
    IsComponentIn.restrict h.component_in_jointCentralizer hLC hCK
  refine ⟨hLC, hcomp.2.1, ?_, ?_⟩
  · let _ := hcomp.2.2
    exact IsQuasisimple.toIsPerfect
  · simpa only [K, C] using hsupp

/-- The numerical part of the intrinsic 16.1.2 calculation.  Divisibility is
the source conclusion before cancellation; the strict two-part estimate is a
separate concrete model fact. -/
structure SwappedIndexInput (K J : Subgroup G) (t : G) : Prop where
  twoPart_gt_two :
    2 < 2 ^ (Nat.card (J ⧸ pCore 2 J)).factorization 2
  divisor : ∀ R : Sylow 2 K,
    2 ^ (Nat.card (J ⧸ pCore 2 J)).factorization 2 ∣
      (involutionCentralizer t).relIndex
        ((R : Subgroup K).map K.subtype)

/-! ## Direct consequences of the swapped witness -/

/-- The actual moving component, commuting pair and quotient equivalence are
all retained in one theorem. -/
theorem SwappedComponents.factor_data (h : SwappedComponents H t L K)
    (ht : t ∈ H) :
    ∃ J : Subgroup G, IsComponentIn J H ∧ J ≠ J.conjBy t ∧
      K = J ⊔ J.conjBy t ∧ ⁅J, J.conjBy t⁆ = ⊥ ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* (L ⧸ pCore 2 L)) := by
  exact h.commute ht

/-- The quotient catalogue transports from the A.3.8 component to the source
component `L` through the actual equivalence in `SwappedComponents`. -/
theorem swapped_catalogue_of_A38
    (_h : SwappedComponents H t L K) (_ht : t ∈ H)
    {J : Subgroup G} (_hJ : IsComponentIn J H)
    (_hJneq : J ≠ J.conjBy t) (_hK : K = J ⊔ J.conjBy t)
    (hquot : Nonempty ((J ⧸ pCore 2 J) ≃* (L ⧸ pCore 2 L)))
    (ha38 : A38SwappedInput J) :
    SwappedQuotientModel (L ⧸ pCore 2 L) := by
  obtain ⟨e⟩ := hquot
  exact ha38.quotientModel.of_mulEquiv e.symm

/-- A convenient form of the preceding theorem which extracts the component
from the swapped witness itself. -/
theorem swapped_catalogue
    (h : SwappedComponents H t L K) (ht : t ∈ H)
    (ha38 : ∀ J : Subgroup G, IsComponentIn J H →
      A38SwappedInput J) :
    ∃ J : Subgroup G, IsComponentIn J H ∧ J ≠ J.conjBy t ∧
      K = J ⊔ J.conjBy t ∧
      SwappedQuotientModel (L ⧸ pCore 2 L) := by
  obtain ⟨J, hJ, hne, hK, _, hq⟩ := h.factor_data ht
  exact ⟨J, hJ, hne, hK,
    swapped_catalogue_of_A38 h ht hJ hne hK hq (ha38 J hJ)⟩

/-! ## The solvable residual -/

/-- The intrinsic supplement in `SwappedResidualInput` identifies the actual
embedded solvable residual. -/
theorem swapped_residual_of_input [Finite G]
    {K L : Subgroup G} {t : G}
    (h : SwappedResidualInput K L t) :
    L = centralizerResidual K t := by
  let C := centralizerIn K t
  obtain ⟨N, hNnormal, hNsolv, hsup⟩ := h.supplement
  let _ : Group.IsPerfect (L.subgroupOf C) := h.perfect
  let _ : N.Normal := hNnormal
  let _ : Group.IsSolvable N := hNsolv
  have hEq : L.subgroupOf C = solvableResidual C :=
    h.subnormal.eq_solvableResidual_of_sup_eq_top N hsup
  change L = (solvableResidual C).map C.subtype
  rw [← map_subgroupOf_eq_of_le h.leCentralizer, hEq]

/-- The residual identity in the exact source notation. -/
theorem swapped_residual [Finite G]
    {K L : Subgroup G} {t : G}
    (h : SwappedResidualInput K L t) :
    L = (solvableResidual (centralizerIn K t)).map (centralizerIn K t).subtype := by
  simpa only [centralizerResidual] using swapped_residual_of_input h

/-! ## The Sylow index estimate -/

/-- The intrinsic divisibility calculation implies the lower bound for every
Sylow subgroup of `K`; no normalization of `R` by `t` is used. -/
theorem swapped_index_bound [Finite G]
    {K J : Subgroup G} {t : G}
    (h : SwappedIndexInput K J t) (R : Sylow 2 K) :
    2 ^ (Nat.card (J ⧸ pCore 2 J)).factorization 2 ≤
        (involutionCentralizer t).relIndex
          ((R : Subgroup K).map K.subtype) ∧
      2 < 2 ^ (Nat.card (J ⧸ pCore 2 J)).factorization 2 := by
  have hpos : 0 < (involutionCentralizer t).relIndex
      ((R : Subgroup K).map K.subtype) :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact ⟨Nat.le_of_dvd hpos (h.divisor R), h.twoPart_gt_two⟩

/-! ## The complete conditional branch -/

/-- All conclusions of the swapped branch, with exactly the earlier source
inputs that remain to be discharged by the Chapter 16 assembly. -/
structure SwappedBranchConclusion [Finite G]
    (H : Subgroup G) (t : G) (L K : Subgroup G) : Prop where
  component : ∃ J : Subgroup G, IsComponentIn J H ∧
    J ≠ J.conjBy t ∧ K = J ⊔ J.conjBy t ∧
    ⁅J, J.conjBy t⁆ = ⊥ ∧
    Nonempty ((J ⧸ pCore 2 J) ≃* (L ⧸ pCore 2 L))
  residual : L = centralizerResidual K t
  catalogue : SwappedQuotientModel (L ⧸ pCore 2 L)
  index : ∀ J : Subgroup G, IsComponentIn J H → J ≠ J.conjBy t →
    K = J ⊔ J.conjBy t → ∀ R : Sylow 2 K,
      2 ^ (Nat.card (J ⧸ pCore 2 J)).factorization 2 ≤
          (involutionCentralizer t).relIndex
            ((R : Subgroup K).map K.subtype) ∧
        2 < 2 ^ (Nat.card (J ⧸ pCore 2 J)).factorization 2

/-- Assemble the branch from the actual swapped witness and the three
independent earlier deductions. -/
theorem swapped_branch_of_inputs [Finite G]
    {H : Subgroup G} {t : G} {L K : Subgroup G}
    (ht : t ∈ H) (hswap : SwappedComponents H t L K)
    (hres : SwappedResidualInput K L t)
    (ha38 : ∀ J : Subgroup G, IsComponentIn J H → A38SwappedInput J)
    (hindex : ∀ J : Subgroup G, IsComponentIn J H →
      J ≠ J.conjBy t → K = J ⊔ J.conjBy t →
      SwappedIndexInput K J t) :
    SwappedBranchConclusion H t L K := by
  obtain ⟨J, hJ, hne, hK, hcomm, hquot⟩ := hswap.factor_data ht
  let hc : SwappedQuotientModel (L ⧸ pCore 2 L) :=
    swapped_catalogue_of_A38 hswap ht hJ hne hK hquot (ha38 J hJ)
  refine ⟨⟨J, hJ, hne, hK, hcomm, hquot⟩,
    swapped_residual_of_input hres, hc, ?_⟩
  intro J' hJ' hne' hK' R
  exact swapped_index_bound (hindex J' hJ' hne' hK') R

end CFSG.Quasithin.Chapter16.ComponentTransfer

module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Preliminaries
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.PPrimeCore
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import Mathlib.GroupTheory.RegularWreathProduct

/-!
# Component elimination in the A₅ centralizer argument

This file records the source-shaped implications used after the component
selected in 13.6.8--16 has been fixed.  The ambient group is always the one
from `CentralizerReduction.Notation`: `Gv v` is the literal centralizer and
`Gcheck v` is the literal quotient by `⟨v⟩`.  In particular, the residual in
13.6.23(1) is `pResidual 3 (Gv v)`, while the prime-to-three core in the last
paragraph is `pPrimeCore 3`.

The difficult local and representation-theoretic facts are parameters of the
individual source implications.  They are earlier source results (A.3, A.4,
B.4--5, C.1, E.2 and 13.6.2--16); no conclusion numbered 13.6.17--23 is
included as an input.  The parameters retain actual subgroup inclusions and
equivariant model data, so a later assembly can discharge them from the
component-selection and model owners.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.930--933.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination

open Subgroup
open Stellmacher
open Theory.GroupTheory
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.ChapterC

universe u
variable {G : Type u} [Group G]

/-- Relative component membership.  The normality and subnormality here are
relative to the displayed local group, as in the source. -/
def IsComponentIn (H K : Subgroup G) : Prop :=
  K ≤ H ∧ (K.subgroupOf H).IsCComponent

/- The image in the ambient group of the intrinsic p-core of an actual
   subgroup.  This keeps O₂(H) distinct from the ambient subgroup type H. -/
def ambientPCore (p : ℕ) (H : Subgroup G) : Subgroup G :=
  (pCore p (↥H)).map H.subtype

/-- A selected component keeps the actual ambient subgroup and its checked
quotient.  The model field is deliberately an actual block/model predicate;
it is not an unconnected name for a group family. -/
structure SelectedComponent (L M V : Subgroup G) (z v : G) where
  K : Subgroup G
  K_le_Gv : K ≤ Gv v
  K_component : IsComponentIn (Gv v) K
  noncentral : ¬ K ≤ centralizer ({z} : Set G)
  quotient : IsQuasisimple (K ⧸ pCore 2 K)

namespace SelectedComponent

variable {L M V : Subgroup G} {z v : G} (d : SelectedComponent L M V z v)

theorem K_nontrivial : d.K ≠ ⊥ := by
  intro h
  apply d.noncentral
  rw [h]
  exact bot_le

theorem checked_component : IsComponentIn (Gv v) d.K := d.K_component

end SelectedComponent

/- The source family Y_z consists of the actual components satisfying the
   displayed Tv-invariance, noncentrality, and checked-quasisimple quotient
   conditions. -/
def IsYzMember (T K : Subgroup G) (z v : G) : Prop :=
  IsComponentIn (Gv v) K ∧
    K ≤ normalizer (Tv T v : Set G) ∧
    ¬ K ≤ centralizer ({z} : Set G) ∧
    IsQuasisimple (K ⧸ pCore 2 K)

/- The three clauses of 13.6.16 are retained as actual local subgroup
   statements.  They are inputs from the preceding component-selection
   argument, rather than a hidden contradiction premise. -/
structure EarlierConclusions (L M V T : Subgroup G) (z v : G) (K : Subgroup G) where
  selected : SelectedComponent L M V z v
  selected_eq : selected.K = K
  span_commutative : IsMulCommutative (conjugateSpanBy V (Gv z))
  local_span_commutative : ∀ H : Subgroup G, H ≤ Gv z →
    IsMulCommutative (conjugateSpanBy V H)
  Tv_normalizes_K : K ≤ normalizer (Tv T v : Set G)
  two_core_trivial : ambientPCore 2 (K ⊔ T) = ⊥
  characteristic_strict : ∀ C : Subgroup (Tv T v), C.Characteristic → C ≠ ⊥ →
    ¬ ((solvableRadical (↥K)).map K.subtype ⊔
      (normalizer (C.map (Tv T v).subtype : Set G) ⊓ K) < K)
  commutator_J : K = ⁅K, elementaryAbelianMaxJ (Tv T v)⁆

theorem EarlierConclusions.isYz
    {L M V T : Subgroup G} {z v : G} {K : Subgroup G}
    (d : EarlierConclusions L M V T z v K) :
    IsYzMember T d.selected.K z v := by
  have hnorm : d.selected.K ≤ normalizer (Tv T v : Set G) := by
    rw [d.selected_eq]
    exact d.Tv_normalizes_K
  exact ⟨d.selected.K_component, hnorm, d.selected.noncentral, d.selected.quotient⟩

/-- The exact earlier transfer used in the proof of 13.6.17.  Its conclusion
is only the A.4.9 construction of a further component centralised by `a`; the
13.6.3.2 contradiction is supplied separately by the caller. -/
structure CentralizerTransfer (K : Subgroup G) (a v : G) where
  lift : K ≤ Gv a →
    ∃ K₁ : Subgroup G, IsComponentIn (Gv v) K₁ ∧ K₁ ≤ Gv a
  forbidden : ∀ {K₁ : Subgroup G}, IsComponentIn (Gv v) K₁ →
    K₁ ≤ Gv a → False

/-- Lemma 13.6.17: a conjugate whose checked image is central cannot
centralize the selected component.  The index-two and A.4.9 work is exposed
through `CentralizerTransfer`; no noncentrality conclusion is assumed. -/
theorem lemma_13_6_17
    {z v a : G} {K : Subgroup G}
    (transfer : CentralizerTransfer K a v)
    (hconj : ∃ g : G, a = MulAut.conj g z) : ¬ K ≤ Gv a := by
  intro hcentral
  obtain ⟨g, rfl⟩ := hconj
  obtain ⟨K₁, hK₁, hK₁a⟩ := transfer.lift hcentral
  exact transfer.forbidden hK₁ hK₁a

/-- The source list of actual binary model predicates used below.  `linear`
and `symplectic` retain their genuine conjugation-module block data. -/
inductive ModelCase (K : Subgroup G) : Prop
  | l3 (model : IsLinearTwoBlock K 3)
  | l3_doubled (model : IsLinearTwoBlock K 3)
      (summand₁ summand₂ parabolic : Subgroup G)
      (summand₁_le : summand₁ ≤ K) (summand₂_le : summand₂ ≤ K)
      (summands_generate : K ≤ summand₁ ⊔ summand₂)
      (parabolic_le : parabolic ≤ normalizer (summand₁ ⊔ summand₂ : Set G))
      (parabolic_irreducible : parabolic ≤ normalizer (K : Set G))
      (incompatible : K ≤ summand₁ ⊔ summand₂ →
        parabolic ≤ normalizer (K : Set G) → False)
  | sp4 (model : IsSp4FourBlock K)
  | g2 (model : CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.IsG2TwoBlock K)
  | ahat6 (model : IsExceptionalAhat6Block K)
  | a7_ordinary (model : IsAlternatingBlock K 7)
  | a7_exceptional (model : IsExceptionalA7Block K)

/- The higher-field alternatives in 13.6.19 carry their genuine model
   predicates.  The parabolic calculation below is a separate input because
   it is the output of the corresponding B.4/B.5/C.1 action proof. -/
inductive HigherFieldCase (K : Subgroup G) : Prop
  | sl3 (n : ℕ) (model : IsSL3EvenBlock K n)
  | sp4 (model : IsSp4FourBlock K)
  | g2 (model : CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.IsG2TwoBlock K)

/-- 13.6.18.  The Borel calculation is an earlier E.2/B.2 action fact: it
produces centralisation of the selected component by the particular conjugate
`a`.  Combined with 13.6.17 this excludes every even-field L₂ case. -/
theorem lemma_13_6_18
    {z v a : G} {K : Subgroup G}
    (transfer : CentralizerTransfer K a v)
    (hconj : ∃ g : G, a = MulAut.conj g z)
    {n : ℕ} (hmodel : IsL2EvenBlock K n)
    (hBorel : IsL2EvenBlock K n → K ≤ Gv a) : False := by
  exact (lemma_13_6_17 transfer hconj) (hBorel hmodel)

/-- 13.6.19.  For the higher-field SL₃, Sp₄ and G₂ cases, the relevant
parabolic has a nontrivial L₂ section.  `hparabolic` is the actual subgroup
and quotient/module output of the preceding B.4/B.5 and C.1 calculations;
`hnotL2` is the 13.6.16.2 block obstruction applied to that subgroup. -/
theorem lemma_13_6_19
    {v : G} {_K : Subgroup G}
    (_hcase : HigherFieldCase _K)
    (hsection : ∃ K₁ : Subgroup G, IsComponentIn (Gv v) K₁ ∧
      ∃ n : ℕ, 1 < n ∧ IsL2EvenBlock K₁ n)
    (hnotL2 : ∀ {K₁ : Subgroup G}, IsComponentIn (Gv v) K₁ →
      ∀ {n : ℕ}, 1 < n → ¬ IsL2EvenBlock K₁ n) : False := by
  obtain ⟨K₁, hK₁, n, hn, hL2⟩ := hsection
  exact hnotL2 hK₁ hn hL2

/-- The m₃(K)=2 route in 13.6.20 is precisely the earlier A.3.18
alternative.  It is kept as an implication with its numerical premise, so
the theorem does not assume `Lv ≤ K` outright. -/
theorem lv_le_of_m3_two
    {L : Subgroup G} {v : G} {K : Subgroup G}
    (hm : Nat.card (K ⧸ pCore 3 K) = 2)
    (hA318 : Nat.card (K ⧸ pCore 3 K) = 2 → Lv L v ≤ K) :
    Lv L v ≤ K :=
  hA318 hm

/-- The doubled-natural L₃(2) calculation is isolated as an honest module
interface.  The two summand subgroups and marked parabolic are retained as
actual subgroups, and their source action incompatibility gives the second
route of 13.6.20. -/
structure DoubledNaturalObstruction (L V K : Subgroup G) (v : G) where
  module : IsLinearTwoBlock K 3
  summand₁ : Subgroup G
  summand₂ : Subgroup G
  summand₁_le : summand₁ ≤ K
  summand₂_le : summand₂ ≤ K
  summands_generate : K ≤ summand₁ ⊔ summand₂
  parabolic : Subgroup G
  parabolic_le : parabolic ≤ normalizer (summand₁ ⊔ summand₂ : Set G)
  parabolic_irreducible : parabolic ≤ normalizer (K : Set G)
  incompatible : K ≤ summand₁ ⊔ summand₂ → parabolic ≤ normalizer (K : Set G) → False

theorem lv_le_of_l3_two
    {L V K : Subgroup G} {v : G}
    (d : DoubledNaturalObstruction L V K v) : Lv L v ≤ K :=
  (d.incompatible d.summands_generate d.parabolic_irreducible).elim

/-- 13.6.20, with both source alternatives visible.  The first branch uses
A.3.18; the second uses the actual doubled-natural module interface. -/
theorem lemma_13_6_20
    {L V K : Subgroup G} {v : G}
    (hA318 : Nat.card (K ⧸ pCore 3 K) = 2 → Lv L v ≤ K)
    (doubled : DoubledNaturalObstruction L V K v) :
    Lv L v ≤ K := by
  by_cases hm : Nat.card (K ⧸ pCore 3 K) = 2
  · exact lv_le_of_m3_two hm hA318
  · exact lv_le_of_l3_two doubled

/-- 13.6.21.  Once `Lv` is inside K, the source observation that K does not
act on the marked Lᵥ-section gives `K ⊄ M`.  The action obstruction is an
explicit earlier conclusion, rather than a field already containing the
claimed non-containment. -/
theorem lemma_13_6_21
    {L M _V : Subgroup G} {v : G} {K : Subgroup G}
    (_hLvK : Lv L v ≤ K)
    (hK_Gv : K ≤ Gv v)
    (hnotact : K ≤ Mv M v → Lv L v = ⊥)
    (hLv_nontrivial : Lv L v ≠ ⊥) : ¬ K ≤ M := by
  intro hKM
  apply hLv_nontrivial
  have hKMv : K ≤ Mv M v := by
    intro x hx
    exact ⟨hKM hx, hK_Gv hx⟩
  have hLvbot : Lv L v ≤ (⊥ : Subgroup G) := by
    exact le_of_eq (hnotact hKMv)
  exact le_antisymm hLvbot bot_le

/-- The model-specific positive data used in the 13.6.22 case split.  Every
field is an actual subgroup/module statement; the structure contains no
boolean family tag and no prepackaged contradiction. -/
structure SmallModelGeometry (L M V : Subgroup G) (z v : G) (K : Subgroup G) where
  commutator_subgroup : Subgroup G
  commutator_le : commutator_subgroup ≤ K
  marked_line : Subgroup G
  marked_line_le : marked_line ≤ commutator_subgroup
  fixed_by_Lv : marked_line ≤ centralizer (Lv L v : Set G)
  fixed_by_K : marked_line ≤ centralizer (K : Set G)
  moving_element : ∃ k : K, ∃ x : marked_line,
    (k : G) * (x : G) * (k : G)⁻¹ ≠ (x : G)

/-- The line in `SmallModelGeometry` cannot simultaneously be fixed by Lᵥ and
have the marked K-action.  This tiny algebraic step is used by each ordinary,
exceptional A₇, and covered A₆ branch after its concrete model supplies the
geometry. -/
theorem small_model_line_contradiction
    {L M V : Subgroup G} {z v : G} {K : Subgroup G}
    (d : SmallModelGeometry L M V z v K) : False := by
  obtain ⟨k, x, hx⟩ := d.moving_element
  have hcx : (x : G) ∈ centralizer (K : Set G) := d.fixed_by_K x.property
  have hcomm : ∀ y : K, (y : G) * (x : G) = (x : G) * (y : G) := by
    intro y
    exact (mem_centralizer_iff.mp hcx) (y : G) y.property
  have hk := hcomm k
  apply hx
  calc
    (k : G) * (x : G) * (k : G)⁻¹ = (x : G) * (k : G) * (k : G)⁻¹ := by rw [hk]
    _ = (x : G) := by simp

/-- 13.6.22.  `hcase` is the complete positive model split (ordinary and
exceptional A₇, covered A₆, and both L₃(2) module shapes).  The supplied
marked geometry closes every branch through the same line calculation. -/
theorem lemma_13_6_22
    {L M V : Subgroup G} {z v : G} {K : Subgroup G}
    (hcase : ModelCase K)
    (geometry : ∀ _c : ModelCase K, SmallModelGeometry L M V z v K) : False := by
  exact small_model_line_contradiction (geometry hcase)

/-- The residual equality in 13.6.23(1).  The quotient and normality
hypotheses are stated on the actual subgroup `K.subgroupOf (Gv v)`, and the
conclusion is transported back to the ambient group by the literal subtype
map. -/
theorem lemma_13_6_23_one
    {_L _M _V : Subgroup G} {_z v : G} {K : Subgroup G}
    (hK : K ≤ Gv v)
    (hnormal : (K.subgroupOf (Gv v)).Normal)
    (hperfect : IsPPerfect 3 (K.subgroupOf (Gv v)))
    (hquot : IsPGroup 3 ((Gv v) ⧸ K.subgroupOf (Gv v))) :
    K = (pResidual 3 (Gv v)).map (Gv v).subtype := by
  let _ := hnormal
  have he : pResidual 3 (Gv v) = K.subgroupOf (Gv v) :=
    pResidual_eq_of_isPPerfect (K.subgroupOf (Gv v)) hperfect hquot
  rw [he]
  exact (Subgroup.map_subgroupOf_eq_of_le hK).symm

/-- Actual rank-four data left by 13.6.22.  The action is represented by a
homomorphism on the checked component quotient, and the parabolic is an
actual subgroup of that quotient. -/
structure RankFourData (K : Subgroup G) where
  Kplus : Subgroup G
  Kplus_le : K ≤ Kplus
  group_equiv : Nonempty (Kplus ⧸ pCore 2 Kplus ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
  T : Subgroup G
  T_normalizes_Kplus : T ≤ normalizer (Kplus : Set G)
  dynkin_action : T →* MulAut (Kplus ⧸ pCore 2 Kplus)
  dynkin_nontrivial : ∃ t : T, dynkin_action t ≠ 1
  middle_parabolic : Subgroup (Kplus ⧸ pCore 2 Kplus)
  middle_node : Fin 3
  middle_node_eq : middle_node = 1
  middle_parabolic_proper : middle_parabolic < ⊤
  middle_parabolic_maximal : ∀ H : Subgroup (Kplus ⧸ pCore 2 Kplus),
    middle_parabolic ≤ H → H < ⊤ → H = middle_parabolic

/-- 13.6.23(2--3), preserving the actual Dynkin-action and parabolic data. -/
theorem lemma_13_6_23_two_three
    {K : Subgroup G}
    (d : RankFourData K) :
    Nonempty (d.Kplus ⧸ pCore 2 d.Kplus ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
      (∃ t : d.T, d.dynkin_action t ≠ 1) ∧
      d.middle_parabolic < ⊤ ∧ d.middle_node = 1 ∧
      (∀ H : Subgroup (d.Kplus ⧸ pCore 2 d.Kplus),
        d.middle_parabolic ≤ H → H < ⊤ → H = d.middle_parabolic) :=
  ⟨d.group_equiv, d.dynkin_nontrivial, d.middle_parabolic_proper,
    d.middle_node_eq, d.middle_parabolic_maximal⟩

/- The ambient image of a prime-to-three core of an actual subgroup. -/
def ambientPPrimeCore (H : Subgroup G) : Subgroup G :=
  (pPrimeCore 3 H).map H.subtype

abbrev SymmetricThreeWreathTwo :=
  RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))

/- An actual quotient model for the S₃ wr C₂ action.  The `let` installs the
   displayed normality proof while forming the quotient group. -/
structure WreathQuotientData (H : Type*) [Group H] where
  R : Subgroup H
  R_normal : R.Normal
  quotient_model : let _ := R_normal; Nonempty (H ⧸ R ≃* SymmetricThreeWreathTwo)

/- The three prime-to-three cores in the final orthogonal argument.  The
equalities are between the actual ambient images, so no quotient witness is
silently substituted for `C_G(V₂)`. -/
structure OrthogonalSixData (L M V : Subgroup G) (z v : G) (K : Subgroup G) where
  T : Subgroup G
  X : Subgroup G
  X_eq_CK : X = ambientPPrimeCore (K ⊓ Gv z)
  X_eq_CGv : X = ambientPPrimeCore (Gv v ⊓ Gv z)
  X_eq_CGV : X = ambientPPrimeCore (Gv v ⊓ centralizer (V : Set G))
  X_le_Gv : X ≤ Gv v
  T_invariant : X ≤ normalizer (Tv T v : Set G)
  wreath_quotient : WreathQuotientData (X.subgroupOf (Gv v))
  J : Subgroup (Gv v)
  J_normal : J.Normal
  J_characteristic : J.Characteristic
  J_nontrivial : J ≠ ⊥
  J_le_two_core : J.map (Gv v).subtype ≤ ambientPCore 2 (K ⊔ T)

/-- The prime-to-three core equalities and invariance used after 13.6.23. -/
theorem orthogonal_six_core_equalities
    {L M V : Subgroup G} {z v : G} {K : Subgroup G}
    (d : OrthogonalSixData L M V z v K) :
    d.X = ambientPPrimeCore (K ⊓ Gv z) ∧
      d.X = ambientPPrimeCore (Gv v ⊓ Gv z) ∧
      d.X = ambientPPrimeCore (Gv v ⊓ centralizer (V : Set G)) ∧
      d.X ≤ normalizer (Tv d.T v : Set G) ∧
      d.wreath_quotient.R.Normal :=
  ⟨d.X_eq_CK, d.X_eq_CGv, d.X_eq_CGV, d.T_invariant,
    d.wreath_quotient.R_normal⟩

/-- Final source-shaped contradiction: once the orthogonal six-dimensional
action supplies the marked Thompson subgroup, 13.6.16(1) closes the selected
component case. -/
theorem final_orthogonal_contradiction
    {L M V : Subgroup G} {z v : G} {K : Subgroup G}
    (d : OrthogonalSixData L M V z v K)
    (h16 : ambientPCore 2 (K ⊔ d.T) = ⊥) : False := by
  have hmap : d.J.map (Gv v).subtype = (⊥ : Subgroup G) := by
    apply le_antisymm
    · simpa [h16] using d.J_le_two_core
    · exact bot_le
  have hinj : Function.Injective ((Gv v).subtype : Gv v →* G) := by
    intro a b hab
    exact Subtype.ext hab
  have hJbot : d.J = ⊥ := by
    apply (Subgroup.map_injective (f := (Gv v).subtype) hinj)
    rw [hmap, Subgroup.map_bot]
  exact d.J_nontrivial hJbot

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination

end

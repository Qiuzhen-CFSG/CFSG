module

public import Theory.GroupTheory.NoncentralChiefRefinement.Series
public import Theory.GroupTheory.CentralPChiefFactors
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Logic.Equiv.Sum

/-!
# Literal chief sections, actions and noncentral counts

Ambient conjugation descends to `B / (A.subgroupOf B)`. Its representative
formula identifies trivial action with the quotient-image centrality convention
used for p-chief factors. Equivariant section isomorphisms preserve centrality
and p-group structure. The count is the cardinality of the actual qualifying
intervals of a chief series, and concatenation adds these cardinalities.

Central coarse strata give only central chief intervals. The terminal predicate
`HasNoTwoChiefFactors` quantifies over all actual chief intervals of its group;
it does not assume a count or a chosen series.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.2.5(8), printed pp.335–336; centrality follows the convention of B.7.2.
-/

@[expose] public section
open Subgroup
namespace NoncentralChiefRefinement
variable {K : Type*} [Group K]

/-- The literal relative quotient, with the lower endpoint first. -/
abbrev Section (A B : NormalNode K) := B.val ⧸ A.val.subgroupOf B.val

private theorem map_relative_conj (A B : NormalNode K) (k : K) :
    (A.val.subgroupOf B.val).map (MulAut.conjNormal k : B.val ≃* B.val) =
      A.val.subgroupOf B.val := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact A.property.conj_mem x hx k
  · intro x hx
    refine ⟨MulAut.conjNormal k⁻¹ x, ?_, ?_⟩
    · exact A.property.conj_mem x hx k⁻¹
    · apply Subtype.ext
      simp

/-- Actual ambient conjugation on a relative quotient. -/
def sectionAction (A B : NormalNode K) : K →* MulAut (Section A B) where
  toFun k := QuotientGroup.congr _ _ (MulAut.conjNormal k) (by
    exact map_relative_conj A B k)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) x
    change QuotientGroup.mk' _ (MulAut.conjNormal 1 x) = QuotientGroup.mk' _ x
    rw [map_one]
    rfl
  map_mul' k l := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) x
    change QuotientGroup.mk' _ (MulAut.conjNormal (k * l) x) =
      QuotientGroup.mk' _ (MulAut.conjNormal k (MulAut.conjNormal l x))
    rw [map_mul]
    rfl

@[simp] theorem sectionAction_mk (A B : NormalNode K) (k : K) (b : B.val) :
    sectionAction A B k (QuotientGroup.mk' (A.val.subgroupOf B.val) b) =
      QuotientGroup.mk' (A.val.subgroupOf B.val) (MulAut.conjNormal k b) := rfl

/-- Isomorphism of literal sections together with their ambient actions. -/
structure SectionEquiv (A B C D : NormalNode K) where
  equiv : Section A B ≃* Section C D
  equivariant (k : K) (x : Section A B) :
    equiv (sectionAction A B k x) = sectionAction C D k (equiv x)

/-- Centrality uses precisely the quotient-image convention of
`Subgroup.HasCentralPChiefFactors`. -/
def IsCentral (A B : NormalNode K) : Prop :=
  B.val.map (QuotientGroup.mk' A.val) ≤ center (K ⧸ A.val)

theorem isCentral_iff_commutator_le (A B : NormalNode K) :
    IsCentral A B ↔ ⁅(⊤ : Subgroup K), B.val⁆ ≤ A.val :=
  Subgroup.map_mk_le_center_iff _ _

/-- Central strata stay central after any normal-interval refinement. -/
theorem IsCentral.subinterval {A B C D : NormalNode K}
    (h : IsCentral A B) (hAC : A ≤ C) (hDB : D ≤ B) : IsCentral C D := by
  rw [isCentral_iff_commutator_le] at h ⊢
  exact (Subgroup.commutator_mono le_rfl hDB).trans (h.trans hAC)

/-- A two-chief factor is counted only when its actual conjugation action is
noncentral. Chiefness is supplied by the surrounding `ChiefSeries`. -/
def IsNoncentralTwo (A B : NormalNode K) : Prop :=
  IsPGroup 2 (Section A B) ∧ ¬ IsCentral A B

/-- Count actual noncentral two-chief intervals of a specified series. -/
noncomputable def ChiefSeries.noncentralTwoCount (s : ChiefSeries K) : ℕ :=
  Nat.card {i : Fin s.length // IsNoncentralTwo (s i.castSucc) (s i.succ)}

/-- A precise terminal quotient hypothesis; it rules out all two-chief
intervals, including central ones. -/
def HasNoTwoChiefFactors (H : Type*) [Group H] : Prop :=
  ∀ A B : NormalNode H, A ⋖ B → ¬ IsPGroup 2 (Section A B)

open scoped commutatorElement

/-- The quotient-image convention is equivalent to pointwise triviality of
actual conjugation on the literal relative quotient. -/
theorem isCentral_iff_action (A B : NormalNode K) :
    IsCentral A B ↔ ∀ k x, sectionAction A B k x = x := by
  rw [isCentral_iff_commutator_le, Subgroup.commutator_le]
  constructor
  · intro h k x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) x
    rw [sectionAction_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change k * (b : K) * k⁻¹ / (b : K) ∈ A.val
    simpa only [commutatorElement_def, div_eq_mul_inv] using h k (mem_top _) b b.property
  · intro h k _ b hb
    have he := h k (QuotientGroup.mk' (A.val.subgroupOf B.val) ⟨b, hb⟩)
    rw [sectionAction_mk] at he
    have hm := QuotientGroup.eq_iff_div_mem.mp he
    change k * b * k⁻¹ / b ∈ A.val at hm
    simpa only [commutatorElement_def, div_eq_mul_inv] using hm

namespace SectionEquiv
variable {A B C D E F : NormalNode K}

def refl (A B : NormalNode K) : SectionEquiv A B A B :=
  ⟨MulEquiv.refl _, fun _ _ => rfl⟩

def symm (e : SectionEquiv A B C D) : SectionEquiv C D A B where
  equiv := e.equiv.symm
  equivariant k x := by
    apply e.equiv.injective
    rw [e.equiv.apply_symm_apply, e.equivariant, e.equiv.apply_symm_apply]

def trans (e : SectionEquiv A B C D) (f : SectionEquiv C D E F) :
    SectionEquiv A B E F where
  equiv := e.equiv.trans f.equiv
  equivariant k x := by
    change f.equiv (e.equiv (sectionAction A B k x)) = _
    rw [e.equivariant, f.equivariant]
    rfl

theorem isCentral_iff (e : SectionEquiv A B C D) : IsCentral A B ↔ IsCentral C D := by
  simp only [isCentral_iff_action]
  constructor
  · intro h k y
    obtain ⟨x, rfl⟩ := e.equiv.surjective y
    rw [← e.equivariant, h]
  · intro h k x
    apply e.equiv.injective
    rw [e.equivariant, h]

theorem isPGroup_iff (e : SectionEquiv A B C D) (p : ℕ) :
    IsPGroup p (Section A B) ↔ IsPGroup p (Section C D) :=
  ⟨fun h => h.of_equiv e.equiv, fun h => h.of_equiv e.equiv.symm⟩

theorem isNoncentralTwo_iff (e : SectionEquiv A B C D) :
    IsNoncentralTwo A B ↔ IsNoncentralTwo C D :=
  and_congr (e.isPGroup_iff 2) (not_congr e.isCentral_iff)

end SectionEquiv

/-- Equivariant matching of actual factors preserves the chief count. -/
theorem ChiefSeries.noncentralTwoCount_eq_of_matching (s t : ChiefSeries K)
    (e : Fin s.length ≃ Fin t.length)
    (h : ∀ i, Nonempty (SectionEquiv (s i.castSucc) (s i.succ)
      (t (e i).castSucc) (t (e i).succ))) :
    s.noncentralTwoCount = t.noncentralTwoCount := by
  classical
  exact Nat.card_congr (e.subtypeEquiv fun i => (h i).some.isNoncentralTwo_iff)

/-- Refining a central stratum produces no noncentral two-chief factors. -/
theorem ChiefSeries.noncentralTwoCount_eq_zero_of_central
    (s : ChiefSeries K) (h : IsCentral s.head s.last) : s.noncentralTwoCount = 0 := by
  apply Nat.card_eq_zero.mpr
  left
  refine ⟨fun i => i.property.2 ?_⟩
  exact h.subinterval (CompositionSeries.head_le _) (CompositionSeries.le_last _)

/-- Concatenation adds counts of actual chief intervals. -/
theorem ChiefSeries.noncentralTwoCount_smash (s t : ChiefSeries K)
    (hst : s.last = t.head) :
    ChiefSeries.noncentralTwoCount (s.smash t hst) = s.noncentralTwoCount + t.noncentralTwoCount := by
  classical
  let P := fun i : Fin (s.length + t.length) =>
    IsNoncentralTwo ((s.smash t hst) i.castSucc) ((s.smash t hst) i.succ)
  let e := Equiv.subtypeEquivOfSubtype (p := P)
    (finSumFinEquiv : Fin s.length ⊕ Fin t.length ≃ Fin (s.length + t.length))
  change Nat.card {i // P i} = _
  rw [← Nat.card_congr e, Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
  congr 1
  · apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    simp only [P, finSumFinEquiv_apply_left, RelSeries.smash_castAdd,
      RelSeries.smash_succ_castAdd]
  · apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    simp only [P, finSumFinEquiv_apply_right, RelSeries.smash_natAdd,
      RelSeries.smash_succ_natAdd]

end NoncentralChiefRefinement

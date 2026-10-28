module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Notation
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Lifting the six-point stabilizer in the ordinary A₇ branch

The six-point stabilizer is the actual range of extension by the identity
on the seventh letter. Its isomorphism with A₆ is induced by the bijection
of the remaining six letters. Pull back that subgroup through the original
map K → K/O₂(K) → A₇ and take its two-residual. The restricted projection
is onto A₆ and has precisely the intrinsic two-core as kernel.

The source normalizer residual is contained in this lift by residual
monotonicity; normalization passes to the characteristic residual. Thus
movement of z by Lᵥ passes to the constructed subgroup. The elementary
three-transposition calculation identifies the fixed letter preserved by
the normalizer. No ambient normality of K or its stabilizer is assumed.

This is the construction part of the replacement. The earlier Thompson/
Baumann calculation must still supply the displayed placement hypotheses,
and the commutator-generation and local-family arguments must still prove
membership in the literal `ComponentSelection.Yz`. This module does not
claim to complete the ordinary A₇ branch.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, the ordinary A₇ paragraph on printed p.932 (PDF p.949).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven

/-- The alternating permutations of the six letters other than x. -/
def sixPoints (x : Fin 7) : Finset (Fin 7) := Finset.univ.erase x

def sixStabilizer (x : Fin 7) : Subgroup (alternatingGroup (Fin 7)) :=
  (alternatingGroup.ofSubtype (sixPoints x)).range

theorem mem_sixStabilizer_iff (x : Fin 7) (g : alternatingGroup (Fin 7)) :
    g ∈ sixStabilizer x ↔ (g : Equiv.Perm (Fin 7)) x = x := by
  rw [sixStabilizer, alternatingGroup.mem_range_ofSubtype_iff]
  constructor
  · intro h
    by_contra hn
    exact (Finset.mem_erase.mp (h (Equiv.Perm.mem_support.mpr hn))).1 rfl
  · intro h y hy
    exact Finset.mem_erase.mpr ⟨by
      intro he
      subst y
      exact Equiv.Perm.mem_support.mp hy h, Finset.mem_univ _⟩

noncomputable def sixStabilizerEquiv (x : Fin 7) :
    sixStabilizer x ≃* alternatingGroup (Fin 6) :=
  (MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := sixPoints x))).symm.trans
    (Fintype.equivFinOfCardEq (by simp [sixPoints] : Fintype.card (sixPoints x) = 6)).altCongrHom

private theorem six_perfect : Group.IsPerfect (alternatingGroup (Fin 6)) :=
  ⟨commutator_alternatingGroup_eq_top (by simp)⟩

private theorem six_core : pCore 2 (alternatingGroup (Fin 6)) = ⊥ := by
  let := alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 6))
  let := six_perfect
  rcases (inferInstance : (pCore 2 (alternatingGroup (Fin 6))).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp : IsPGroup 2 (alternatingGroup (Fin 6)) :=
      (h ▸ pCore_isPGroup).of_equiv (topEquiv (G := alternatingGroup (Fin 6)))
    let := hp.isNilpotent
    exact (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6)) inferInstance).elim

private theorem sixStabilizer_residual (x : Fin 7) : pResidual 2 (sixStabilizer x) = ⊤ := by
  let := six_perfect
  let : Group.IsPerfect (sixStabilizer x) :=
    Group.IsPerfect.ofSurjective (f := (sixStabilizerEquiv x).symm.toMonoidHom)
      (sixStabilizerEquiv x).symm.surjective
  apply (pResidual_eq_top_iff 2 _).mpr
  intro N hn hp
  let := hn
  let := hp.isNilpotent
  by_contra hn
  let : Nontrivial (sixStabilizer x ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
  exact Group.IsPerfect.not_isSolvable (sixStabilizer x ⧸ N) inferInstance

variable {H : Type*} [Group H]

/-- The literal inverse image in the original group. -/
def stabilizerPreimage (q : H →* alternatingGroup (Fin 7)) (x : Fin 7) : Subgroup H :=
  (sixStabilizer x).comap q

/-- Lift the two-residual, rather than identifying the full preimage with A₆. -/
def residualLift (q : H →* alternatingGroup (Fin 7)) (x : Fin 7) : Subgroup H :=
  (pResidual 2 (stabilizerPreimage q x)).map (stabilizerPreimage q x).subtype

theorem residualLift_le (q : H →* alternatingGroup (Fin 7)) (x : Fin 7) :
    residualLift q x ≤ stabilizerPreimage q x := map_subtype_le _

variable [Finite H]

theorem residualLift_image (q : H →* alternatingGroup (Fin 7))
    (hq : Function.Surjective q) (x : Fin 7) :
    (residualLift q x).map q = sixStabilizer x := by
  rw [residualLift, map_embedded_pResidual]
  have he : (stabilizerPreimage q x).map q = sixStabilizer x :=
    map_comap_eq_self_of_surjective hq _
  rw [he, sixStabilizer_residual, ← MonoidHom.range_eq_map, range_subtype]

/-- The restriction has the six-point stabilizer as its actual codomain. -/
def liftProjection (q : H →* alternatingGroup (Fin 7)) (x : Fin 7) :
    residualLift q x →* sixStabilizer x :=
  (q.comp (residualLift q x).subtype).codRestrict _ fun r => residualLift_le q x r.property

theorem liftProjection_surjective (q : H →* alternatingGroup (Fin 7))
    (hq : Function.Surjective q) (x : Fin 7) : Function.Surjective (liftProjection q x) := by
  intro a
  have ha : (a : alternatingGroup (Fin 7)) ∈ (residualLift q x).map q := by
    rw [residualLift_image q hq x]
    exact a.property
  obtain ⟨r, hr, he⟩ := ha
  exact ⟨⟨r, hr⟩, Subtype.ext he⟩

omit [Finite H] in
theorem liftProjection_kernel (q : H →* alternatingGroup (Fin 7)) (x : Fin 7) :
    (liftProjection q x).ker = q.ker.comap (residualLift q x).subtype := by
  ext r
  change liftProjection q x r = 1 ↔ q r = 1
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem liftProjection_kernel_eq_core (q : H →* alternatingGroup (Fin 7))
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker) (x : Fin 7) :
    (liftProjection q x).ker = pCore 2 (residualLift q x) := by
  have hp : IsPGroup 2 (liftProjection q x).ker := by
    rw [liftProjection_kernel]
    exact hk.comap_of_injective _ (residualLift q x).subtype_injective
  have hc : pCore 2 (sixStabilizer x) = ⊥ := by
    apply (map_eq_bot_iff_of_injective (f := (sixStabilizerEquiv x).toMonoidHom) _ (sixStabilizerEquiv x).injective).mp
    rw [pCore_map_iso, six_core]
  have he := (liftProjection q x).comap_pCore_of_ker_isPGroup
    (liftProjection_surjective q hq x) hp
  rw [hc] at he
  exact he

/-- First isomorphism theorem with the proved, literal two-core kernel. -/
noncomputable def residualLiftQuotientEquiv (q : H →* alternatingGroup (Fin 7))
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker) (x : Fin 7) :
    (residualLift q x ⧸ pCore 2 (residualLift q x)) ≃* alternatingGroup (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq (liftProjection_kernel_eq_core q hq hk x).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (liftProjection q x)
      (liftProjection_surjective q hq x)).trans (sixStabilizerEquiv x))

theorem residualLift_twoPerfect (q : H →* alternatingGroup (Fin 7)) (x : Fin 7) :
    IsPPerfect 2 (residualLift q x) := isPPerfect_embedded_pResidual 2 _

omit [Finite H] in
/-- Normalization is relative to the actual preimage. -/
theorem normalizes_residualLift (q : H →* alternatingGroup (Fin 7)) (x : Fin 7)
    (A : Subgroup H) (hA : A ≤ normalizer (stabilizerPreimage q x : Set H)) :
    A ≤ normalizer (residualLift q x : Set H) :=
  hA.trans (normalizer_le_normalizer_characteristic_image _ _)

omit [Finite H] in
/-- The source normalizer residual lies in the constructed lift as soon as
its normalizer lies in the six-point preimage. -/
theorem residual_le_residualLift (q : H →* alternatingGroup (Fin 7)) (x : Fin 7)
    (N : Subgroup H) (hN : N ≤ stabilizerPreimage q x) :
    (pResidual 2 N).map N.subtype ≤ residualLift q x := embedded_pResidual_mono 2 hN

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven

open Subgroup Equiv Equiv.Perm
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven

def threeTranspositions : Subgroup (Perm (Fin 7)) :=
  closure {swap 0 1, swap 2 3, swap 4 5}

theorem threeTranspositions_fix_six :
    threeTranspositions ≤ MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) := by
  rw [threeTranspositions, closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl <;> change _ = (6 : Fin 7) <;> decide

theorem threeTranspositions_unique_fixed (x : Fin 7)
    (hx : ∀ g ∈ threeTranspositions, g x = x) : x = 6 := by
  have h01 := hx (swap 0 1) (subset_closure (by simp))
  have h23 := hx (swap 2 3) (subset_closure (by simp))
  have h45 := hx (swap 4 5) (subset_closure (by simp))
  fin_cases x <;> simp_all

/-- The common fixed letter, and hence its six-letter complement, is preserved
by the entire normalizer of the three-transposition subgroup. -/
theorem normalizer_threeTranspositions_fix_six :
    normalizer (threeTranspositions : Set (Perm (Fin 7))) ≤
      MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) := by
  intro t ht
  apply threeTranspositions_unique_fixed
  intro g hg
  have hc : t⁻¹ * g * t ∈ threeTranspositions := by
    have hh := (mem_normalizer_iff.mp ((normalizer _).inv_mem ht) g).mp hg
    simpa using hh
  have hf : (t⁻¹ * g * t) (6 : Fin 7) = 6 := threeTranspositions_fix_six hc
  have he := congrArg t hf
  simpa using he
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven

open Subgroup
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven
variable {G : Type*} [Group G] (K : Subgroup G)

/-- The original quotient by O₂(K), with the chosen alternating coordinates. -/
def blockProjection (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    K →* alternatingGroup (Fin 7) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))

theorem blockProjection_surjective (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    Function.Surjective (blockProjection K e) := e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem blockProjection_kernel (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    (blockProjection K e).ker = pCore 2 K := by
  ext k
  change e (QuotientGroup.mk' (pCore 2 K) k) = 1 ↔ k ∈ pCore 2 K
  rw [e.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

def ambientPreimage (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (x : Fin 7) : Subgroup G := (stabilizerPreimage (blockProjection K e) x).map K.subtype

def replacement (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (x : Fin 7) : Subgroup G := (residualLift (blockProjection K e) x).map K.subtype

theorem replacement_le (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7) :
    replacement K e x ≤ K := map_subtype_le _

variable [Finite G]

theorem replacement_eq_residual_preimage
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7) :
    replacement K e x = (pResidual 2 (ambientPreimage K e x)).map (ambientPreimage K e x).subtype :=
  map_embedded_pResidual 2 _ K.subtype

noncomputable def replacementQuotientEquiv
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7) :
    (replacement K e x ⧸ pCore 2 (replacement K e x)) ≃* alternatingGroup (Fin 6) := by
  let eR := (residualLift (blockProjection K e) x).equivMapOfInjective K.subtype K.subtype_injective
  exact (QuotientGroup.congr _ _ eR (pCore_map_iso 2 eR)).symm.trans
    (residualLiftQuotientEquiv (blockProjection K e) (blockProjection_surjective K e)
      (by rw [blockProjection_kernel]; exact pCore_isPGroup) x)

theorem replacement_twoPerfect
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7) :
    IsPPerfect 2 (replacement K e x) := by
  rw [replacement_eq_residual_preimage]
  exact isPPerfect_embedded_pResidual 2 _

theorem normalizes_replacement
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7)
    (A : Subgroup G) (hA : A ≤ normalizer (ambientPreimage K e x : Set G)) :
    A ≤ normalizer (replacement K e x : Set G) := by
  rw [replacement_eq_residual_preimage]
  exact hA.trans (normalizer_le_normalizer_characteristic_image _ _)

theorem residual_le_replacement
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7)
    (N : Subgroup G) (hN : N ≤ ambientPreimage K e x) :
    (pResidual 2 N).map N.subtype ≤ replacement K e x := by
  rw [replacement_eq_residual_preimage]
  exact embedded_pResidual_mono 2 hN

/-- The lifting part of 13.6.22, applied to its literal relative normalizer.
The Thompson/Baumann source calculation still supplies the residual identity
and the two placement hypotheses. Y_z membership is a separate obligation. -/
theorem replacement_spec
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7)
    (L T S : Subgroup G) (z v : G)
    (hLv : Lv L v = (pResidual 2 (K ⊓ normalizer (S : Set G) : Subgroup G)).map
      (K ⊓ normalizer (S : Set G)).subtype)
    (hN : K ⊓ normalizer (S : Set G) ≤ ambientPreimage K e x)
    (hT : Tv T v ≤ normalizer (ambientPreimage K e x : Set G))
    (hz : ⁅zpowers z, Lv L v⁆ ≠ ⊥) :
    Lv L v ≤ replacement K e x ∧ replacement K e x ≤ K ∧
    Tv T v ≤ normalizer (replacement K e x : Set G) ∧
    ⁅zpowers z, replacement K e x⁆ ≠ ⊥ ∧
    Nonempty ((replacement K e x ⧸ pCore 2 (replacement K e x)) ≃*
      alternatingGroup (Fin 6)) := by
  have hL : Lv L v ≤ replacement K e x := by
    rw [hLv]
    exact residual_le_replacement K e x _ hN
  refine ⟨hL, replacement_le K e x, normalizes_replacement K e x _ hT, ?_,
    ⟨replacementQuotientEquiv K e x⟩⟩
  intro hzero
  exact hz (bot_unique ((commutator_mono le_rfl hL).trans hzero.le))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven

open Subgroup
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven
variable {G : Type*} [Group G] [Finite G] (K : Subgroup G)

/-- Keep the chosen quotient and module coordinates together, so later source
markings can use the defining equivariance of the same block model. -/
noncomputable def ordinaryModuleModel (h : ChapterC.IsAlternatingBlock K 7) :
    ChapterC.BlockModuleModel K h.2.2.choose := h.2.2.choose_spec.1.some

/-- The quotient coordinates belong to the same chosen natural-module model. -/
noncomputable def ordinaryQuotientEquiv (h : ChapterC.IsAlternatingBlock K 7) :
    (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7) :=
  (ordinaryModuleModel K h).quotientIso

/-- Construct the subgroup required by the ordinary-block replacement, including
its genuine A₆ quotient, from the source normalizer calculation. Membership in
Y_z and the source proof of the placement premises remain separate obligations;
this statement is the lifting step, not the completed Lemma 13.6.22. -/
theorem exists_replacement_of_source_placement
    (h : ChapterC.IsAlternatingBlock K 7) (x : Fin 7)
    (L T S : Subgroup G) (z v : G)
    (hLv : Lv L v = (pResidual 2 (K ⊓ normalizer (S : Set G) : Subgroup G)).map
      (K ⊓ normalizer (S : Set G)).subtype)
    (hN : K ⊓ normalizer (S : Set G) ≤ ambientPreimage K (ordinaryQuotientEquiv K h) x)
    (hT : Tv T v ≤ normalizer (ambientPreimage K (ordinaryQuotientEquiv K h) x : Set G))
    (hz : ⁅zpowers z, Lv L v⁆ ≠ ⊥) :
    ∃ K₁ : Subgroup G, Lv L v ≤ K₁ ∧ K₁ ≤ K ∧
      Tv T v ≤ normalizer (K₁ : Set G) ∧ ⁅zpowers z, K₁⁆ ≠ ⊥ ∧
      Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* alternatingGroup (Fin 6)) :=
  ⟨replacement K (ordinaryQuotientEquiv K h) x,
    replacement_spec K _ x L T S z v hLv hN hT hz⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven

end

module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.Stabilizers
public import Theory.GroupTheory.TwoPerfectCyclicQuotient
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Actual factor modules and local symmetric-three quotients

The Baumann invariance of the same source pair transports to its original
quotient, and the residual lift supplies [Lᵢ,J(T)]=Lᵢ. The two-core of M
normalizes both residual lifts, so their commutator modules lie in Lᵢ.
Two-perfectness makes these modules equal to their further commutators.

For a Sylow supplement U containing J(T), index three and Thompson saturation
exclude U being normal in LᵢU. Its three-coset action therefore identifies the
quotient by O₂(LᵢU) with S₃. These are the actual factors and modules used by
the later source LocalData construction.

Source: Aschbacher–Smith, 15.4.12(6), 15.4.19–20, printed pp.1160–1164.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure
open TwoFactors.SourceFactors.Permutation
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}

private theorem thompson_le_baumann (T : Subgroup G) :
    ChapterB.thompsonJ T 0 ≤ ChapterB.baumann T := by
  refine le_inf (ChapterB.thompsonJ_le _ _) ?_
  intro j hj a ha
  rw [ChapterB.thompsonAlpha_eq] at ha
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp ha).2.2 j hj |>.symm

/-- Each factor belongs to the original member X. -/
theorem Pair.factor_le (p : Pair T M X) (h : Input K T M X 2) (i : Bool) :
    p.quotient.factor i ≤ X := by
  cases i
  · exact le_sup_left.trans_eq (p.quotient.factor_generate h)
  · exact le_sup_right.trans_eq (p.quotient.factor_generate h)

/-- The original quotient map preserves the source Baumann invariance. -/
theorem Pair.quotient_baumann (p : Pair T M X) (h : Input K T M X 2) (i : Bool) :
    ((ChapterB.baumann (T : Subgroup G)).subgroupOf M).map (quotientMap M) ≤
      normalizer (p.quotient.line i : Set (CoreQuotient M)) := by
  have hLM := (p.factor_le h i).trans h.member_le
  have hn : (ChapterB.baumann (T : Subgroup G)).subgroupOf M ≤
      normalizer ((p.quotient.factor i).subgroupOf M : Set M) := by
    rw [← subgroupOf_normalizer_eq hLM]
    exact fun _ hx => p.baumann i hx
  have hm := (map_mono (f := quotientMap M) hn).trans
    (((p.quotient.factor i).subgroupOf M).le_normalizer_map (quotientMap M))
  change _ ≤ normalizer (image M (p.quotient.factor i) : Set (CoreQuotient M)) at hm
  rwa [SourceModules.factor_image p.quotient i] at hm

/-- Thompson saturation holds for the already selected pair, without choosing
another pair with potentially incompatible quotient coordinates. -/
theorem Pair.thompson_commutator (p : Pair T M X) (h : Input K T M X 2) (i : Bool) :
    ⁅p.quotient.factor i, ChapterB.thompsonJ (T : Subgroup G) 0⁆ = p.quotient.factor i :=
  p.quotient.factor_thompson_commutator h (p.quotient_baumann h) i

/-- The original local two-core normalizes each residual lift. -/
theorem Pair.core_normalizes_factor (p : Pair T M X) (i : Bool) :
    M.pCoreIn 2 ≤ normalizer (p.quotient.factor i : Set G) := by
  apply liftedFactors_normalized M (quotientMap M) p.quotient.line (pCore 2 M) i
  have he : (pCore 2 M).map (quotientMap M) = ⊥ := QuotientGroup.map_mk'_self _
  exact he ▸ bot_le

/-- The actual normal module V(M) lies in O₂(M). -/
theorem source_localV_le_core (h : Input K T M X 2) : localV T M ≤ M.pCoreIn 2 := by
  apply le_trans (map_mono (internalModule_le_core_omega T M h.sylow_le
    (h.ambient.evenCharacteristic T M h.maximal h.sylow_le)))
  exact map_mono (show Stellmacher.omegaOneCenterAmbient (pCore 2 M) ≤ pCore 2 M from
    fun _ hx => ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx).1)

/-- The source module Vᵢ is contained in its own actual factor. -/
theorem Pair.module_le_factor (p : Pair T M X) (h : Input K T M X 2) (i : Bool) :
    p.quotient.moduleFactor i ≤ p.quotient.factor i :=
  le_normalizer_iff_commutator_le_right.mp
    ((source_localV_le_core h).trans (p.core_normalizes_factor i))

/-- Every actual factor module is elementary abelian. -/
theorem Pair.module_elementary (p : Pair T M X) (h : Input K T M X 2) (i : Bool) :
    IsElementaryAbelian 2 (p.quotient.moduleFactor i) := by
  let := h.moved_elementary
  have hle : p.quotient.moduleFactor i ≤ movedModule (T : Subgroup G) M X :=
    commutator_mono le_rfl (p.factor_le h i)
  exact IsElementaryAbelian.of_le hle

/-- The actual factor acts on Vᵢ, and the commutator action is saturated. -/
theorem Pair.module_full_commutator (p : Pair T M X) (h : Input K T M X 2) (i : Bool) :
    ⁅p.quotient.moduleFactor i, p.quotient.factor i⁆ = p.quotient.moduleFactor i := by
  have hp : IsPGroup 2 (localV T M) :=
    (isPGroup_pCoreIn 2 M).to_le (source_localV_le_core h)
  exact commutator_isPPerfect_idempotent (p.quotient.factor i) (localV T M)
    (p.quotient.factor_perfect i) hp
    (((p.factor_le h i).trans h.member_le).trans (localV_normalized _ _))

/-- The other two-perfect factor centralizes this factor modulo its own core. -/
theorem Pair.sibling_commutator (p : Pair T M X) (h : Input K T M X 2) (i : Bool) :
    ⁅p.quotient.factor (!i), p.quotient.factor i⁆ ≤ (p.quotient.factor i).pCoreIn 2 :=
  commutator_le_pCoreIn_of_twoPerfect_of_normalizes_of_quotient_card_three
    _ _ (p.quotient.factor_perfect (!i))
    ((p.factor_le h (!i)).trans (p.quotient.factor_normalized h i))
    (p.quotient.factor_quotient_card i)

/-- The local S₃ quotient follows from the actual index-three Sylow subgroup
and the original Thompson commutator, rather than from a model assumption. -/
theorem Pair.local_symmetricThree (p : Pair T M X) (h : Input K T M X 2)
    (i : Bool) (U : Subgroup G)
    (hJU : ChapterB.thompsonJ (T : Subgroup G) 0 ≤ U)
    (P : Sylow 2 (p.quotient.factor i ⊔ U : Subgroup G))
    (hP : (P : Subgroup (p.quotient.factor i ⊔ U : Subgroup G)).map
      (p.quotient.factor i ⊔ U : Subgroup G).subtype = U)
    (hindex : U.relIndex (p.quotient.factor i ⊔ U) = 3) :
    Nonempty (((p.quotient.factor i ⊔ U : Subgroup G) ⧸
      pCore 2 (p.quotient.factor i ⊔ U : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  let D := p.quotient.factor i ⊔ U
  have hpidx : (P : Subgroup D).index = 3 := by
    have heq : ((P : Subgroup D).map D.subtype).relIndex D = (P : Subgroup D).index := by
      simpa only [← MonoidHom.range_eq_map, D.range_subtype, relIndex_top_right] using
        relIndex_map_map_of_injective (P : Subgroup D) ⊤ D.subtype_injective
    have hpi : U.relIndex D = 3 := hindex
    rw [← hP, heq] at hpi
    exact hpi
  have hproper : pCore 2 D < (P : Subgroup D) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P) ?_
    intro he
    have hUP : U = D.pCoreIn 2 := by rw [← hP, ← he]; rfl
    have hnU : D ≤ normalizer (U : Set G) := by
      rw [hUP]
      exact D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))
    have hLU : p.quotient.factor i ≤ U := by
      rw [← p.thompson_commutator h i]
      exact (commutator_mono le_rfl hJU).trans
        (le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hnU))
    have hDU : D = U := sup_eq_right.mpr hLU
    change U.relIndex D = 3 at hindex
    rw [hDU, relIndex_self] at hindex
    omega
  exact sylow_index_three_core_quotient P hpidx hproper

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses

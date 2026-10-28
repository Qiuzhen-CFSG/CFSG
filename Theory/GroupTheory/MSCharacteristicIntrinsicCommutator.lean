module
public import Theory.GroupTheory.MSCharacteristicAbelianCommutator
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PResidual.RelativeCoreCommutator
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# The intrinsic moving core under the Sylow characteristic condition

For a perfect normal subgroup K with quasisimple K/O₂(K), a Sylow supplement
identifies the image of K with F* of the ambient two-core quotient. The
ambient and intrinsic core commutators agree by perfect commutator
idempotence. Consequently the genuine characteristic-subgroup condition on
the full Sylow forces an abelian intrinsic moving core to be elementary.

This is the abelian exponent argument in Aschbacher--Smith C.1.31--34,
printed pp.135--137, applied without the universal MS classification.
The central-cover HS exclusion in original 15.1.22 is its direct consumer.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.MSAbelianCommutator
variable {G : Type*} [Group G] [Finite G]

/-- A perfect normal subgroup with quasisimple two-core quotient and a Sylow
supplement has elementary abelian moving core whenever that core is abelian
and no nontrivial characteristic subgroup of the Sylow is normal. -/
theorem intrinsic_elementary_of_abelian (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    [IsQuasisimple (K ⧸ pCore 2 K)] (S : Sylow 2 G)
    (hgen : K ⊔ (S : Subgroup G) = ⊤)
    (hms : ∀ C : Subgroup (S : Subgroup G), C.Characteristic →
      (C.map (S : Subgroup G).subtype).Normal → C = ⊥)
    (hc : IsMulCommutative (⁅pCore 2 K,(⊤ : Subgroup K)⁆ : Subgroup K)) :
    IsElementaryAbelian 2 (⁅pCore 2 K,(⊤ : Subgroup K)⁆ : Subgroup K) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let J := K.map q
  let : IsQuasisimple J := IsQuasisimple.of_mulEquiv (coreQuotientEquivImage 2 K)
  let : J.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hsup : J ⊔ (S : Subgroup G).map q = ⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hq : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ J) :=
    quotient_isPGroup_of_sup_eq_top ((S : Subgroup G).map q) J
      (S.isPGroup'.map q) ((sup_comm _ _).trans hsup)
  have hfit : generalizedFitting (G ⧸ pCore 2 G) = J :=
    generalizedFitting_eq_of_quasisimple_two_quotient J hq (pCore_quotient_pCore_eq_bot 2)
  have hp : IsPPerfect 2 K := by
    intro A hA ha
    let := hA
    let := ha.isNilpotent
    exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ A)
  have he : ⁅pCore 2 G,K⁆ = (⁅pCore 2 K,(⊤ : Subgroup K)⁆).map K.subtype := by
    apply le_antisymm
    · exact commutator_le_core_commutator_of_isSubnormal K (pCore 2 G)
        (inferInstance : K.Normal).isSubnormal hp pCore_isPGroup
        (by rw [normalizer_eq_top]; exact le_top)
    · rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]
      exact commutator_mono (by rw [pCore_eq_comap_of_normal]; exact map_comap_le _ _) le_rfl
  let := hc
  have hc' : IsMulCommutative (⁅pCore 2 G,K⁆ : Subgroup G) := by
    rw [he]
    infer_instance
  let := hc'
  have hel := elementary_of_abelian K S S.isPGroup' (fitting_pCore_le_sylow S) hgen hms hfit
  rw [he] at hel
  let := hel
  refine {
    toIsMulCommutative := hc
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  have hx : ((x : K) : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _
    (mem_map_of_mem K.subtype x.property)
  exact Subtype.ext (Subtype.ext hx)

end Theory.GroupTheory.MSAbelianCommutator

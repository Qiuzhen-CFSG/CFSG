module
public import Theory.GroupTheory.Fitting.TwoCorePreimage

/-!
# Fitting preimages under normal inclusions

The inverse image of F(G/O₂(G)) is characteristic. For a normal subgroup K,
its two-core lies in the ambient two-core. The induced quotient map carries
the nilpotent Fitting subgroup to a normal nilpotent subgroup, giving the
required containment of their literal preimages. Isomorphism transport uses
the same quotient construction.

Source: standard Fitting functoriality, used in Aschbacher–Smith C.2.6 and
the original 15.2.4 application, printed pp.145 and 1107.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The Fitting preimage above the two-core is characteristic. -/
instance twoFittingCore_characteristic : (twoFittingCore G).Characteristic :=
  Subgroup.Characteristic.comap_quotient_mk inferInstance

/-- Normal inclusions preserve containment in the two-core Fitting preimage. -/
theorem twoFittingCore_map_subtype_le_of_normal (K : Subgroup G) [K.Normal] :
    (twoFittingCore K).map K.subtype ≤ twoFittingCore G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let qK := QuotientGroup.mk' (pCore 2 K)
  have hk : pCore 2 K ≤ (q.comp K.subtype).ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mpr
      (pCoreIn_le_of_subnormal 2 (inferInstance : K.Normal).isSubnormal (mem_map_of_mem _ hx))
  let f := QuotientGroup.lift (pCore 2 K) (q.comp K.subtype) hk
  let F := (twoFittingCore K).map K.subtype
  let : (twoFittingCore K).Characteristic := twoFittingCore_characteristic
  let : F.Normal := inferInstance
  have he : F.map q = (fittingSubgroup (K ⧸ pCore 2 K)).map f := by
    rw [map_map]
    change ((fittingSubgroup (K ⧸ pCore 2 K)).comap qK).map (q.comp K.subtype) = _
    have hf : q.comp K.subtype = f.comp qK := rfl
    rw [hf, ←map_map,map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hn : (F.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hnil : Group.IsNilpotent (F.map q) := by
    rw [he]
    exact Group.nilpotent_of_surjective (f.subgroupMap _) (f.subgroupMap_surjective _)
  exact map_le_iff_le_comap.mp (le_sSup ⟨hn,hnil⟩)

/-- An isomorphism carries the Fitting preimage into the target preimage. -/
theorem twoFittingCore_map_equiv_le {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) : (twoFittingCore A).map e.toMonoidHom ≤ twoFittingCore B := by
  let f := QuotientGroup.congr (pCore 2 A) (pCore 2 B) e (pCore_map_iso 2 e)
  have hh : (fittingSubgroup (A ⧸ pCore 2 A)).map f.toMonoidHom ≤
      fittingSubgroup (B ⧸ pCore 2 B) := by
    exact le_sSup ⟨Normal.map inferInstance _ f.surjective,
      Group.nilpotent_of_surjective (f.toMonoidHom.subgroupMap _)
        (f.toMonoidHom.subgroupMap_surjective _)⟩
  rintro _ ⟨a,ha,rfl⟩
  apply hh
  refine ⟨QuotientGroup.mk' (pCore 2 A) a,ha,?_⟩
  exact QuotientGroup.congr_mk' (pCore 2 A) (pCore 2 B) e (pCore_map_iso 2 e) a

end Theory.GroupTheory

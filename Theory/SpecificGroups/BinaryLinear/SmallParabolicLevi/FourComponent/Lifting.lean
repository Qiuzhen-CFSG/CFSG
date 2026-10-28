module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# A local component over the binary rank-two quotient

A finite group whose quotient by its two-core is PSL₃(2) has a normal
C-component mapping onto that quotient. The component and the two-core
therefore generate the group, so the quotient by the component is a
two-group. In particular the component contains the two-residual, without
any assumption that the latter is perfect.

We embed this construction in a specified overgroup and retain the actual
quotient map on every representative. The component is local to that
overgroup; no subnormality in the larger ambient group is asserted.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.25, printed p.959 (PDF p.976). The lifting uses the genuine A.3.3
C-component correspondence and the proved matrix simplicity of PSL₃(2).
-/

@[expose] public section

namespace BinaryLinear.SmallParabolicLevi.FourComponent

open Subgroup BinaryLinear.SmallParabolicLevi

private theorem exists_intrinsic_component {G : Type*} [Group G] [Finite G]
    (e : (G ⧸ pCore 2 G) ≃* (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) :
    ∃ K : Subgroup G, K.IsCComponent ∧ K.Normal ∧ pResidual 2 G ≤ K ∧
      ∃ f : (K ⧸ pCore 2 K) ≃* (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)),
        ∀ k : K, f (QuotientGroup.mk' _ k) = e (QuotientGroup.mk' _ k.val) := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup 3) :=
    BinaryLinear.linearGroup_isPerfect 3 (by decide)
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := Group.IsPerfect.ofSurjective
    (f := linearThreeEquivProjective.toMonoidHom) linearThreeEquivProjective.surjective
  let : IsSimpleGroup (G ⧸ pCore 2 G) := e.isSimpleGroup
  let : Group.IsPerfect (G ⧸ pCore 2 G) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let t : (⊤ : Subgroup (G ⧸ pCore 2 G)) ≃* (G ⧸ pCore 2 G) := Subgroup.topEquiv
  let : IsSimpleGroup (⊤ : Subgroup (G ⧸ pCore 2 G)) := t.isSimpleGroup
  let : Group.IsPerfect (⊤ : Subgroup (G ⧸ pCore 2 G)) :=
    Group.IsPerfect.ofSurjective (f := t.symm.toMonoidHom) t.symm.surjective
  have ht : (⊤ : Subgroup (G ⧸ pCore 2 G)).IsCComponent :=
    Subgroup.isCComponent_of_isSimpleGroup_of_isPerfect (inferInstance : (⊤ : Subgroup (G ⧸ pCore 2 G)).Normal).isSubnormal
  let : Group.IsNilpotent (pCore 2 G) := (pCore_isPGroup (p := 2) (G := G)).isNilpotent
  obtain ⟨K, hK, hmap⟩ := ht.exists_map_quotient_eq (pCore 2 G)
  have hn : K.Normal := cComponent_normal_of_quotient_normal hK (pCore 2 G) (hmap.symm ▸ inferInstance)
  let := hn
  have hsup : K ⊔ pCore 2 G = ⊤ := by
    have h := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 G))) hmap
    simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using h
  have hr : pResidual 2 G ≤ K := sInf_le ⟨hn,
    isPGroup_quotient_of_sup_eq_top K (pCore 2 G) pCore_isPGroup hsup⟩
  let f := (cComponentTwoCoreQuotientEquiv hK).trans
    ((MulEquiv.subgroupCongr hmap).trans (Subgroup.topEquiv.trans e))
  refine ⟨K, hK, hn, hr, f, ?_⟩
  intro k
  rfl


/-- Lift the whole PSL₃(2) quotient to an actual normal local C-component,
retaining the embedded two-residual and the intrinsic quotient map. -/
theorem exists_component_of_twoCoreQuotient {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    (e : (P ⧸ pCore 2 P) ≃* (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) :
    ∃ (K : Subgroup G) (hKP : K ≤ P), (K.subgroupOf P).IsCComponent ∧
      P ≤ normalizer K ∧ (pResidual 2 P).map P.subtype ≤ K ∧
      ∃ f : (K ⧸ pCore 2 K) ≃* (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)),
        ∀ k : K, f (QuotientGroup.mk' _ k) =
          e (QuotientGroup.mk' _ (⟨k.val, hKP k.property⟩ : P)) := by
  obtain ⟨J, hJ, hn, hr, f, hf⟩ := exists_intrinsic_component e
  let K := J.map P.subtype
  have hKP : K ≤ P := map_subtype_le J
  have he : K.subgroupOf P = J := comap_map_eq_self_of_injective P.subtype_injective J
  have hK : (K.subgroupOf P).IsCComponent := he.symm ▸ hJ
  have hnormal : (K.subgroupOf P).Normal := he.symm ▸ hn
  let a : K ≃* J := (subgroupOfEquivOfLe hKP).symm.trans (MulEquiv.subgroupCongr he)
  let q : (K ⧸ pCore 2 K) ≃* (J ⧸ pCore 2 J) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  refine ⟨K, hKP, hK, (normal_subgroupOf_iff_le_normalizer hKP).mp hnormal,
    map_mono hr, q.trans f, ?_⟩
  intro k
  exact hf (a k)

end BinaryLinear.SmallParabolicLevi.FourComponent

end

module
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryAlternatingSevenControl.PointStabilizer
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Ambient
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SubgroupLocalStructureTransport

/-!
# Central involutions in exceptional A₇ extensions

Let U be a self-centralizing normal elementary group of order sixteen, with
quotient A₇. The faithful binary action is transitive on U minus the identity.
Its Sylow fixed line identifies the center of a Sylow two-subgroup as a group
of order two. For every nonidentity z in U, the actual point stabilizer action
on U/⟨z⟩ identifies C(z)/O₂(C(z)) with PSL₃(2), and O₂(C(z)) is precisely U.
No splitting of the extension is needed.

These are the local calculations in Aschbacher–Smith 5.2.12, printed p.654
(`refs/quasithin.pdf`). The source consumer separately proves the ambient
centralizer equality using characteristic two and the original Sylow subgroup.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace Theory.GroupTheory.QuasithinM23
variable {G : Type*} [Group G] [Finite G]
  (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
  (hU : Nat.card U = 16)
  (q : G →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
  (hk : q.ker = centralizer (U : Set G))

include hU in
omit [U.Normal] in
private theorem core_finrank : Module.finrank (ZMod 2) (Additive U) = 4 := by
  apply Nat.pow_right_injective (by decide : 1 < 2)
  calc
    2 ^ Module.finrank (ZMod 2) (Additive U) = Nat.card (Additive U) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    _ = 2 ^ 4 := (Nat.card_congr Additive.toMul).trans hU

include hU q hq hk

/-- Conjugation is transitive on the fifteen nonidentity core elements. -/
theorem core_transitive {x y : G} (hx : x ∈ U) (hy : y ∈ U)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : ∃ g : G, g*x*g⁻¹ = y := by
  let ρ := NormalElementaryQuotient.representation U q hq hk
  have hf := NormalElementaryQuotient.representation_injective U q hq hk
  obtain ⟨a,ha⟩ := BinaryAlternatingSevenControl.transitive ρ hf (core_finrank U hU)
    (v := Additive.ofMul ⟨x,hx⟩) (w := Additive.ofMul ⟨y,hy⟩)
    (fun he => hx1 (congrArg (fun v : Additive U => (v.toMul : G)) he))
    (fun he => hy1 (congrArg (fun v : Additive U => (v.toMul : G)) he))
  obtain ⟨g,rfl⟩ := hq a
  refine ⟨g,?_⟩
  have hh := congrArg (fun v : Additive U => (v.toMul : G)) ha
  exact (NormalElementaryQuotient.representation_apply U q hq hk g _).symm.trans hh

/-- The full Sylow center is the unique fixed line in the original core. -/
theorem sylow_center_two (hC : centralizer (U : Set G) = U) (P : Sylow 2 G) :
    centralizer ((P : Subgroup G) : Set G) ≤ U ∧ Nat.card (center P) = 2 := by
  have hUP : U ≤ (P : Subgroup G) :=
    (IsElementaryAbelian.isPGroup (p := 2) (G := U)).le_sylow_of_normal P
  have hCP : centralizer ((P : Subgroup G) : Set G) ≤ U :=
    (centralizer_le hUP).trans_eq hC
  refine ⟨hCP,?_⟩
  let ρ := NormalElementaryQuotient.representation U q hq hk
  have hf := NormalElementaryQuotient.representation_injective U q hq hk
  have hd := BinaryAlternatingSevenControl.sylow_fixed_finrank ρ hf (core_finrank U hU)
    (P.mapSurjective hq)
  have hc : Nat.card (U ⊓ centralizer ((P : Subgroup G) : Set G) : Subgroup G) = 2 := by
    rw [← Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv U q hq hk
      (P : Subgroup G))]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    change 2 ^ Module.finrank (ZMod 2)
      (Representation.BinaryOffender.fixedSpace ρ (P.mapSurjective hq)) = 2
    rw [hd]; norm_num
  rw [inf_eq_right.mpr hCP,
    centralizer_eq_mapped_center_of_le (P : Subgroup G) (hCP.trans hUP),
    card_map_of_injective (P : Subgroup G).subtype_injective] at hc
  exact hc

/-- The literal point centralizer has core U and quotient PSL₃(2). -/
theorem point_centralizer_geometry (hC : centralizer (U : Set G) = U)
    {z : G} (hz : z ∈ U) (hz1 : z ≠ 1) :
    (centralizer ({z} : Set G)).pCoreIn 2 = U ∧
      Nonempty ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let ρ := NormalElementaryQuotient.representation U q hq hk
  have hf := NormalElementaryQuotient.representation_injective U q hq hk
  let v : Additive U := Additive.ofMul ⟨z,hz⟩
  have hv : v ≠ 0 := fun he => hz1 (congrArg (fun v : Additive U => (v.toMul : G)) he)
  let C := centralizer ({z} : Set G)
  let D := BinaryAlternatingSevenControl.pointStabilizer ρ v
  have hpre : D.comap q = C := by
    ext x
    rw [mem_comap, BinaryAlternatingSevenControl.mem_pointStabilizer,
      mem_centralizer_singleton_iff]
    constructor
    · intro he
      have hh := congrArg (fun v : Additive U => (v.toMul : G)) he
      rw [NormalElementaryQuotient.representation_apply] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro he
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply]
      change x*z*x⁻¹=z
      rw [he,mul_inv_cancel_right]
  have hmap : C.map q = D := by rw [←hpre,map_comap_eq_self_of_surjective hq]
  let e := BinaryAlternatingSevenControl.pointStabilizerEquivPSL ρ hf (core_finrank U hU) hv
  have hD : pCore 2 D = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [pCore_map_iso,Matrix.PSL3Two.pCore_two_PSL_eq_bot,Subgroup.map_bot]
  have hker : IsPGroup 2 q.ker := by
    rw [hk,hC]
    exact IsElementaryAbelian.isPGroup 2 U
  have hzero : (C.pCoreIn 2).map q = ⊥ := by
    rw [map_pCoreIn_of_ker_isPGroup q hker C,hmap,pCoreIn,hD,Subgroup.map_bot]
  have hcore : C.pCoreIn 2 = U := by
    apply le_antisymm
    · exact ((Subgroup.map_eq_bot_iff _).mp hzero).trans_eq (hk.trans hC)
    · have hUC : U ≤ C := by
        intro u hu
        exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hu hz)
      exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U) hUC
        (le_normalizer_of_normal)
  refine ⟨hcore,?_⟩
  let f : C →* D := (MulEquiv.subgroupCongr hmap).toMonoidHom.comp (q.subgroupMap C)
  have hf' : Function.Surjective f :=
    (MulEquiv.subgroupCongr hmap).surjective.comp (q.subgroupMap_surjective C)
  have hkf : f.ker = pCore 2 C := by
    have he : U.subgroupOf C = pCore 2 C := by
      rw [←hcore]
      exact comap_map_eq_self_of_injective C.subtype_injective _
    rw [←he]
    ext x
    change f x = 1 ↔ (x : G) ∈ U
    rw [← Subtype.val_inj]
    change q x = 1 ↔ (x : G) ∈ U
    rw [←MonoidHom.mem_ker,hk,hC]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkf.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective f hf').trans e)⟩

end Theory.GroupTheory.QuasithinM23

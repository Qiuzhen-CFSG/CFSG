module
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Perpendicular
public import Theory.Representation.BinaryPermutation.EightPointTransport
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Perpendicular transport on the original six-space

The perpendiculars of two distinct points generate the original V, via
its actual group coordinates. Conjugation that induces a permutation
carries a point and its perpendicular together. It also carries the
intrinsic two-core of that point's ambient centralizer to the new one.

Source: Aschbacher--Smith, 12.6.24(3--5), printed pp.830--831.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
open BinaryPermutation BinaryPermutation.TerminalOrthogonal.Eight
variable {G : Type*} [Group G] (E : Setup G)

/-- The literal polar hyperplane at any point of the unchanged V. -/
noncomputable def pointPerpendicular (v : E.V) : Subgroup G :=
  ({ E with z := v } : Setup G).V₅

/-- Every point perpendicular is a subgroup of the original V. -/
theorem pointPerpendicular_le (v : E.V) : E.pointPerpendicular v ≤ E.V :=
  ({ E with z := v } : Setup G).V₅_le

/-- The actual coordinates test membership in a point perpendicular. -/
theorem mem_pointPerpendicular (v w : E.V) :
    w.val ∈ E.pointPerpendicular v ↔ form.polarBilin (E.coordinates v).toAdd
      (E.coordinates w).toAdd = 0 :=
  ({ E with z := v } : Setup G).mem_V₅_iff w

/-- Two distinct point perpendiculars generate the original V. -/
theorem pointPerpendicular_sup (v w : E.V) (hne : v ≠ w) :
    E.pointPerpendicular v ⊔ E.pointPerpendicular w = E.V := by
  apply le_antisymm (sup_le (E.pointPerpendicular_le v) (E.pointPerpendicular_le w))
  intro x hx
  have hn : (E.coordinates v).toAdd ≠ (E.coordinates w).toAdd := by
    intro hh
    exact hne (E.coordinates.injective hh)
  have he := EightGeometry.perpendicular_sup _ _ hn
  have hm : (E.coordinates ⟨x,hx⟩).toAdd ∈
      (form.polarBilin (E.coordinates v).toAdd).ker ⊔
        (form.polarBilin (E.coordinates w).toAdd).ker := he.symm ▸ Submodule.mem_top
  obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hm
  let av := E.coordinates.symm (Multiplicative.ofAdd a)
  let bv := E.coordinates.symm (Multiplicative.ofAdd b)
  have hav : av.val ∈ E.pointPerpendicular v := by
    apply (E.mem_pointPerpendicular v av).mpr
    simpa only [av,E.coordinates.apply_symm_apply,toAdd_ofAdd] using (show form.polarBilin (E.coordinates v).toAdd a = 0 from ha)
  have hbv : bv.val ∈ E.pointPerpendicular w := by
    apply (E.mem_pointPerpendicular w bv).mpr
    simpa only [bv,E.coordinates.apply_symm_apply,toAdd_ofAdd] using (show form.polarBilin (E.coordinates w).toAdd b = 0 from hb)
  have habv : av * bv = ⟨x,hx⟩ := by
    apply E.coordinates.injective
    rw [map_mul]
    apply Multiplicative.toAdd.injective
    simpa only [av,bv,E.coordinates.apply_symm_apply,toAdd_mul,toAdd_ofAdd] using hab
  have hm := (E.pointPerpendicular v ⊔ E.pointPerpendicular w).mul_mem
    (mem_sup_left hav) (mem_sup_right hbv)
  change (av*bv).val ∈ _ at hm
  rw [habv] at hm
  exact hm

variable [Finite G]

/-- Conjugation transports the point and its polar hyperplane together. -/
theorem pointPerpendicular_map (v : E.V) (hv : v ≠ 1)
    (a : normalizer (E.V : Set G))
    (p : Equiv.Perm (Fin 8))
    (hp : ∀ u : E.V, (E.coordinates (E.V.normalizerMonoidHom a u)).toAdd =
      naturalRepresentation (Fin 8) p (E.coordinates u).toAdd) :
    (E.pointPerpendicular v).map (MulAut.conj a.val).toMonoidHom =
      E.pointPerpendicular (E.V.normalizerMonoidHom a v) := by
  have hle : (E.pointPerpendicular v).map (MulAut.conj a.val).toMonoidHom ≤
      E.pointPerpendicular (E.V.normalizerMonoidHom a v) := by
    rintro _ ⟨x,hx,rfl⟩
    let u : E.V := ⟨x,E.pointPerpendicular_le v hx⟩
    change (E.V.normalizerMonoidHom a u).val ∈ _
    apply (E.mem_pointPerpendicular _ _).mpr
    rw [hp v,hp u]
    have hpolar : form.polarBilin (naturalRepresentation (Fin 8) p (E.coordinates v).toAdd)
        (naturalRepresentation (Fin 8) p (E.coordinates u).toAdd) =
          form.polarBilin (E.coordinates v).toAdd (E.coordinates u).toAdd := by
      simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,←map_add,form_invariant]
    rw [hpolar]
    exact (E.mem_pointPerpendicular v u).mp hx
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective (MulAut.conj a.val).injective]
  change Nat.card ({E with z := E.V.normalizerMonoidHom a v} : Setup G).V₅ ≤
    Nat.card ({E with z := v} : Setup G).V₅
  rw [perpendicular_card ({E with z := v} : Setup G) hv,perpendicular_card _ (by
    intro hh; exact hv ((E.V.normalizerMonoidHom a).injective
      (hh.trans (E.V.normalizerMonoidHom a).map_one.symm)))]

/-- The same conjugation transports containment in the point centralizer core. -/
theorem pointPerpendicular_core_transport (hz : E.z ≠ 1)
    (hcore : E.V₅ ≤ E.Gz.pCoreIn 2)
    (a : normalizer (E.V : Set G)) (p : Equiv.Perm (Fin 8))
    (hp : ∀ u : E.V, (E.coordinates (E.V.normalizerMonoidHom a u)).toAdd =
      naturalRepresentation (Fin 8) p (E.coordinates u).toAdd) :
    E.pointPerpendicular (E.V.normalizerMonoidHom a E.z) ≤
      (centralizer ({(E.V.normalizerMonoidHom a E.z).val} : Set G)).pCoreIn 2 := by
  rw [←E.pointPerpendicular_map E.z hz a p hp]
  have hc : E.Gz.map (MulAut.conj a.val).toMonoidHom =
      centralizer ({(E.V.normalizerMonoidHom a E.z).val} : Set G) := by
    rw [E.Gz_eq,Theory.GroupTheory.map_centralizer_equiv,Set.image_singleton]
    rfl
  rw [←hc,←map_pCoreIn_of_injective 2 E.Gz _ (MulAut.conj a.val).injective]
  exact map_mono hcore

end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup

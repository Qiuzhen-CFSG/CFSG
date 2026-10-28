module
public import Theory.SpecificGroups.SymmetricEight.NormalElementaryOdd
public import Theory.Representation.BinaryNaturalDual.FourActors.Model

/-!
# Normal elementary Sylow actors inducing outer GL₄(2) automorphisms

Conjugation contains every inner automorphism of the normal linear group.
An outer element makes the image all of Aut(GL₄(2)), identified with S₈
through the actual exceptional isomorphism. The original Sylow maps onto
an S₈ Sylow; its normal elementary actor has odd image and hence order at
least sixteen by the checked eight-point calculation. The same bound then
holds for the original actor, without assuming conjugation faithful.

Source: Aschbacher--Smith G.10.15(3), printed p.363, with the original
small-actor hypothesis of 14.3.12, printed p.993.
-/

public noncomputable section
namespace BinaryLinear.FourOuterSylowActor
open Subgroup Equiv.Perm
open Theory.SpecificGroups.SymmetricEight.NormalElementaryOdd
open BinaryLinear.OuterCyclic
open BinaryNaturalDual.FourActors

/-- A normal elementary Sylow actor inducing an outer action on a normal
binary degree-four linear group has order at least sixteen. -/
theorem normal_elementary_outer_actor_card
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (H : Subgroup D) [H.Normal] (S : Sylow 2 D) (X : Subgroup D)
    [IsElementaryAbelian 2 X]
    (hXS : X ≤ (S : Subgroup D)) (hSX : (S : Subgroup D) ≤ normalizer (X : Set D))
    (hd : Module.finrank (ZMod 2) W = 4)
    (e : H ≃* LinearMap.GeneralLinearGroup (ZMod 2) W)
    (x : X) (ho : (MulAut.conjNormal (x : D) : MulAut H) ∉ MulAut.innerSubgroup H) :
    16 ≤ Nat.card X := by
  let c : W ≃ₗ[ZMod 2] Space 4 := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hd)
  let e4 : H ≃* LinearGroup 4 := e.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv c).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space 4)))
  let C : D →* MulAut (LinearGroup 4) := (MulAut.congr e4).toMonoidHom.comp MulAut.conjNormal
  let f : D →* Equiv.Perm (Fin 8) := permutationEquiv.toMonoidHom.comp C
  have hinner (h : H) : f (h : D) = (linearAlternatingEquiv (e4 h)).val := by
    dsimp only [f,C,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
    rw [MulAut.conjNormal_val,MulAut.congr_conj,permutationEquiv_inner]
  have houter : C (x : D) ∉ MulAut.innerSubgroup (LinearGroup 4) := by
    intro hx
    rw [← MulAut.map_innerSubgroup_congr e4] at hx
    obtain ⟨a,ha,he⟩ := hx
    exact ho ((MulAut.congr e4).injective he ▸ ha)
  have hodd : f (x : D) ∉ alternatingGroup (Fin 8) := by
    intro hx
    exact houter ((permutationEquiv_mem_alternating _).mp hx)
  have hAlt : alternatingGroup (Fin 8) ≤ f.range := by
    intro y hy
    let h := e4.symm (linearAlternatingEquiv.symm ⟨y,hy⟩)
    refine ⟨(h : D),?_⟩
    rw [hinner]
    simp only [h,e4.apply_symm_apply,linearAlternatingEquiv.apply_symm_apply]
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    intro y _
    by_cases hy : y ∈ alternatingGroup (Fin 8)
    · exact hAlt hy
    · have hm : y * (f (x : D))⁻¹ ∈ alternatingGroup (Fin 8) := by
        rw [(alternatingGroup (Fin 8)).mul_mem_iff_of_index_two alternatingGroup.index_eq_two,
          (alternatingGroup (Fin 8)).inv_mem_iff]
        exact iff_of_false hy hodd
      have hh := f.range.mul_mem (hAlt hm) (show f (x : D) ∈ f.range from ⟨(x : D),rfl⟩)
      simpa only [inv_mul_cancel_right] using hh
  let P := S.mapSurjective hf
  let A := X.map f
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  have hAP : A ≤ (P : Subgroup (Equiv.Perm (Fin 8))) := Subgroup.map_mono hXS
  have hPA : (P : Subgroup (Equiv.Perm (Fin 8))) ≤ normalizer (A : Set (Equiv.Perm (Fin 8))) :=
    (Subgroup.map_mono hSX).trans (Subgroup.le_normalizer_map f)
  let a : A := ⟨f x,mem_map.mpr ⟨x,x.property,rfl⟩⟩
  have ha : (a : Equiv.Perm (Fin 8)).sign ≠ 1 := hodd
  exact (sylow_normal_elementary_card P A hAP hPA a ha).trans
    (Nat.le_of_dvd Nat.card_pos (X.card_map_dvd f))

end BinaryLinear.FourOuterSylowActor

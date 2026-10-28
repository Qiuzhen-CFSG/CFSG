module
public import Theory.Representation.SL3.PairedOddField
public import Theory.SpecificGroups.PSL3.PairedLinearDisplacement
public import Theory.LinearAlgebra.QuadraticRankOneDisplacement
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Odd displacement on a covered natural/dual pair

A small odd-prime actor has trivial common field coefficient. Its two linear
blocks then lie in an injective linear image of the original covering group.
The full marked SL₃ lies in that same image, so the scalar and reflection
obstructions give four field dimensions of displacement. The odd-prime rank
hypothesis remains on the original cover, including its full central kernel.
Source: Aschbacher--Smith H.0.1 and H.4.1, printed pp.377--379.
-/
public noncomputable section
open Matrix Module Subgroup Representation.BinaryOffender
namespace Representation.SL3NaturalFixed
variable {F H K : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group H] [Group K] [Finite K]

private def restrictLinearHom : ((Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) →*
    ((Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F)) where
  toFun := LinearEquiv.restrictScalars (ZMod 2)
  map_one' := by ext; rfl
  map_mul' := fun _ _ => by ext; rfl

private def binaryMatrixHom : GL (Fin 3) F →* (Module.End (ZMod 2) (Fin 3 → F))ˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → F)).symm.toMonoidHom.comp
    (restrictLinearHom.comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 3 → F)).toMonoidHom.comp
        GeneralLinearGroup.toLin.toMonoidHom))

omit [Finite F] in
private theorem binaryMatrixHom_injective : Function.Injective (binaryMatrixHom (F := F)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → F)).symm.injective.comp
    ((LinearEquiv.restrictScalars_injective (ZMod 2)).comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 3 → F)).injective.comp
        GeneralLinearGroup.toLin.injective))

omit [Finite F] in
private theorem matrix_of_field_linear
    (β : Representation (ZMod 2) H (Fin 3 → F)) (x : H)
    (hlin : ∀ (c : F) v, β x (c • v)=c • β x v) :
    ∃ S : GL (Fin 3) F, ∀ v, S.val *ᵥ v=β x v := by
  let l : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := β x
      map_add' := (β x).map_add
      map_smul' := fun c v => hlin c v }
  let e := LinearEquiv.ofBijective l
    (LinearMap.GeneralLinearGroup.toLinearEquiv (β.asGroupHom x)).bijective
  let S := GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  exact ⟨S,fun v => LinearMap.toMatrix'_mulVec l v⟩

private theorem matrix_displacement
    (β : Representation (ZMod 2) H (Fin 3 → F)) (x : H)
    (S : GL (Fin 3) F) (hS : ∀ v, S.val *ᵥ v=β x v) :
    fixedCodim β (zpowers x) = finrank (ZMod 2) F *
      finrank F (LinearMap.range (Matrix.toLin' S.val - LinearMap.id)) := by
  let e := (GeneralLinearGroup.toLin S).toLinearEquiv
  have he : (e.restrictScalars (ZMod 2)).toLinearMap=β x := by
    apply LinearMap.ext
    intro v
    exact hS v
  rw [fixedCodim_zpowers_eq_displacement_rank,←he]
  exact QuadraticForm.displacement_rank_restrictScalars (k := ZMod 2) e

/-- The paired beta bound for an actual covering group. The second marked
constituent is the literal field dual in prescribed field coordinates. -/
theorem paired_odd_displacement_of_cover
    (a : MulAut (SpecialLinearGroup (Fin 3) F))
    (d : (Fin 3 → F) ≃ₗ[F] Module.Dual F (Fin 3 → F))
    (hd : ∀ g v, d (specialLinearNatural 3 (a g) v) =
      (specialLinearNatural 3).dual g (d v))
    (β γ : Representation (ZMod 2) H (Fin 3 → F))
    (hfaithful : Function.Injective (β.prod γ))
    (α : H →* MulAut (SpecialLinearGroup (Fin 3) F))
    (hβ : ∀ x g v, β x (specialLinearNatural 3 g v) =
      specialLinearNatural 3 (α x g) (β x v))
    (hγ : ∀ x g v, γ x (specialLinearNatural 3 (a g) v) =
      specialLinearNatural 3 (a (α x g)) (γ x v))
    (f : K →* H) (hfs : Function.Surjective f)
    (j : SpecialLinearGroup (Fin 3) F →* H)
    (hjβ : ∀ g v, β (j g) v = specialLinearNatural 3 g v)
    (hjγ : ∀ g v, γ (j g) v = specialLinearNatural 3 (a g) v)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hrank : primeRank p K ≤ 2)
    (x : H) (hx : orderOf x=p) :
    4*finrank (ZMod 2) F ≤ fixedCodim (β.prod γ) (zpowers x) := by
  by_contra! hsmall
  let : Fact p.Prime := ⟨hp⟩
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let db := d.restrictScalars (ZMod 2)
  let δ : Representation (ZMod 2) H (Module.Dual F (Fin 3 → F)) :=
    db.conjRingEquiv.toMonoidHom.comp γ
  have hδ (y : H) (g) (φ : Module.Dual F (Fin 3 → F)) :
      δ y ((specialLinearNatural 3).dual g φ) =
        (specialLinearNatural 3).dual (α y g) (δ y φ) := by
    obtain ⟨v,rfl⟩ := d.surjective φ
    change d (γ y (d.symm ((specialLinearNatural 3).dual g (d v)))) =
      (specialLinearNatural 3).dual (α y g) (d (γ y (d.symm (d v))))
    rw [←hd,d.symm_apply_apply,d.symm_apply_apply,hγ,hd]
  let E := (LinearEquiv.refl (ZMod 2) (Fin 3 → F)).prodCongr db
  have hcoord (y : H) (v : (Fin 3 → F) × (Fin 3 → F)) :
      E ((β.prod γ) y v)=(β.prod δ) y (E v) := by
    refine Prod.ext ?_ ?_
    · rfl
    change d (γ y v.2)=d (γ y (d.symm (d v.2)))
    rw [d.symm_apply_apply]
  have hcod := fixedCodim_map_equivariant (β.prod γ) (β.prod δ)
    (MonoidHom.id H) E hcoord (zpowers x)
  simp only [Subgroup.map_id] at hcod
  have hsmall' : fixedCodim (β.prod δ) (zpowers x) < 4*finrank (ZMod 2) F :=
    hcod ▸ hsmall
  obtain ⟨hb,he⟩ := paired_odd_field_linear_of_small β δ α hβ hδ hp hodd x hx hsmall'
  have hg (c : F) (v : Fin 3 → F) : γ x (c • v)=c • γ x v := by
    apply d.injective
    have hh := he c (d v)
    change d (γ x (d.symm (c • d v)))=c • d (γ x (d.symm (d v))) at hh
    simpa only [←map_smul,d.symm_apply_apply] using hh
  obtain ⟨S₁,hS₁⟩ := matrix_of_field_linear β x hb
  obtain ⟨S₂,hS₂⟩ := matrix_of_field_linear γ x hg
  let S := (S₁,S₂)
  let r := (binaryMatrixHom (F := F)).prodMap (binaryMatrixHom (F := F))
  have hr : Function.Injective r := by
    intro v w he
    exact Prod.ext (binaryMatrixHom_injective (congrArg Prod.fst he))
      (binaryMatrixHom_injective (congrArg Prod.snd he))
  let U := β.asGroupHom.prod γ.asGroupHom
  have hU : Function.Injective U := by
    intro y z he
    apply hfaithful
    apply LinearMap.ext
    intro v
    exact Prod.ext
      (congrArg (fun b : (Module.End (ZMod 2) (Fin 3 → F))ˣ => b.val v.1)
        (congrArg Prod.fst he))
      (congrArg (fun b : (Module.End (ZMod 2) (Fin 3 → F))ˣ => b.val v.2)
        (congrArg Prod.snd he))
  have hRS : r S=U x := by
    apply Prod.ext
    · apply Units.ext
      exact LinearMap.ext hS₁
    · apply Units.ext
      exact LinearMap.ext hS₂
  have hj (g : SpecialLinearGroup (Fin 3) F) : r (g.toGL,(a g).toGL)=U (j g) := by
    apply Prod.ext
    · apply Units.ext
      exact LinearMap.ext (fun v => (hjβ g v).symm)
    · apply Units.ext
      exact LinearMap.ext (fun v => (hjγ g v).symm)
  have ho : orderOf S=p := by
    have hh := orderOf_injective r hr S
    rw [hRS,orderOf_injective U hU,hx] at hh
    exact hh.symm
  have hfirst (g : SpecialLinearGroup (Fin 3) F) :
      S₁*g.toGL*S₁⁻¹=(α x g).toGL := by
    apply mul_inv_eq_iff_eq_mul.mpr
    apply GeneralLinearGroup.toLin.injective
    apply Units.ext
    apply LinearMap.ext
    intro v
    change (S₁.val*g.val) *ᵥ v = ((α x g).val*S₁.val) *ᵥ v
    rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hS₁,hS₁]
    exact hβ x g v
  have hsecond (g : SpecialLinearGroup (Fin 3) F) :
      S₂*(a g).toGL*S₂⁻¹=(a (α x g)).toGL := by
    apply mul_inv_eq_iff_eq_mul.mpr
    apply GeneralLinearGroup.toLin.injective
    apply Units.ext
    apply LinearMap.ext
    intro v
    change (S₂.val*(a g).val) *ᵥ v = ((a (α x g)).val*S₂.val) *ᵥ v
    rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hS₂,hS₂]
    exact hγ x g v
  have hbound := Matrix.SL3Reflection.paired_linear_odd_displacement_in_injective_image
    a r hr (U.comp f) hrank hodd (fun g => by
      obtain ⟨k,hk⟩ := hfs (j g)
      exact ⟨k,by change U (f k)=r (g.toGL,(a g).toGL); rw [hk,hj]⟩)
    S (by
      obtain ⟨k,hk⟩ := hfs x
      exact ⟨k,by change U (f k)=r S; rw [hk,hRS]⟩) ho (α x) hfirst hsecond
  have hbnd := Nat.mul_le_mul_left (finrank (ZMod 2) F) hbound
  rw [fixedCodim_prod,matrix_displacement β x S₁ hS₁,
    matrix_displacement γ x S₂ hS₂] at hsmall
  dsimp only [S] at hbnd
  nlinarith
end Representation.SL3NaturalFixed

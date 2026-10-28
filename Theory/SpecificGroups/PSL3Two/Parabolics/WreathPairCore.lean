module
public import Theory.SpecificGroups.PSL3Two.Parabolics.WreathPair
public import Theory.GroupTheory.PCoreImage

/-!
# Two-cores of the paired binary-three parabolics

The coordinate S₄-to-S₃ quotient has two-group kernel and preserves the
factor permutation. Since S₃ wr C₂ has trivial two-core, the two-core of
either S₄ wreath parabolic lies in the base. This property survives a
two-group cover and the conjugation arranging an arbitrary full Sylow.
It supplies O₂(Hᵢ) ≤ T₁ in Aschbacher--Smith 10.2.5, pp.747--748.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Two.WreathPair

private abbrev W4 := RegularWreathProduct (Equiv.Perm (Fin 4)) Bit
private abbrev W3 := RegularWreathProduct (Equiv.Perm (Fin 3)) Bit

private def quotientHom : W4 →* W3 where
  toFun x := ⟨fun i => Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom (x.left i),x.right⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp

private theorem quotientHom_surjective : Function.Surjective quotientHom := by
  intro x
  choose a ha using fun i => Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom_surjective (x.left i)
  exact ⟨⟨a,x.right⟩,RegularWreathProduct.ext (funext ha) rfl⟩

private theorem wreath_core_right (x : W4) (hx : x ∈ pCore 2 W4) : x.right = 1 := by
  let e : W3 ≃* Theory.GroupTheory.WreathTwoResidual.Actor :=
    RegularWreathProduct.congr
      (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm
      (MulEquiv.refl Bit)
  have hz : pCore 2 W3 = ⊥ := by
    apply bot_unique
    intro y hy
    apply mem_bot.mpr
    apply e.injective
    have hm := mem_map_of_mem e.toMonoidHom hy
    rw [pCore_map_iso,Theory.GroupTheory.WreathTwoResidual.twoCore_eq_bot,mem_bot] at hm
    exact hm.trans e.map_one.symm
  let : ((pCore 2 W4).map quotientHom).Normal :=
    (inferInstance : (pCore 2 W4).Normal).map _ quotientHom_surjective
  have hl : (pCore 2 W4).map quotientHom ≤ pCore 2 W3 :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map quotientHom⟩
  have he := hl (mem_map_of_mem quotientHom hx)
  rw [hz,mem_bot] at he
  exact congrArg RegularWreathProduct.right he

private theorem point_core_right {x : Actor} (hx : x ∈ point.pCoreIn 2) : x.right = 1 := by
  obtain ⟨a,ha,rfl⟩ := hx
  have he : pointEquiv a ∈ pCore 2 W4 := by
    rw [← pCore_map_iso 2 pointEquiv]
    exact mem_map_of_mem pointEquiv.toMonoidHom ha
  simpa only [pointEquiv_right, Subgroup.subtype_apply] using wreath_core_right _ he

private theorem line_core_right {x : Actor} (hx : x ∈ line.pCoreIn 2) : x.right = 1 := by
  obtain ⟨a,ha,rfl⟩ := hx
  have he : lineEquiv a ∈ pCore 2 W4 := by
    rw [← pCore_map_iso 2 lineEquiv]
    exact mem_map_of_mem lineEquiv.toMonoidHom ha
  simpa only [lineEquiv_right, Subgroup.subtype_apply] using wreath_core_right _ he

variable {H : Type*} [Group H] [Finite H]

private def coreQuotientPreimage (f : H →* Actor) (hf : Function.Surjective f)
    (hp : IsPGroup 2 f.ker) (P : Subgroup Actor) :
    (P.comap f ⧸ pCore 2 (P.comap f)) ≃* (P ⧸ pCore 2 P) := by
  let r := f.subgroupComap P
  have hr : Function.Surjective r := f.subgroupComap_surjective_of_surjective P hf
  have hk : r.ker = f.ker.subgroupOf (P.comap f) := by
    ext x
    change (r x : P) = 1 ↔ f x = 1
    exact Subtype.ext_iff
  exact r.pCoreQuotientEquiv hr (by rw [hk]; exact hp.comap_subtype)

/-- The two actual Sylow parabolics with their cores in the factor-preserving base. -/
theorem exists_parabolics_with_core (f : H →* Actor) (hf : Function.Surjective f)
    (hp : IsPGroup 2 f.ker) (S : Sylow 2 H) :
    ∃ A B : Subgroup H, (S : Subgroup H) ≤ A ∧ (S : Subgroup H) ≤ B ∧
      IsCoatom A ∧ IsCoatom B ∧ A ≠ B ∧ A ⊔ B = ⊤ ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* Theory.GroupTheory.WreathTwoResidual.Actor) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Theory.GroupTheory.WreathTwoResidual.Actor) ∧
      (∀ a ∈ A.pCoreIn 2, (f a).right = 1) ∧
      (∀ b ∈ B.pCoreIn 2, (f b).right = 1) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Actor (S.mapSurjective hf) sylow
  let q := (MulAut.conj g).toMonoidHom.comp f
  have hq : Function.Surjective q := (MulAut.conj g).surjective.comp hf
  have hk : q.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  have hqp : IsPGroup 2 q.ker := hk ▸ hp
  have hS : (S : Subgroup H).map q = borel := by
    have he := congrArg Sylow.toSubgroup hg
    change ((S : Subgroup H).map f).map (MulAut.conj g).toMonoidHom = _ at he
    simpa only [Subgroup.map_map,sylow_eq] using he
  let A := point.comap q
  let B := line.comap q
  have hSA : (S : Subgroup H) ≤ A := map_le_iff_le_comap.mp (hS ▸ borel_le_point)
  have hSB : (S : Subgroup H) ≤ B := map_le_iff_le_comap.mp (hS ▸ borel_le_line)
  have hA : IsCoatom A := isCoatom_comap_of_surjective hq point_maximal
  have hB : IsCoatom B := isCoatom_comap_of_surjective hq line_maximal
  have hne : A ≠ B := by
    intro he
    have hh := congrArg (Subgroup.map q) he
    exact point_ne_line (by simpa only [A,B,map_comap_eq_self_of_surjective hq] using hh)
  have hgen : A ⊔ B = ⊤ := by
    apply hA.2
    apply lt_of_le_of_ne le_sup_left
    intro he
    have hBA : B ≤ A := he ▸ le_sup_right
    exact hA.ne_top (hB.2 _ (lt_of_le_of_ne hBA (Ne.symm hne)))
  have core_right (P : Subgroup Actor) (hP : ∀ x ∈ P.pCoreIn 2, x.right = 1)
      (x : H) (hx : x ∈ (P.comap q).pCoreIn 2) : (f x).right = 1 := by
    have hc : q x ∈ P.pCoreIn 2 := by
      rw [← map_comap_eq_self_of_surjective hq P,
        ← map_pCoreIn_of_ker_isPGroup q hqp]
      exact mem_map_of_mem q hx
    have he := hP _ hc
    change (g * f x * g⁻¹).right = 1 at he
    simpa only [RegularWreathProduct.mul_right,RegularWreathProduct.inv_right,
      mul_inv_eq_one, mul_eq_left] using he
  exact ⟨A,B,hSA,hSB,hA,hB,hne,hgen,
    ⟨(coreQuotientPreimage q hq hqp point).trans pointQuotientEquiv⟩,
    ⟨(coreQuotientPreimage q hq hqp line).trans lineQuotientEquiv⟩,
    core_right point (fun _ hx => point_core_right hx),
    core_right line (fun _ hx => line_core_right hx)⟩

end Matrix.PSL3Two.WreathPair

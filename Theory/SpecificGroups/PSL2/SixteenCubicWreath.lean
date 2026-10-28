module
public import Theory.GroupTheory.WreathFrattiniLift
public import Theory.FieldTheory.CubicSixteenAction
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.SpecificGroups.PSL2.BorelCoprimeFieldAction

/-!
# Recovering the full PSL₂(16) wreath group from its cubic Borel action

The field projection and restriction to actual cube roots of unity define
the two cubic torus coordinates of the automorphism wreath group. Their
image has order eight. Surjectivity on these coordinates lifts through the
Frattini field kernel; a subgroup containing the inner square is therefore
the entire automorphism wreath group.

The source applies this to its literal normal-square conjugation action
to obtain the required quotient isomorphism. The Borel formula
identifies the detector with the induced action modulo the actual unipotent
radical, including inner twists that need not preserve the diagonal torus.
The Chapter14 source application retains the original exchanged factors.
It must still establish order eight using the earlier cubic outside subgroup.

Source: Aschbacher--Smith 14.6.14(4), final paragraph, printed p.1033.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.PSL2.SixteenCubicWreath
open WreathTwoElementaryRank
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The actual coefficient action on the cubic roots in the Borel torus quotient. -/
@[expose] def cubicAction : MulAut (Theory.PSL2.Group F) →* MulAut (rootsOfUnity 3 F) :=
  (FiniteField.CubicSixteen.action F).comp (fieldProjection F)

/-- The two cubic torus coordinates, with the original exchanging permutation. -/
@[expose] def cubicWreathAction : W (MulAut (Theory.PSL2.Group F)) →* W (MulAut (rootsOfUnity 3 F)) :=
  RegularWreathProduct.mapBase (cubicAction F)

omit [CharP F 2] in
theorem cubic_target_card (hF : Nat.card F = 16) :
    Nat.card (W (MulAut (rootsOfUnity 3 F))) = 8 := by
  rw [RegularWreathProduct.card,FiniteField.CubicSixteen.action_target_card F hF]
  norm_num [C2]

/-- Full cubic image lifts through the Frattini field kernel and the inner square. -/
theorem full_of_cubic_surjective (hF : Nat.card F = 16)
    {A : Type*} [_root_.Group A] (ρ : A →* W (MulAut (Theory.PSL2.Group F)))
    (hinner : ∀ x y : Theory.PSL2.Group F, baseHom (MulAut.conj x,MulAut.conj y) ∈ ρ.range)
    (hfull : Function.Surjective ((cubicWreathAction F).comp ρ)) :
    Function.Surjective ρ := by
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  let π := RegularWreathProduct.mapBase (Q := C2) (fieldProjection F)
  have hfield : IsPGroup 2 (F ≃+* F) := IsPGroup.of_card (n := 2)
    (FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two (by simpa using hF))
  have hπρ : Function.Surjective (π.comp ρ) :=
    wreath_surjective_of_frattini_reduction hfield (FiniteField.CubicSixteen.action F)
      (FiniteField.CubicSixteen.action_ker_le_frattini F hF) (π.comp ρ) hfull
  have hk : π.ker ≤ ρ.range := by
    intro w hw
    have hr : w.right = 1 := congrArg RegularWreathProduct.right hw
    have hc (i : C2) : w.left i ∈ inner F := by
      rw [←fieldProjection_ker]
      exact congrArg (fun v => v.left i) hw
    obtain ⟨x,hx⟩ := (mem_inner_iff F _).mp (hc 1)
    obtain ⟨y,hy⟩ := (mem_inner_iff F _).mp (hc turn)
    have he : baseHom (MulAut.conj x,MulAut.conj y) = w := by
      apply RegularWreathProduct.ext
      · funext i
        rcases index_cases i with rfl | rfl
        · simpa [baseHom] using hx.symm
        · simpa [baseHom,turn_ne_one] using hy.symm
      · exact hr.symm
    exact he ▸ hinner x y
  have hgen : ρ.range ⊔ π.ker = ⊤ := by
    have hh := congrArg (comap π) (MonoidHom.range_eq_top.mpr hπρ)
    rw [MonoidHom.range_comp,comap_map_eq,comap_top] at hh
    exact hh
  rw [sup_eq_left.mpr hk] at hgen
  exact MonoidHom.range_eq_top.mp hgen

/-- Order eight of the actual cubic action is enough; no full outer-image premise is used. -/
theorem full_of_cubic_image_card (hF : Nat.card F = 16)
    {A : Type*} [_root_.Group A] (ρ : A →* W (MulAut (Theory.PSL2.Group F)))
    (hinner : ∀ x y : Theory.PSL2.Group F, baseHom (MulAut.conj x,MulAut.conj y) ∈ ρ.range)
    (hcard : Nat.card ((cubicWreathAction F).comp ρ).range = 8) :
    Function.Surjective ρ := by
  apply full_of_cubic_surjective F hF ρ hinner
  apply MonoidHom.range_eq_top.mp
  apply eq_of_le_of_card_ge le_top
  rw [card_top,cubic_target_card F hF,hcard]

open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
open Matrix.ProjectiveSpecialLinearGroup.OddBorel

omit [Finite F] in
private theorem coefficient_action_eq (σ : F ≃+* F) :
    Theory.PSL2.fieldAut σ = Atlas.fieldEquivPSL 2 σ := by
  ext x
  obtain ⟨g,rfl⟩ := Theory.PSL2.quotientMap_surjective F x
  rw [Theory.PSL2.fieldAut_apply_quotientMap]
  change _ = Atlas.fieldEquivPSL 2 σ (QuotientGroup.mk' _ g)
  rw [Atlas.fieldEquivPSL_mk]
  rfl

/-- On an aligned Borel, the detector is exactly the action on the cubic
part of its literal unipotent quotient. -/
theorem cubicAction_borel_quotient
    (α : MulAut (Theory.PSL2.Group F))
    (hU : (kernel F).map α.toMonoidHom = kernel F)
    (x : borel F) (hx : torusProjection F x ∈ rootsOfUnity 3 F) :
    ∃ y : borel F, (y : Theory.PSL2.Group F) = α x ∧
      torusProjection F y =
        (cubicAction F α ⟨torusProjection F x,hx⟩ : Fˣ) := by
  obtain ⟨g,σ,he⟩ := Theory.PSL2.semilinear_coverage α
  have he' : α = MulAut.conj g * Atlas.fieldEquivPSL 2 σ :=
    he.trans (congrArg (fun β => MulAut.conj g * β) (coefficient_action_eq F σ))
  have hg := inner_factor_mem_borel F g σ (he' ▸ hU)
  have hi : fieldProjection F (MulAut.conj g) = 1 := by
    change MulAut.conj g ∈ (fieldProjection F).ker
    rw [fieldProjection_ker]
    exact ⟨g,rfl⟩
  have hσ : fieldProjection F α = σ := by
    rw [he,map_mul,hi,fieldProjection_fieldAut,one_mul]
  refine ⟨borelActor F ⟨g,hg⟩ σ x,?_,?_⟩
  · rw [borelActor_apply_coe,←he']
  · rw [torusProjection_borelActor]
    change Units.map σ.toMonoidHom (torusProjection F x) =
      Units.map (fieldProjection F α).toMonoidHom (torusProjection F x)
    rw [hσ]

end Theory.PSL2.SixteenCubicWreath

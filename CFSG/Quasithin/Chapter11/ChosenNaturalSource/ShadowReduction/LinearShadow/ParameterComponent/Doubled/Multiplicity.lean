module
public import Theory.Representation.SL2SylowFixedRecognition.Definitions
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# The doubled rank budget forces one natural summand

A Sylow transvection fixes the first coordinate line in each natural summand.
The second-coordinate projection is therefore a surjective quotient of the
original module whose kernel contains its Sylow fixed space. Rank-nullity
bounds the multiplicity times the binary field degree by the actual fixed
codimension, without assuming a split central extension. At field degree 2n,
a positive multiplicity and the source 3n bound force multiplicity one.

Source: Aschbacher--Smith, 11.3.6, printed p.772. The source application is
in Doubled/RankBudget; the G.1.6 coordinate producer remains independent.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.SL2SylowFixedRecognition Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {F W : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

theorem quotient_multiplicity_bound (ρ : Representation (ZMod 2) SL(2,F) W)
    (c : QuotientCoordinates ρ) :
    c.multiplicity * Module.finrank (ZMod 2) F ≤ fixedCodim ρ (upperUnipotent F) := by
  let f : W →ₗ[ZMod 2] (Fin c.multiplicity → F) :=
    { toFun := fun w i => c.coordinates w i 1
      map_add' := by intro v w; ext i; exact congrFun (congrFun (c.coordinates.map_add v w) i) 1
      map_smul' := by intro a w; ext i; exact congrFun (congrFun (c.coordinates.map_smul a w) i) 1 }
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨w,hw⟩ := c.surjective (fun i => ![0,v i])
    exact ⟨w,by ext i; exact congrFun (congrFun hw i) 1⟩
  have hker : fixedSpace ρ (upperUnipotent F) ≤ LinearMap.ker f := by
    intro w hw
    change f w = 0
    ext i
    have ht := hw ⟨transvection zero_ne_one (1 : F),
      (mem_upperUnipotent F _).mpr ⟨1,rfl⟩⟩
    have he := congrArg (fun v => c.coordinates v i 0) ht
    change c.coordinates (ρ (transvection zero_ne_one (1 : F)) w) i 0 = c.coordinates w i 0 at he
    rw [c.intertwines] at he
    change c.coordinates w i 1 = 0
    simpa [transvection_coe,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using he
  have hdim := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hf,finrank_top] at hdim
  have hk := Submodule.finrank_mono hker
  have hfix := fixedCodim_add_finrank ρ (upperUnipotent F)
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at hdim
  simp only [Nat.cast_id] at hdim
  omega

theorem quotient_multiplicity_sylow_bound (ρ : Representation (ZMod 2) SL(2,F) W)
    (c : QuotientCoordinates ρ) (R : Sylow 2 SL(2,F)) :
    c.multiplicity * Module.finrank (ZMod 2) F ≤ fixedCodim ρ R := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F) (upperUnipotentSylow F 2) R
  have he : (R : Subgroup SL(2,F)) =
      (upperUnipotent F).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  rw [he,fixedCodim_map_conj]
  exact quotient_multiplicity_bound ρ c

theorem quotient_multiplicity_one (ρ : Representation (ZMod 2) SL(2,F) W)
    (c : QuotientCoordinates ρ) {n : ℕ} (hn : 0 < n)
    (hF : Module.finrank (ZMod 2) F = 2 * n)
    (hmove : ∃ g w, ρ g w ≠ w)
    (R : Sylow 2 SL(2,F)) (hbudget : fixedCodim ρ R ≤ 3 * n) : c.multiplicity = 1 := by
  have hl := quotient_multiplicity_sylow_bound ρ c R
  have hp := c.positive_of_movement hmove
  rw [hF] at hl
  nlinarith

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled

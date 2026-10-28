module
public import Theory.SpecificGroups.SymplecticFour.MaximalElementary.Point
public import Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.PointRadicalRoots
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Geometry

/-!
# Point-radical displacement and its critical root hyperplane

A nontrivial elementary group of transvections inside the point radical
moves precisely its defining point. Orthogonality identifies its fixed
hyperplane with the full radical's displacement space. Both spaces transport
under the same actual symplectic conjugation.

Source: MS93 (3.6), printed p.871, the equality controlling the secondary
seed before asserting full movement of its orbit modulo Z.
-/

public noncomputable section
open Subgroup Representation Module
open scoped IsMulCommutative commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.MaximalElementary
open Theory.SpecificGroups.SymplecticFour InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem point_displacement_eq_root_fixed
    (A B : Subgroup (Sp F)) [IsElementaryAbelian 2 B]
    (hBA : B ≤ A) (hne : B ≠ ⊥)
    (hroot : ∀ x ∈ B, Module.finrank F (movedSpace x) ≤ 1)
    (g : Sp F) (hA : A.map (MulAut.conj g).toMonoidHom = pointRadicalAmbient) :
    displacementSpace A = TwoLocalCover.fixedSpace B := by
  let B' := B.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 B' := IsElementaryAbelian.map _
  have hB' : B' ≤ pointRadicalAmbient := hA ▸ map_mono hBA
  have hne' : B' ≠ ⊥ := fun hh => hne
    ((map_eq_bot_iff_of_injective B (MulAut.conj g).injective).mp hh)
  have hr' : ∀ x ∈ B', Module.finrank F (movedSpace x) ≤ 1 := by
    rintro _ ⟨x,hx,rfl⟩
    change Module.finrank F (movedSpace (g*x*g⁻¹)) ≤ 1
    rw [movedSpace_conj,(toLinear g).finrank_map_eq]
    exact hroot x hx
  obtain ⟨x,hx,hd,hr⟩ := RootHyperplaneComparison.elementary_transvection_common_line B' hne' hr'
  have hrx : Module.finrank F (movedSpace x) = 1 := hd ▸ hr
  have hxt : IsB1 x := by
    refine ⟨orderOf_eq_prime_iff.mpr ⟨elemPow_eq_one_of_isElementaryAbelian x hx,?_⟩,hrx⟩
    intro he
    subst x
    have hz : movedSpace (1 : Sp F) = ⊥ := by
      apply le_bot_iff.mp
      rintro v ⟨w,rfl⟩
      change (1 : Sp F) • w-w = 0
      simp
    rw [hz,finrank_bot] at hrx
    omega
  obtain ⟨x₀,hx₀,hxx⟩ := hB' hx
  have hxline : movedSpace x = point F := by
    rw [←hxx]
    apply TransvectionRecognition.pointRadical_movedSpace_of_isB1 x₀ hx₀
    change IsB1 (pointLocal.subtype x₀)
    rwa [hxx]
  have hfixed : TwoLocalCover.fixedSpace B' = displacementSpace pointRadicalAmbient := by
    rw [←orthogonal_displacementSpace,hd,hxline,PointRadicalAction.radical_displacement]
  have hfixmap (v : Vector F) : g • v ∈ TwoLocalCover.fixedSpace B' ↔
      v ∈ TwoLocalCover.fixedSpace B := by
    constructor
    · intro hv x hx
      have he := hv ((MulAut.conj g) x) (mem_map_of_mem _ hx)
      apply (toLinear g).injective
      simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul,toLinear_apply] using he
    · intro hv x hx
      obtain ⟨y,hy,rfl⟩ := hx
      change (g*y*g⁻¹) • (g • v) = g • v
      simp only [mul_smul,inv_smul_smul,hv y hy]
  ext v
  rw [←hfixmap, hfixed,←hA,PointRadicalAction.displacement_conjugate]
  constructor
  · intro hv
    exact ⟨v,hv,rfl⟩
  · rintro ⟨w,hw,he⟩
    exact (toLinear g).injective he ▸ hw
end Theory.SpecificGroups.SymplecticFour.MaximalElementary


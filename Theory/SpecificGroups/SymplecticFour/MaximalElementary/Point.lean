module
public import Theory.SpecificGroups.SymplecticFour.MaximalElementary
public import Theory.SpecificGroups.SymplecticFour.FixedPlaneDisplacement
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.NaturalFixed

/-!
# Nonquadratic elementary images of maximum order

An elementary subgroup of Sp₄(q) of order q cubed is a conjugate of one of
the two parabolic radicals. The plane radical fixes a self-orthogonal plane,
so it acts quadratically on the natural module. A nonquadratic image is
therefore the point radical, under the actual symplectic conjugation.

Source: MS93 (3.6), printed p.871, identifying the full kernel image on
the original natural cover before the secondary seed calculation.
-/

public noncomputable section
open Subgroup Representation
namespace Theory.SpecificGroups.SymplecticFour.MaximalElementary
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

theorem conjugate_point_of_not_quadratic {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 0 < n)
    (A : Subgroup (Sp F)) [IsElementaryAbelian 2 A]
    (hc : Nat.card A = Nat.card F^3)
    (hnot : ¬ ∀ a ∈ A, ∀ b ∈ A, ∀ v : Vector F, a • (b • v-v) = b • v-v) :
    ∃ g : Sp F, A.map (MulAut.conj g).toMonoidHom = pointRadicalAmbient := by
  obtain ⟨g,hg | hg⟩ := conjugate_radical hF hn A hc
  · exact ⟨g,hg⟩
  · exfalso
    apply hnot
    have hfix (x : Sp F) (hx : x ∈ planeRadicalAmbient) (v : Vector F)
        (hv : v ∈ plane F) : x • v = v := by
      have hv' : v ∈ Representation.BinaryOffender.fixedSpace
          (SymplecticConjugatePair.binaryNatural (F := F)) SymplecticConjugatePair.planeRadical := by
        rw [SymplecticConjugatePair.planeRadical_natural_fixedSpace]
        exact hv
      exact hv' ⟨x,hx⟩
    have hP : (form F).orthogonal (plane F) = plane F := by
      ext v
      constructor
      · intro hv
        exact (orthogonal_plane_iff v).mp (fun y hy =>
          TwoLocalCover.form_alternating.eq_iff.mp (hv y hy))
      · intro hv y hy
        exact plane_isotropic y v hy hv
    have hquad (x : Sp F) (hx : x ∈ planeRadicalAmbient)
        (y : Sp F) (hy : y ∈ planeRadicalAmbient) (v : Vector F) :
        x • (y • v-v) = y • v-v :=
      hfix x hx _ (displacement_mem_of_self_orthogonal (plane F) hP y (hfix y hy) v)
    intro a ha b hb v
    have ha' : (MulAut.conj g) a ∈ planeRadicalAmbient := hg ▸ mem_map_of_mem _ ha
    have hb' : (MulAut.conj g) b ∈ planeRadicalAmbient := hg ▸ mem_map_of_mem _ hb
    have he := hquad _ ha' _ hb' (g • v)
    apply (toLinear g).injective
    simpa only [MulAut.conj_apply, mul_smul, inv_smul_smul, smul_sub,
      toLinear_apply] using he
end Theory.SpecificGroups.SymplecticFour.MaximalElementary

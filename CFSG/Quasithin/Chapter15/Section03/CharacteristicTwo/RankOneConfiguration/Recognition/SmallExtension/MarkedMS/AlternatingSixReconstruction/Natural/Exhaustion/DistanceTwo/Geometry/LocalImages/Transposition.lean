module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.FourImage

/-!
# The involution underlying an original critical image

A central involution whose natural displacement is fixed by a nonquadratic
binary image in S₆ is a transposition. Sylow conjugacy reduces the argument
to sixteen explicit words; the finite certificate tests only the five pair
vectors generating the natural quotient. Its conclusion concerns quadratic
movement on the whole augmentation cover, retaining the constant line.

The literal replacement application is in CriticalTransposition. Source:
MS93 (3.3)(ii)(2) and (3.6), printed pp.866--871.
-/

public noncomputable section

open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
private def quadraticTest (a b : Six.Perm) : Prop :=
  ∀ v : Fin 6 → ZMod 2,
    representation (Fin 6) a (representation (Fin 6) b v-v) =
      representation (Fin 6) b v-v
private instance (a b : Six.Perm) : Decidable (quadraticTest a b) := by
  unfold quadraticTest
  infer_instance

private instance (g : Six.Perm) : Decidable g.IsSwap := by
  unfold Equiv.Perm.IsSwap
  infer_instance

private theorem involution_fixer_table : ∀ i : Fin 16,
    Six.sylowWords i ≠ 1 → Six.sylowWords i ^ 2 = 1 →
    (Six.sylowWords i).IsSwap ∨
      ∀ j k : Fin 16,
        fixesTest (Six.sylowWords j) (Six.sylowWords i) →
        fixesTest (Six.sylowWords k) (Six.sylowWords i) →
        Six.sylowWords j * Six.sylowWords i = Six.sylowWords i * Six.sylowWords j →
        Six.sylowWords k * Six.sylowWords i = Six.sylowWords i * Six.sylowWords k →
        quadraticTest (Six.sylowWords j) (Six.sylowWords k) := by decide +kernel

private theorem isSwap_of_conjugate (g a : Six.Perm)
    (ha : ((MulAut.conj g) a).IsSwap) : a.IsSwap := by
  obtain ⟨i,j,hij,he⟩ := ha
  have ha' : a = (MulAut.conj g⁻¹) (Equiv.swap i j) := by
    rw [←he]
    simp [MulAut.conj_apply,mul_assoc]
  rw [ha']
  change (g⁻¹ * Equiv.swap i j * (g⁻¹)⁻¹).IsSwap
  rw [←Equiv.swap_apply_apply]
  exact ⟨g⁻¹ i,g⁻¹ j,(Equiv.injective g⁻¹).ne hij,rfl⟩

/-- A central involution whose natural displacement is fixed by a
nonquadratic two-image must be a transposition. Quadraticity is tested on
the entire augmentation cover, including its constant line. -/
theorem isSwap_of_nonquadratic_fixer (A B : Subgroup Six.Perm)
    (hp : IsPGroup 2 B) (hAB : A ≤ B)
    (hcentral : B ≤ centralizer (A : Set Six.Perm))
    (hfix : B ≤ subspaceKernel (naturalRepresentation (Fin 6))
      (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A) ⊤)
    (hnq : ¬ IsQuadratic (coreRepresentation (Fin 6)) B)
    {a : Six.Perm} (ha : a ∈ A) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) : a.IsSwap := by
  obtain ⟨P,hBP⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Six.Perm P Six.sylow
  let Ac := A.map (MulAut.conj g).toMonoidHom
  let Bc := B.map (MulAut.conj g).toMonoidHom
  have hBc : Bc ≤ Six.sylowCarrier := by
    rintro _ ⟨b,hb,rfl⟩
    change (MulAut.conj g) b ∈ (Six.sylow : Subgroup Six.Perm)
    rw [←hg]
    exact mem_map_of_mem _ (hBP hb)
  have hac : (MulAut.conj g) a ∈ Ac := mem_map_of_mem _ ha
  have hcentral' : Bc ≤ centralizer (Ac : Set Six.Perm) := by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨a,ha,rfl⟩
    exact (map_mul (MulAut.conj g) a b).symm.trans
      ((congrArg (MulAut.conj g) (hcentral hb a ha)).trans (map_mul (MulAut.conj g) b a))
  have hfix' := moved_fixer_conjugate A B g hfix
  obtain ⟨i,hi⟩ := (Six.mem_sylowCarrier_iff _).mp
    (hBc (mem_map_of_mem _ (hAB ha)))
  have hi1 : Six.sylowWords i ≠ 1 := by
    rw [hi]
    intro hh
    exact ha1 ((MulAut.conj g).map_eq_one_iff.mp hh)
  have hi2 : Six.sylowWords i ^ 2 = 1 := by
    rw [hi,←map_pow,ha2,map_one]
  rcases involution_fixer_table i hi1 hi2 with hs | hq
  · apply isSwap_of_conjugate g a
    rwa [hi] at hs
  · exfalso
    apply hnq
    have hquad : IsQuadratic (coreRepresentation (Fin 6)) Bc := by
      intro x hx y hy v
      obtain ⟨j,rfl⟩ := (Six.mem_sylowCarrier_iff x).mp (hBc hx)
      obtain ⟨k,rfl⟩ := (Six.mem_sylowCarrier_iff y).mp (hBc hy)
      apply Subtype.ext
      apply hq j k
      · rw [hi]
        exact fixesTest_of_fixes_moved Ac Bc hfix' hac hx
      · rw [hi]
        exact fixesTest_of_fixes_moved Ac Bc hfix' hac hy
      · rw [hi]
        exact (hcentral' hx _ hac).symm
      · rw [hi]
        exact (hcentral' hy _ hac).symm
    have hh := PlaneMovement.quadratic_conjugate (coreRepresentation (Fin 6)) Bc hquad g⁻¹
    have he : Bc.map (MulAut.conj g⁻¹).toMonoidHom = B := by
      rw [map_map]
      have hi : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          MonoidHom.id _ := by ext x; simp [MulAut.conj_apply,mul_assoc]
      rw [hi,map_id]
    rwa [he] at hh

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages

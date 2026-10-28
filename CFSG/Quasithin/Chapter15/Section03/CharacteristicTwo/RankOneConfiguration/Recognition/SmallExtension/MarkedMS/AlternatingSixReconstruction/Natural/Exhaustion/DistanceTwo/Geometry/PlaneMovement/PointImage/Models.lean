module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Reduction
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Model
public import Theory.Representation.BinaryPermutationSixCover.Universal
public import Theory.Representation.BinaryOffender.QuadraticDualOffender

/-!
# The two elementary-eight images on the whole six-letter cover

Sylow conjugacy and the existing elementary subgroup census leave the
ordinary disjoint-transposition group and the point core. The ordinary
class is quadratic on the entire augmentation cover, by a small kernel
checked calculation. Conjugation preserves quadraticity. The application
in Source excludes this class using the actual replacement displacement.

Source: MS93 (3.6), printed p.871; Aschbacher--Smith B.3.2 and B.3.4,
printed pp.83--85.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement
open CFSG.Quasithin.ChapterB.Offenders

theorem ordinary_core_quadratic : IsQuadratic (coreRepresentation (Fin 6)) (D 6) := by
  intro a ha b hb v
  obtain ⟨i,rfl⟩ := (Six.mem_disjointTranspositions_iff (3 : Fin 4) a).mp ha
  obtain ⟨j,rfl⟩ := (Six.mem_disjointTranspositions_iff (3 : Fin 4) b).mp hb
  apply Subtype.ext
  have cert : ∀ i j : Fin 8, ∀ v : Fin 6 → ZMod 2,
      representation (Fin 6) (Six.initialWords 3 i)
        (representation (Fin 6) (Six.initialWords 3 j) v - v) =
      representation (Fin 6) (Six.initialWords 3 j) v - v := by decide +kernel
  exact cert i j v.val

theorem quadratic_conjugate {K V : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) K V)
    (A : Subgroup K) (hq : IsQuadratic ρ A) (g : K) :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
  have hinv (v : V) : ρ g⁻¹ (ρ g v) = v := by
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hginv (v : V) : ρ g (ρ g⁻¹ v) = v := by
    simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  change ρ (g*a*g⁻¹) (ρ (g*b*g⁻¹) v-v) = ρ (g*b*g⁻¹) v-v
  have he : ρ (g*b*g⁻¹) v-v = ρ g (ρ b (ρ g⁻¹ v)-ρ g⁻¹ v) := by
    simp only [map_sub,map_mul,Module.End.mul_apply,hginv]
  rw [he]
  simp only [map_mul,Module.End.mul_apply,hinv,hq a ha b hb]

/-- Every elementary eight in S6 is one of the two literal conjugacy classes. -/
theorem elementary_eight_models (A : Subgroup (Equiv.Perm (Fin 6)))
    [IsElementaryAbelian 2 A] (hc : Nat.card A = 8) :
    (∃ g, A = (D 6).map (MulAut.conj g).toMonoidHom) ∨
      ∃ g, A = Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj g).toMonoidHom := by
  have hn : A ≠ ⊥ := by intro he;rw [he,card_bot] at hc;omega
  obtain ⟨B,hB,hcases,hAB⟩ := Six.exists_conjugate_le_D_or_exceptional ⟨hn,inferInstance⟩
  have hBc : Nat.card B = 8 := hAB.card_eq.symm.trans hc
  rcases hcases with hD | hE
  · have hd : Nat.card (D 6) = 8 := Six.card_disjointTranspositions 3
    have he : B = D 6 := eq_of_le_of_card_ge hD (hBc.trans hd.symm).ge
    exact Or.inl (he ▸ hAB)
  · have he : B = exceptional 6 (by decide) :=
      eq_of_le_of_card_ge hE (hBc.trans Six.card_exceptional.symm).ge
    have he : B = Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore :=
      he.trans CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.symm
    exact Or.inr (he ▸ hAB)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement

module
public import Theory.SpecificGroups.AlternatingSix.PGLNineFivePairs

/-!
# A₅ overgroups of an actual five-subgroup in PGL₂(9)

A point stabilizer in the fixed A₆ coordinates supplies one A₅. Sylow-five
conjugacy moves its five-subgroup onto the supplied subgroup. This produces
an actual overgroup, without choosing coordinates on the arbitrary source.
-/

public noncomputable section
namespace AlternatingSix.PGLNineFivePairs
open Subgroup
open Atlas.Comparisons.Exceptional GorensteinWalter
local notation "P" => PGL2 Nine.F
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Finite P :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- Every actual five-subgroup is contained in an actual A₅ subgroup. -/
theorem exists_five_overgroup (R : Subgroup P) (hR : Nat.card R = 5) :
    ∃ H : Subgroup P, R ≤ H ∧ Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  let H₀ := MulAction.stabilizer (alternatingGroup (Fin 6)) (0 : Fin 6)
  let f : H₀ →* P := Matrix.ProjectiveSpecialLinearGroup.toPGL.comp
    (psl2NineCoordinatesEquivAlt6.symm.toMonoidHom.comp H₀.subtype)
  have hf : Function.Injective f :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp
      (psl2NineCoordinatesEquivAlt6.symm.injective.comp H₀.subtype_injective)
  let H := f.range
  let eH : H ≃* alternatingGroup (Fin 5) :=
    (MonoidHom.ofInjective hf).symm.trans (SmallIndex.pointEquiv (n := 5) 0)
  have hH : Nat.card H = 60 := by
    rw [Nat.card_congr eH.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  let S : Sylow 5 H := default
  have hS : Nat.card S = 5 := by rw [S.card_eq_multiplicity,hH]; decide +kernel
  let R₀ := (S : Subgroup H).map H.subtype
  have hc₀ : Nat.card R₀ = 5 := (card_map_of_injective H.subtype_injective).trans hS
  have hcP : Nat.card P = 720 := by rw [pgl2_card_formula,Nine.card]; norm_num
  let S₀ : Sylow 5 P := Sylow.ofCard R₀ (by rw [hc₀,hcP]; decide +kernel)
  let S₁ : Sylow 5 P := Sylow.ofCard R (by rw [hR,hcP]; decide +kernel)
  obtain ⟨p,hp⟩ := MulAction.exists_smul_eq P S₀ S₁
  have he : R₀.map (MulAut.conj p).toMonoidHom = R := congrArg Sylow.toSubgroup hp
  refine ⟨H.map (MulAut.conj p).toMonoidHom,?_,?_⟩
  · rw [←he]
    exact map_mono (map_subtype_le _)
  · exact ⟨(H.equivMapOfInjective (MulAut.conj p).toMonoidHom
      (MulAut.conj p).injective).symm.trans eH⟩
end AlternatingSix.PGLNineFivePairs

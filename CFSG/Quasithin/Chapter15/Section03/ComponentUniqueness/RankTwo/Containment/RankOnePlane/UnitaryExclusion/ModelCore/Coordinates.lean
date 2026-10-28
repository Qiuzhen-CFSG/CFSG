module

public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport

/-!
# Aligning a marked PSU₃(4) Sylow subgroup with the actual matrix root

Compose the supplied model equivalence with the proved Hermitian basis change
and a Sylow conjugation. The resulting group equivalence sends the specified
Sylow subgroup onto the range of the projective Hermitian root homomorphism.
The root is Sylow by projection from the actual special-unitary root group.

This common coordinate boundary is available independently to calculations of
the central quotient and of the normalizer action. It supplies an actual
isomorphism and an equality of embedded subgroups, not a group-family tag.

Source: Huppert II.10.4 and II.10.12; Aschbacher--Smith, F.1.3(1), printed
pp.259--260, and the PSU₃(4) inference in 15.3.40, printed p.1138.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open CFSG.Quasithin.ChapterF.Source.Unitary
open scoped Matrix

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion

/-- Arbitrary forms and marked Sylow subgroups admit genuine standard root coordinates. -/
theorem unitary_four_sylow_coordinates
    {H : Type*} [Group H] [Finite H] (hm : ClassicalGroup.IsPSU H 3 4)
    (P : Sylow 2 H) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm 3 F)
      (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
      Nat.card F = 16 ∧ (∀ x, J.conj x = x ^ 4) ∧
      ∃ e : H ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        (P : Subgroup H).map e.toMonoidHom = (hermitianUnipotentPSU J hJ).range := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨f⟩⟩ := hm
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J 2 (by decide) hcard hconj
  let J0 := FormTransport.standardForm J
  let e0 := f.trans (FormTransport.projectiveEquiv J C hC)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J0) :=
    Finite.of_surjective e0 e0.surjective
  obtain ⟨_, _, T, hT, _⟩ := standard_su_borel_data J0 2 (by decide) hcard hconj rfl
  let P0 := T.mapSurjective (suProjection_surjective J0)
  have hP0 : (P0 : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J0)) =
      (hermitianUnipotentPSU J0 rfl).range := by
    change (T : Subgroup J0.specialSubgroup).map (suProjection J0) = _
    rw [hT]
    exact suRoot_map_projection J0 rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J0)
    (P.mapSurjective (f := e0.toMonoidHom) e0.surjective) P0
  let e := e0.trans (MulAut.conj g)
  refine ⟨F, inferInstance, inferInstance, J0, rfl, hcard, hconj, e, ?_⟩
  have he : (P : Subgroup H).map e.toMonoidHom = P0 := by
    change (P : Subgroup H).map ((MulAut.conj g).toMonoidHom.comp e0.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact congrArg Sylow.toSubgroup hg
  exact he.trans hP0

end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion

module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.BorelGeometry
public import Theory.SpecificGroups.SU3.EvenSemilinear.CyclicOuter
public import Theory.SpecificGroups.SU3.BorelTorus.BorelResiduals.Quotients
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.TorusAction

/-!
# Aligning the actual component with the standard unitary Borel

The projective root is Sylow, and its normalizer is the join of the root
and full diagonal torus. Consequently its two-core is the root, and its
quotient by that core is abelian.

An actual isomorphism from `IsPSU` is composed with the proved Hermitian
basis change and Sylow conjugacy. The resulting equivalence takes the
intrinsic image of N_L(S ∩ L) to that standard Borel. The matrix field has
order (2^n)² throughout; the stored conjugation is x ↦ x^(2^n).

Source: Aschbacher--Smith F.1.3(1), printed pp.259--260, and the
rank-one paragraph of 15.3.37, printed p.1135.
-/

public section

open Subgroup Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction.BorelInner.Unitary
open BenderSuzuki.MatrixGroups.HermitianForm
open CFSG.Quasithin.ChapterF.Source
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

theorem standard_borel_facts
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) :
    (∃ P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      (P : Subgroup _) = BorelTorus.projectiveRoot J hJ ∧
      normalizer (P : Set _) = BorelTorus.projectiveBorel J hJ) ∧
    (BorelTorus.projectiveBorel J hJ).pCoreIn 2 = BorelTorus.projectiveRoot J hJ ∧
    IsMulCommutative (BorelTorus.projectiveBorel J hJ ⧸
      pCore 2 (BorelTorus.projectiveBorel J hJ)) := by
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  let P := EvenTwoRank.rootSylow J hJ hn hcard hfixed
  have hP : (P : Subgroup _) = BorelTorus.projectiveRoot J hJ := rfl
  obtain ⟨_, _, _, _, _, _, hgen, hnorm, _⟩ :=
    CFSG.Quasithin.ChapterF.Source.Unitary.standard_projective_matrix_borel
      J n hn hcard hconj hJ
  have hB : normalizer (P : Set _) = BorelTorus.projectiveBorel J hJ :=
    hnorm.trans hgen.symm
  have hcore : (BorelTorus.projectiveBorel J hJ).pCoreIn 2 =
      BorelTorus.projectiveRoot J hJ := by
    rw [← hB]
    exact twoCore_sylow_normalizer P
  refine ⟨⟨P, hP, hB⟩, hcore, ?_⟩
  let : IsMulCommutative (BorelTorus.projectiveTorus J hJ) :=
    inferInstanceAs (IsMulCommutative (hermitianTorusPSU J hJ).range)
  let e := BorelTorus.quotientTorusEquiv (BorelTorus.projectiveBorel J hJ)
    (BorelTorus.projectiveRoot J hJ) (BorelTorus.projectiveTorus J hJ)
    le_sup_right hcore
    (BorelTorus.SemilinearActors.projective_root_disjoint_torus J hJ) rfl
  apply IsMulCommutative.of_comm
  intro x y
  apply e.injective
  rw [map_mul, map_mul]
  exact mul_comm' _ _

theorem exists_standard_borel_equiv
    {G : Type*} [Group G] [Finite G] {L S : Subgroup G}
    {n : ℕ} (hn : 0 < n) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n))
    (T : Sylow 2 L) (hT : (T : Subgroup L).map L.subtype = S ⊓ L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm 3 F)
      (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
      Nat.card F = (2 ^ n) ^ 2 ∧ (∀ x, J.conj x = x ^ (2 ^ n)) ∧
      ∃ e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        ((borel L S).subgroupOf L).map e.toMonoidHom =
          BorelTorus.projectiveBorel J hJ := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨f⟩⟩ := hm
  obtain ⟨C, hC⟩ := CFSG.Quasithin.ChapterF.Source.Unitary.FormTransport.exists_standard_basis
    J n hn hcard hconj
  let J0 := CFSG.Quasithin.ChapterF.Source.Unitary.FormTransport.standardForm J
  have hJ0 : J0.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let e0 : L ≃* ProjectiveSpecialUnitaryMatrixGroup J0 :=
    f.trans (CFSG.Quasithin.ChapterF.Source.Unitary.FormTransport.projectiveEquiv J C hC)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J0) := Finite.of_surjective e0 e0.surjective
  obtain ⟨⟨P, hP, hB⟩, _⟩ := standard_borel_facts J0 hJ0 hn hcard hconj
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J0)
    (T.mapSurjective (f := e0.toMonoidHom) e0.surjective) P
  let e := e0.trans (MulAut.conj g)
  have he : (T : Subgroup L).map e.toMonoidHom = P := by
    change (T : Subgroup L).map ((MulAut.conj g).toMonoidHom.comp e0.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact congrArg Sylow.toSubgroup hg
  have hS : (S ⊓ L).subgroupOf L = (T : Subgroup L) := by
    rw [← hT]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hnB : (borel L S).subgroupOf L = normalizer (T : Set L) := by
    change (borel L S).subgroupOf L = normalizer ((T : Subgroup L) : Set L)
    rw [← hS, ← subgroupOf_normalizer_eq inf_le_right]
    ext x
    exact and_iff_right x.property
  refine ⟨F, inferInstance, inferInstance, J0, hJ0, hcard, hconj, e, ?_⟩
  rw [hnB]
  change (normalizer ((T : Subgroup L) : Set L)).map e.toMonoidHom = _
  rw [map_equiv_normalizer_eq, he]
  exact hB

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction.BorelInner.Unitary

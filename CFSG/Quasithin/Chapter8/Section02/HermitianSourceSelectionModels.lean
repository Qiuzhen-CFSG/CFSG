module
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Selection.Sources
public import Theory.GroupTheory.SpecificGroups.OddDihedralTwoNormalizer
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.SpecificGroups.Suzuki.RootCenter

/-!
# Concrete model inputs for Hermitian source selection

The three model clauses used in 8.2.2 are proved for their literal carriers.
An odd-dihedral Sylow has order two and is self-normalizing. In binary PSL₂
and Suzuki groups, the normal root subgroup is the unique ambient Sylow
inside the named Borel. Its known normalizer and center order therefore
apply to any Sylow specified by selection.

This discharges SelectionModelSources, not the earlier E.2 witness and
module clauses. NonFFSourceNonMathieuHermitianSelectionModels applies the
result to the original chosen orbit and half-field tensor.
Source: Aschbacher–Smith, 8.2.2(5–6), printed pp.714–715; the concrete
rank-one calculations are the imported PSL₂ Borel geometry and
Huppert–Blackburn III, XI.3.1, 3.3, 3.10 for the Suzuki root group.
-/

public noncomputable section
open scoped IsMulCommutative MatrixGroups
open Subgroup BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Offenders.Parabolic.Construction

private theorem normal_two_subgroup_le_sylow
    {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : A ≤ B) [(A.subgroupOf B).Normal] (hA : IsPGroup 2 A)
    (S : Sylow 2 G) (hSB : (S : Subgroup G) ≤ B) : A ≤ S := by
  have hp : IsPGroup 2 (A.subgroupOf B) := hA.comap_subtype
  have hh := hp.le_sylow_of_normal (S.subtype hSB)
  intro x hx
  exact hh (show (⟨x,hAB hx⟩ : B) ∈ A.subgroupOf B from hx)

private theorem dihedral_model (p a : ℕ) (hp : p.Prime) (ho : Odd p) (_ha : 0 < a)
    (S : Sylow 2 (DihedralGroup (p ^ a))) :
    normalizer (S : Set (DihedralGroup (p ^ a))) = (S : Subgroup _) ∧
      Nat.card (center S) = 2 := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hn : Odd (p ^ a) := ho.pow
  have hd : 2 ∣ Nat.card (DihedralGroup (p ^ a)) := by
    rw [DihedralGroup.nat_card]
    exact dvd_mul_right _ _
  have hne := S.ne_bot_of_dvd_card hd
  have hc : Nat.card S = 2 := by
    have hdiv : Nat.card S ∣ 2 * p ^ a := by
      rw [← DihedralGroup.nat_card]
      exact (S : Subgroup (DihedralGroup (p ^ a))).card_subgroup_dvd_card
    obtain ⟨b,hb⟩ := S.isPGroup'.exists_card_eq
    have hcop : Nat.Coprime (Nat.card S) (p ^ a) := by
      rw [hb]
      exact hn.coprime_two_left.pow_left b
    have hle := Nat.le_of_dvd (by decide : 0 < 2) (hcop.dvd_of_dvd_mul_right hdiv)
    have hlt := (S : Subgroup (DihedralGroup (p ^ a))).one_lt_card_iff_ne_bot.mpr hne
    omega
  refine ⟨odd_dihedral_two_subgroup_normalizer (p ^ a) hn (MulEquiv.refl _)
    (S : Subgroup _) S.isPGroup' hne, ?_⟩
  let : IsCyclic S := isCyclic_of_prime_card hc
  rw [center_eq_top, card_top, hc]

private theorem psl2_model (k : ℕ) (hk : 1 < k)
    (S : Sylow 2 (PSL2 (BinaryGaloisField k)))
    (hS : (S : Subgroup _) ≤ PBorel (BinaryGaloisField k)) :
    PBorel (BinaryGaloisField k) = normalizer (S : Set _) ∧
      Nat.card (center S) = 2 ^ k := by
  let F := BinaryGaloisField k
  let P := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.standardSylow F
  have hP := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.coe_standardSylow F
  have hSB : (S : Subgroup _) ≤ Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F := by
    rwa [Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel_eq_PBorel]
  have hp : IsPGroup 2 (Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F) :=
    hP ▸ P.isPGroup'
  have hle := normal_two_subgroup_le_sylow
    (show Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F ≤
      Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F from le_sup_left) hp S hSB
  have he : (S : Subgroup (PSL2 F)) = Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F := by
    have he' := P.is_maximal' S.isPGroup' (hP.symm ▸ hle)
    exact he'.trans hP
  refine ⟨?_, ?_⟩
  · rw [show (S : Set (PSL2 F)) =
        (Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F : Set (PSL2 F)) from
      congrArg (fun A : Subgroup (PSL2 F) => (A : Set (PSL2 F))) he,
      Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.normalizer_kernel,
      Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel_eq_PBorel]
  · rw [Nat.card_congr (centerCongr (MulEquiv.subgroupCongr he)).toEquiv,
      center_eq_top (G := Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F),
      card_top, Matrix.ProjectiveSpecialLinearGroup.OddBorel.card_kernel]
    exact GaloisField.card 2 k (by omega)

private theorem suzuki_model (m : ℕ) (hm : 0 < m)
    (S : Sylow 2 (SuzukiMatrixGroup m))
    (hS : (S : Subgroup _) ≤ SuzukiBorelSubgroup m) :
    SuzukiBorelSubgroup m = normalizer (S : Set _) ∧
      Nat.card (center S) = 2 ^ (2 * m + 1) := by
  obtain ⟨P,hP⟩ := suzukiRootSubgroup_isSylow m hm
  let : ((SuzukiRootSubgroup m).subgroupOf (SuzukiBorelSubgroup m)).Normal :=
    suzukiRootSubgroup_normal_in_borel m
  have hPB : SuzukiRootSubgroup m ≤ SuzukiBorelSubgroup m := by
    rw [suzukiBorelSubgroup_eq_sup]
    exact le_sup_left
  have hp : IsPGroup 2 (SuzukiRootSubgroup m) := hP ▸ P.isPGroup'
  have hle := normal_two_subgroup_le_sylow hPB hp S hS
  have he : (S : Subgroup _) = SuzukiRootSubgroup m :=
    (P.is_maximal' S.isPGroup' (hP.symm ▸ hle)).trans hP
  refine ⟨?_, ?_⟩
  · rw [show (S : Set (SuzukiMatrixGroup m)) = (SuzukiRootSubgroup m : Set _) from
      congrArg (fun A : Subgroup (SuzukiMatrixGroup m) => (A : Set (SuzukiMatrixGroup m))) he,
      suzukiRootSubgroup_normalizer m hm]
  · exact (Nat.card_congr (centerCongr (MulEquiv.subgroupCongr he)).toEquiv).trans
      (suzukiRootSubgroup_center_card m hm)

/-- The actual dihedral, binary PSL₂ and Suzuki normalizer/center inputs
required by source selection, with no additional model premise. -/
theorem selectionModelSources : SelectionModelSources :=
  ⟨dihedral_model, psl2_model, suzuki_model⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource

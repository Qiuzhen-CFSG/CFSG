module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EnlargementAction
public import Theory.GroupTheory.PCoreKernelRange
public import Theory.GroupTheory.SpecificGroups.DihedralFiveAutomorphisms
public import Theory.SpecificGroups.SymmetricFive.FiveNormalizerSuzuki

/-!
# The dihedral-to-Suzuki alternative in DGS 6.1

The action image contains the ten inner automorphisms of the marked D₁₀
quotient and has order at most twenty. An image of order ten is inner,
which forces equality with the original starred endpoint. Otherwise the
image has order twenty and trivial two-core, and the existing faithful
five-point recognition identifies it with the concrete Suzuki matrix
model Sz(2). The equivalence retains the literal action on representatives.

This proves the dihedral branch of DGS, *Groups and Graphs* (1985),
6.1 and its remark, pp.118--119. It does not discard the exceptional
strict enlargement or assume that the ambient completion is finite.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P B : Subgroup G}

private theorem dihedral_center (d : LocalRankOneData P B)
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* DihedralGroup 5) :
    center (d.Pstar ⧸ pCore 2 d.Pstar) = ⊥ := by
  apply bot_unique
  intro x hx
  have he : e x ∈ center (DihedralGroup 5) := (centerCongr e ⟨x,hx⟩).property
  rw [DihedralGroup.five_center_eq_bot,mem_bot] at he
  exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))

/-- A strict dihedral enlargement has two-core quotient of order twenty. -/
theorem localEnlargement_dihedral_strict_card (d : LocalRankOneData P B)
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* DihedralGroup 5)
    (hne : localEnlargement d ≠ d.Pstar) :
    Nat.card (localEnlargement d ⧸ pCore 2 (localEnlargement d)) = 20 := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  let : Finite (localEnlargement d) := Finite.of_injective
    (inclusion (localEnlargement_le d)) (inclusion_injective _)
  let A := (localStarCoreAction d).range
  let I := MulAut.innerSubgroup (d.Pstar ⧸ pCore 2 d.Pstar)
  have hz := dihedral_center d e
  have hi : I ≤ A := by
    rintro a ⟨x,rfl⟩
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 d.Pstar) x
    exact ⟨inclusion le_sup_left l,localStarCoreAction_on_star d l⟩
  have hI : Nat.card I = 10 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (Theory.GroupTheory.conj_injective_of_center_eq_bot hz)).toEquiv,
      Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  have hbound : Nat.card A ≤ 20 := by
    exact (Nat.card_le_card_of_injective
      (fun a : A => MulAut.congr e a.val)
      ((MulAut.congr e).injective.comp A.subtype_injective)).trans
        DihedralGroup.card_mulAut_five_le_twenty
  have hd : 10 ∣ Nat.card A := hI ▸ card_dvd_of_le hi
  have hc : Nat.card A = 20 := by
    have hp : 0 < Nat.card A := Nat.card_pos
    have hnot : Nat.card A ≠ 10 := by
      intro he
      have hAI : A = I := (eq_of_le_of_card_ge hi (by omega)).symm
      exact hne (localEnlargement_eq_star_of_inner d hz hAI.le)
    omega
  exact (Nat.card_congr (localStarCoreQuotientEquiv d hz).toEquiv).trans hc

/-- The literal strict action image is the concrete small Suzuki group. -/
def localDihedralStrictActionEquiv (d : LocalRankOneData P B)
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* DihedralGroup 5)
    (hne : localEnlargement d ≠ d.Pstar) :
    (localStarCoreAction d).range ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  have hc : Nat.card (localStarCoreAction d).range = 20 :=
    (Nat.card_congr (localStarCoreQuotientEquiv d (dihedral_center d e)).toEquiv).symm.trans
      (localEnlargement_dihedral_strict_card d e hne)
  exact Classical.choice
    (Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.equiv_suzuki_of_card_twenty
      hc (pCore_range_eq_bot_of_ker_eq_pCore 2 _ (localStarCoreAction_kernel d (dihedral_center d e))))

/-- The strict enlargement quotient is Sz(2), through its original quotient action. -/
def localDihedralStrictQuotient (d : LocalRankOneData P B)
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* DihedralGroup 5)
    (hne : localEnlargement d ≠ d.Pstar) :
    (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  (localStarCoreQuotientEquiv d (dihedral_center d e)).trans
    (localDihedralStrictActionEquiv d e hne)

/-- The small Suzuki marking factors through the actual conjugation action. -/
theorem localDihedralStrictQuotient_mk (d : LocalRankOneData P B)
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* DihedralGroup 5)
    (hne : localEnlargement d ≠ d.Pstar) (x : localEnlargement d) :
    localDihedralStrictQuotient d e hne (QuotientGroup.mk' _ x) =
      localDihedralStrictActionEquiv d e hne
        ⟨localStarCoreAction d x, ⟨x,rfl⟩⟩ := by
  change localDihedralStrictActionEquiv d e hne
    (localStarCoreQuotientEquiv d (dihedral_center d e) (QuotientGroup.mk' _ x)) = _
  congr 1
  exact Subtype.ext (localStarCoreQuotientEquiv_mk d (dihedral_center d e) x)

/-- The full source 6.1 dichotomy for a marked dihedral starred quotient. -/
theorem localEnlargement_dihedral_alternatives (d : LocalRankOneData P B)
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* DihedralGroup 5) :
    localEnlargement d = d.Pstar ∨
      Nonempty ((localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  by_cases he : localEnlargement d = d.Pstar
  · exact Or.inl he
  · exact Or.inr ⟨localDihedralStrictQuotient d e he⟩
end CFSG.Quasithin.ChapterF.Source.DGS85

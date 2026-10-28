module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreLieModels
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.LinearThree.ExtensionAmalgam

/-!
# Linear-three original extensions on the Cartan prime pair

The actual zero-core source pair has a solvable left endpoint and a
nonsolvable right endpoint. For each automorphism overgroup of PSL₃(F),
its two embedded root-plane normalizers are therefore excluded. Above
field two both contain the nonsolvable original rank-one local. At field
two the new compatible restriction identifies the entire extension triple
with the ordinary flag triple, where the existing source exclusion applies.

This argument handles either orientation on the same selected R. It keeps
the original sourceS, full overlap and projective scalar quotient; no
ambient Sylow equality or actual-H-component premise is used. Broad DGS
recognition, the other extension families, quintic solvability and final
Cartan normalization remain obligations of the original source assembly.
Source: Aschbacher–Smith F.1.12, pp.263–264, and 5.2.2, pp.647–648.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]

/-- Every actual linear-three root-normalizer extension is excluded on the
original prime pair, in either orientation and with its entire overlap. -/
theorem LocalData.zeroCore_not_linear_extension_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (E : Subgroup (MulAut PSL(3,F))) (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (LieModels.LinearThree.ExtensionAmalgam.amalgam F E hE)) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
        (LieModels.LinearThree.ExtensionAmalgam.amalgam F E hE).reverse) := by
  by_cases hm1 : m = 1
  · have htwo : Nat.card F = 2 := by simpa [hm1] using hF
    let e := (LieModels.LinearThree.ExtensionAmalgam.binaryIso F E hE htwo).symm
    have hn := d.zeroCore_not_linear_parabolic h hH c hd hz hm hF
    constructor
    · rintro ⟨f⟩
      exact hn.1 ⟨f.trans e.toParabolicEquiv⟩
    · rintro ⟨f⟩
      exact hn.2 ⟨f.trans e.reverse.toParabolicEquiv⟩
  · have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < m)
    let := (d.zeroCore_mixed_solvability h hH c hd hz).1
    constructor
    · rintro ⟨f⟩
      exact LieModels.LinearThree.ExtensionAmalgam.endpoint_not_solvable F E hE hlarge true
        (Group.isSolvable_of_surjective (f := f.left.toMonoidHom) f.left.surjective)
    · rintro ⟨f⟩
      exact LieModels.LinearThree.ExtensionAmalgam.endpoint_not_solvable F E hE hlarge false
        (Group.isSolvable_of_surjective (f := f.left.toMonoidHom) f.left.surjective)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

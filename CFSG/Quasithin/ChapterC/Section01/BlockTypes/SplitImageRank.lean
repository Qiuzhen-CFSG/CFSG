module
public import Theory.GroupTheory.QuasithinBasic
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.PSL2.RootTwoRank
public import Mathlib.GroupTheory.Complement
/-!
# Two-rank surviving a split natural block

A homomorphism whose kernel lies in the two-core of a split natural block
is faithful on its actual complement. The root subgroup of the resulting
PSL₂ copy retains rank equal to the field degree.

Source: Aschbacher–Smith, 2.4.11, printed p.531.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
variable {L Y : Type*} [Group L] [Finite L] [Group Y] [Finite Y]

theorem IsL2EvenBlock.two_rank_ge_of_split_map
    {n : ℕ} (hL : IsL2EvenBlock L n)
    (hsp : ∃ A : Subgroup L, (pCore 2 L).IsComplement' A)
    (f : L →* Y) (hk : f.ker ≤ pCore 2 L) : n ≤ primeRank 2 Y := by
  obtain ⟨A,hA⟩ := hsp
  obtain ⟨_,_,F,_,_,hF,_,ρ,⟨m⟩,_⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e : A ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    hA.symm.QuotientMulEquiv.symm.trans (m.quotientIso.trans (Theory.PSL2.sl2QuotientEquiv F))
  let g : A →* Y := f.comp A.subtype
  have hi : Function.Injective g := by
    apply g.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro a ha
    exact Subtype.ext (disjoint_def.mp hA.disjoint (hk ha) a.property)
  have hr : n ≤ primeRank 2 A := by
    rw [Theory.GroupTheory.primeRank_equiv 2 e]
    exact Theory.PSL2.root_two_rank_ge F hF
  exact hr.trans (Theory.GroupTheory.primeRank_le_of_injective 2 g hi)
end CFSG.Quasithin.ChapterC

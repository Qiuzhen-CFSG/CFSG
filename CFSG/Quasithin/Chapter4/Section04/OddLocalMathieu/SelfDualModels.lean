module
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.Models
public import Theory.Mathieu.M22.CoverSelfDualDegree

/-!
# Removing binary G₂ and triality from the odd-local comparison

The same full quasisimple Mathieu cover embeds in the selected simple
section. Both degree-eight isometry models are impossible by the paired
character-orbit bound. This leaves the general Ree F₄ family, retaining an
actual model equivalence and imposing no new source premise.

Hall.OddNormalizer.OddLocalRee applies the result to the original residual
image and preserves componenthood in the whole actor's common fixed group.
Source: Aschbacher--Smith 4.4.3, printed p.623.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
open Triality.Standard
/-- The actual quasisimple Mathieu cover excludes binary G₂ and triality
from the remaining source list, leaving only the Ree family. -/
theorem rank_two_mathieu_cover_is_ree {S : Type*} [Group S] [Finite S]
    (hm : RemainingOddLocalRankTwoModel S) (B : Subgroup S) [IsQuasisimple B]
    (eB : (B ⧸ center B) ≃* M22) :
    ∃ m, 1 ≤ m ∧ Nonempty (S ≃* ReeF4.Model m) := by
  rcases hm with ⟨n,hn,F,_,_,hF,⟨e⟩⟩ | ⟨n,hn,ht⟩ | hr
  · let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact (M22CentralCover.no_embedding_g2 eB (e.toMonoidHom.comp B.subtype)
      (e.injective.comp B.subtype_injective)).elim
  · obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff S n (by omega)).mp ht
    exact (M22CentralCover.no_embedding_binary_triality eB n (by omega)
      (e.toMonoidHom.comp B.subtype) (e.injective.comp B.subtype_injective)).elim
  · exact hr
end CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu

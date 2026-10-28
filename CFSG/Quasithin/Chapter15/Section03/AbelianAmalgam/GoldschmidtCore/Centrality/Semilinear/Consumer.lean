module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.SourceReduction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp

/-!
# Connecting the constructed module to the independent exclusion proof

Unpack the source reduction's proved output and instantiate pushing-up
with exactly its character kernel, intrinsic module, marked quotient,
Sylow subgroup and first local intersection. Both nested core maps and
the ambient conjugate agree literally with the consumer's conventions.
This discharges every module and ambient premise of that independent
proof, retaining its universal Chapter C input and the parent's genuine
earlier Baumann, normalizer-control and maximal-two-local conclusions.

Source: the repaired terminal argument for Aschbacher–Smith 15.3.68(2),
printed pp.1154–1155, using the C.1.37 implication specified by PushingUp.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The proved output contract discharges every module and ambient premise
of the independent pushing-up consumer. Its universal Chapter C source
implication and earlier Baumann/control facts remain with the parent. -/
theorem BadCharacterReduction.excluded {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (hsource : PushingUp.DoubledNaturalSource κ)
    (H B G₁ S V U M X : Subgroup G) (hHB : H ≤ normalizer (B : Set G))
    (s : G) (h : BadCharacterReduction H B G₁ S V U M hHB s)
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hXH : X ≤ H) (hX : IsPPerfect 2 X) (hXM : ¬ X ≤ M)
    (hBR : ChapterB.baumann S ≤ centralizer (V : Set G))
    (hRS : centralizer (V : Set G) ≤ S)
    (hcontrol : (ChapterB.baumann S).characteristicNormalizerClosure ≤ M)
    (hM : IsMaximalTwoLocal M) : False := by
  let K := characterKernel H B hHB
  let P := (G₁ ⊓ K).subgroupOf K
  let Uk := U.subgroupOf K
  obtain ⟨_hinter,_hnBH,_hcoreBH,_hSylBH,_hcoreK,_hlocal,Sk,_hSk,hSkP,hP,_hi,hR,
    hn,hUk,hUcore,hmap,hC,_m,_hmark,eK,_heK,eU,heU,hUsR,hcomm,_hA,_hne,hMA⟩ := h
  let := hn
  have hχ : IsPGroup 2 (quotientAction H B hHB).range :=
    (IsPGroup.of_card ((ExternalQuotient.aut_card B hc).trans (pow_one 2).symm)).to_subgroup _
  exact PushingUp.bad_character_excluded hG hsource M H K S X (otherLine U s) P Uk Sk
    (quotientAction H B hHB) hχ rfl hXH hX hXM hP hSkP eK eU hUk hUcore hC heU
    (hR.symm ▸ hBR) (hR.symm ▸ hRS) hcontrol (s⁻¹)
    (by rw [hmap]; rfl)
    (hR.symm ▸ hUsR) (by rw [hmap]; exact hcomm) hM (by rw [hmap]; exact hMA)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear

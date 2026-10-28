module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OvergroupLift

/-!
# Lifting the binary smaller overgroups

The full preimage of a subgroup of H/O₂(H) has the same intrinsic two-core
quotient as that subgroup. We reuse the checked full-preimage construction
from the Chapter 13 leaf and apply it to the actual smaller-overgroup family.
A nonempty family generating the star quotient therefore generates H after
lifting: its preimages contain O₂(H), so the kernel is retained.

`smallComponentOvergroups` is the intrinsic matrix-generation interface.
Every quotient in this family is literally Q/O₂(Q). The degree-four and
degree-five constructions are still required; this module only proves the
lifting step.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1145, the L₄(2), L₅(2) generation paragraph.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration
variable {G : Type*} [Group G]

/-- Intrinsic smaller overgroups of a specified component parabolic. -/
def smallComponentOvergroups (K P : Subgroup G) : Set (Subgroup G) :=
  {Q | P ≤ Q ∧ Q ≤ K ∧ SmallQuotient Q}

/-- Smaller overgroups in the literal star quotient. -/
def smallStarOvergroups (H Y T : Subgroup G) : Set (Subgroup (H ⧸ pCore 2 H)) :=
  {P | starImage H Y ⊔ starImage H T ≤ P ∧ SmallQuotient P}

private lemma star_sup (H A B : Subgroup G) (hA : A ≤ H) (hB : B ≤ H) :
    starImage H (A ⊔ B) = starImage H A ⊔ starImage H B := by
  simp only [starImage, subgroupOf_sup hA hB, Subgroup.map_sup]

private lemma lift_top (H : Subgroup G) : liftStar H ⊤ = H := by
  simp only [liftStar, comap_top]
  exact le_antisymm (map_subtype_le _) (fun x hx => ⟨⟨x, hx⟩, mem_top _, rfl⟩)

variable [Finite G]

lemma lift_mem_smallOvergroups {H Y T : Subgroup G} (hYH : Y ≤ H) (hTH : T ≤ H)
    {P : Subgroup (H ⧸ pCore 2 H)} (hP : P ∈ smallStarOvergroups H Y T) :
    liftStar H P ∈ smallOvergroups H Y T := by
  refine ⟨(le_liftStar_iff H (Y ⊔ T) (sup_le hYH hTH) P).mpr ?_,
    liftStar_le H P, ?_⟩
  · change starImage H (Y ⊔ T) ≤ P
    rw [star_sup H Y T hYH hTH]
    exact hP.1
  · have hq := hP.2
    change _ ∨ _ at hq
    rcases hq with hq | hq
    · obtain ⟨e⟩ := hq
      exact Or.inl ⟨(liftStarQuotientEquiv H P).trans e⟩
    · obtain ⟨e⟩ := hq
      exact Or.inr ⟨(liftStarQuotientEquiv H P).trans e⟩

lemma generation_of_star_generation {H Y T : Subgroup G}
    (hYH : Y ≤ H) (hTH : T ≤ H)
    (hne : (smallStarOvergroups H Y T).Nonempty)
    (hgen : (⊤ : Subgroup (H ⧸ pCore 2 H)) ≤ sSup (smallStarOvergroups H Y T)) :
    H ≤ sSup (smallOvergroups H Y T) := by
  let W := sSup (smallOvergroups H Y T)
  have hWH : W ≤ H := sSup_le (fun _ h => h.2.1)
  have hPW : ∀ P ∈ smallStarOvergroups H Y T, liftStar H P ≤ W :=
    fun P hP => le_sSup (lift_mem_smallOvergroups hYH hTH hP)
  have hQW : localTwoCore H ≤ W := by
    obtain ⟨P, hP⟩ := hne
    exact (twoCore_le_liftStar H P).trans (hPW P hP)
  have hstar : (⊤ : Subgroup (H ⧸ pCore 2 H)) ≤ starImage H W := by
    apply hgen.trans
    apply sSup_le
    intro P hP
    have hm := map_mono (f := QuotientGroup.mk' (pCore 2 H))
      (comap_mono (f := H.subtype) (hPW P hP))
    change starImage H (liftStar H P) ≤ starImage H W at hm
    simpa only [show starImage H (liftStar H P) = P from starImage_liftStar H P] using hm
  have hlift := (liftStar_le_iff H ⊤ (starImage H W)).mpr hstar
  rw [lift_top] at hlift
  have he : liftStar H (starImage H W) = W :=
    liftStar_starImage_of_core_le H W hWH hQW
  rw [he] at hlift
  exact hlift
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration

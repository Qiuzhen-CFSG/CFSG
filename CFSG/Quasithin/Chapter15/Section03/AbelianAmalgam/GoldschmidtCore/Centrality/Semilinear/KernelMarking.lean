module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ExternalQuotient
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.Marking

/-!
# The compatible quotient and actual index-seven intersection

The external quotient K/N≃H/Q is rewritten using the intrinsic two-cores,
with the representative formula unchanged. Since Q lies in G₁, membership
in its quotient image is equivalent to membership in G₁. The same line
parabolic marking from the natural-module argument therefore proves that
the literal intersection G₁∩K is maximal of index seven in K.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the terminal module argument after 15.3.68, printed pp.1154–1155.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
variable {G : Type*} [Group G] [Finite G]

/-- The external quotient identification, expressed with the intrinsic two-cores. -/
noncomputable def kernelCoreQuotientEquiv (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hbad : ∃ q : ambientTwoCore H, ExternalQuotient.coreCharacter H B hHB q ≠ 1) :
    (characterKernel H B hHB ⧸ pCore 2 (characterKernel H B hHB)) ≃* (H ⧸ pCore 2 H) := by
  let K := characterKernel H B hHB
  have he : pCore 2 K = (ExternalQuotient.kernelIntersection H B hHB).subgroupOf K := by
    change pCore 2 K = (ambientTwoCore H ⊓ characterKernel H B hHB).subgroupOf K
    rw [← ExternalQuotient.kernel_core H B hHB]
    exact (localTwoCore_eq_pCore K).symm
  exact (QuotientGroup.quotientMulEquivOfEq he).trans
    ((ExternalQuotient.kernelQuotientEquiv H B hHB hc hbad).trans
      (QuotientGroup.quotientMulEquivOfEq (localTwoCore_eq_pCore H)))

theorem kernelCoreQuotientEquiv_mk (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hbad : ∃ q : ambientTwoCore H, ExternalQuotient.coreCharacter H B hHB q ≠ 1)
    (k : characterKernel H B hHB) :
    kernelCoreQuotientEquiv H B hHB hc hbad (QuotientGroup.mk' _ k) =
      QuotientGroup.mk' (pCore 2 H) (inclusion (map_subtype_le _) k) := by
  simp only [kernelCoreQuotientEquiv,MulEquiv.trans_apply,QuotientGroup.mk'_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- Pull the same marked line parabolic back to the actual G₁∩K. -/
theorem kernel_marked_parabolic (H B G₁ : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hbad : ∃ q : ambientTwoCore H, ExternalQuotient.coreCharacter H B hHB q ≠ 1)
    (hQG : ambientTwoCore H ≤ G₁)
    (m : (H ⧸ pCore 2 H) ≃* Matrix.PSL3Two.SL)
    (hmark : ((G₁.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).map
      m.toMonoidHom = Matrix.PSL3Two.lineParabolicSL) :
    IsCoatom ((G₁ ⊓ characterKernel H B hHB).subgroupOf (characterKernel H B hHB)) ∧
      (G₁ ⊓ characterKernel H B hHB).relIndex (characterKernel H B hHB) = 7 := by
  apply Recognition.actual_intersection_maximal_index_seven H (characterKernel H B hHB) G₁
    (pCore 2 (characterKernel H B hHB)) (pCore 2 H)
    (kernelCoreQuotientEquiv H B hHB hc hbad) m hmark
  intro k
  rw [kernelCoreQuotientEquiv_mk]
  have hker : (QuotientGroup.mk' (pCore 2 H)).ker ≤ G₁.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro h hh
    exact hQG (mem_map_of_mem H.subtype hh)
  change inclusion (map_subtype_le _) k ∈
    ((G₁.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).comap (QuotientGroup.mk' (pCore 2 H)) ↔ _
  rw [comap_map_eq_self hker]
  rfl

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear

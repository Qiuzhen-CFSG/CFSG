module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.Setup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve

/-!
# The faithful actors in the further enlargement

The action kernel on Y lies in the kernel A on X. Since A has index four
in V and induces an automorphism group of order two on Y, the V-action
on Y has order eight. The centralizing intersection A₁ has index at most
eight, forcing it to be exactly this kernel. E.6.5 also supplies the actual
Sylow subgroup of X fixed pointwise by V.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
variable {G : Type*} [Group G] [Finite G] {M V U A L X Y : Subgroup G}

omit [Finite G] in
/-- The kernel of the full conjugation action is the intrinsic centralizer. -/
theorem conjugation_ker {D Y : Subgroup G} (hn : D ≤ normalizer (Y : Set G)) :
    (Y.normalizerMonoidHom.comp (inclusion hn)).ker =
      (centralizer (Y : Set G)).subgroupOf D := by
  ext d
  change inclusion hn d ∈ Y.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

omit [Finite G] in
/-- The order of the actual action image is the centralizer's relative index. -/
theorem card_actionImage {D Y : Subgroup G} (hn : D ≤ normalizer (Y : Set G)) :
    Nat.card (actionImage D Y) = (centralizer (Y : Set G)).relIndex D := by
  rw [actionImage_eq_range hn, ← index_ker, conjugation_ker]
  rfl

omit [Finite G] in
/-- The whole action image inherits elementary abelianness from the actors. -/
theorem elementary_actionImage {D Y : Subgroup G} [IsElementaryAbelian 2 D]
    (hn : D ≤ normalizer (Y : Set G)) : IsElementaryAbelian 2 (actionImage D Y) := by
  rw [actionImage_eq_range hn]
  exact IsElementaryAbelian.of_surjective _ (MonoidHom.rangeRestrict_surjective _)

/-- The image of V has order eight, derived from the two source kernel indices. -/
theorem EscapeConfiguration.card_actionImage_V [IsElementaryAbelian 2 V]
    {g : G} (c : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) (hm : LinearModelAction A Y) :
    Nat.card (actionImage V Y) = 8 := by
  have hAV : A ≤ V := c.subspace_mem.1
  have hn := hY.normalized_by_V hAV
  have hCA : V ⊓ centralizer (Y : Set G) ≤ A := by
    rw [← c.six.fixed]
    exact inf_le_inf_left V (Subgroup.centralizer_le hY.proper.le)
  have he : centralizer (Y : Set G) ⊓ A = centralizer (Y : Set G) ⊓ V := by
    apply le_antisymm (inf_le_inf_left _ hAV)
    exact le_inf inf_le_left (inf_comm V _ ▸ hCA)
  have hprod := relIndex_inf_mul_relIndex (centralizer (Y : Set G)) A V
  rw [inf_of_le_left hAV, he, inf_relIndex_right,
    ← card_actionImage (hAV.trans hn), hm.order_two] at hprod
  have hidx : A.relIndex V = 4 := by
    rw [relIndex_eq_two_pow_quotient_finrank, ← subgroupCorank_eq_quotient_finrank, c.corank]
    norm_num
  rw [hidx, ← card_actionImage hn] at hprod
  exact hprod.symm

/-- The centralizing intersection is exactly the kernel, not merely a subspace of it. -/
theorem EscapeConfiguration.action_kernel [IsElementaryAbelian 2 V]
    {g : G} (c : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) (hm : LinearModelAction A Y) :
    V ⊓ centralizer (Y : Set G) = intersection A U g := by
  let C := V ⊓ centralizer (Y : Set G)
  have h1C : intersection A U g ≤ C :=
    le_inf (inf_le_left.trans c.subspace_mem.1) (le_centralizer_iff.mp hY.component.1)
  have hC : C.relIndex V = 8 := by
    rw [show C = centralizer (Y : Set G) ⊓ V from inf_comm _ _, inf_relIndex_right,
      ← card_actionImage (hY.normalized_by_V c.subspace_mem.1)]
    exact c.card_actionImage_V hY hm
  have h1 : (intersection A U g).relIndex V ≤ 8 := by
    have hc := intersection_corank_le_three c.hyperplane c.corank g c.conjugator_mem
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hc
    rwa [subgroupCorank_eq_quotient_finrank, ← relIndex_eq_two_pow_quotient_finrank] at hp
  have hp := relIndex_mul_relIndex (intersection A U g) C V h1C inf_le_left
  rw [hC] at hp
  have hn : (intersection A U g).relIndex C ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : (intersection A U g).relIndex C = 1 := by omega
  exact le_antisymm (relIndex_eq_one.mp hidx) h1C

/-- The faithful actor quotient has binary rank three. -/
theorem EscapeConfiguration.intersection_corank [IsElementaryAbelian 2 V]
    {g : G} (c : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) (hm : LinearModelAction A Y) :
    subgroupCorank V (intersection A U g) = 3 := by
  rw [← c.action_kernel hY hm, subgroupCorank, inf_comm V, inf_relIndex_right,
    ← card_actionImage (hY.normalized_by_V c.subspace_mem.1), c.card_actionImage_V hY hm]
  decide

/-- V preserves X and fixes an actual Sylow subgroup of X pointwise. -/
theorem EscapeConfiguration.six_sylow_action
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {g : G} (c : EscapeConfiguration M V U A L X g) :
    V ≤ normalizer (X : Set G) ∧
      ∃ R : Sylow 2 X, (R : Subgroup X).map X.subtype ≤ centralizer (V : Set G) := by
  refine ⟨Components.component_normalized_by_V h c.subspace_mem c.six.component, ?_⟩
  obtain ⟨R, hR⟩ := Components.component_sylow_intersection h c.subspace_mem c.six.component
  exact ⟨R, hR ▸ inf_le_right.trans inf_le_right⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms

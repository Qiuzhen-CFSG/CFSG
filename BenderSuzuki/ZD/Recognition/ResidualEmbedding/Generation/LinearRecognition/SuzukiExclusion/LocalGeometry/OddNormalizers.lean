module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.OddNormalizers.Foundations
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.OddNormalizers.Models
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# Normalizer control for odd centralizer subgroups in the Suzuki case

Let L be the source residual-generated Suzuki subgroup and J = C_G(L).
For every nontrivial Y ≤ J, the proper normalizer N = N_G(Y) has its
literal distinguished circle C containing L. The common distinguished
closure A determines the exponent of the actual Bender model C/Z(C).
The checked model orders exclude PSL₂ and PSU₃ at that exponent, making
the image of L the whole central quotient. Perfectness of C removes the
remaining central supplement. Thus C = L, and relative normality gives
N_G(Y) ≤ N_G(L).

This proves the odd branch of GLS4, Chapter 2, Lemma 14.2(d), and in fact
all of (d), from the original Context alone. Neither oddness nor the
separately authorized embedding of J into L is needed by this source
argument. The distinguished circle and the odd core retain their actual
subgroup and quotient conventions throughout.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Corollary 7.13 and Lemma 14.2(d),
and `refs/KGroup/GLS4/Chapter4.tex`, Lemma 3.9(a).
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

/-- The inclusion of L into the local distinguished circle is onto. The
quotient embedding uses the actual common-exponent Bender recognition. -/
public theorem Context.normalizerCircleEmbedding_surjective (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (hY : Y ≠ ⊥) :
    Function.Surjective (d.normalizerCircleEmbedding Y hYJ) := by
  let L := residualGenerated M z t
  let C := localCircle Z (normalizer (Y : Set G))
  let i := d.normalizerCircleEmbedding Y hYJ
  let q := QuotientGroup.mk' (center C)
  have hi := d.normalizerCircleEmbedding_injective Y hYJ
  obtain ⟨hc, hp, _, _⟩ := d.normalizerCircle_structure Y hYJ hY
  have hsource : IsSimpleBenderGroupAtExponent (2 * m + 1) L :=
    .isSuzuki ⟨m, rfl, ⟨d.model⟩⟩
  have hsimple := hsource.isSimple (by have := d.parameter_pos; omega)
  have hqi : Function.Injective (q.comp i) := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (q.comp i).ker inferInstance with hb | ht
    · exact (q.comp i).ker_eq_bot_iff.mp hb
    · have hzL : z ∈ L := (le_sup_left.trans le_sup_left : zpowers z ≤ L) (mem_zpowers z)
      let zL : L := ⟨z, hzL⟩
      have hzI := IsInvolution.map_of_injective
        (IsInvolution.subtype (d.minimal.disconnected.involutions z d.z_mem) hzL) i hi
      have hodd : Odd (Nat.card q.ker) := by
        rw [QuotientGroup.ker_mk', ← hc]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      have hn := (involution_map_of_odd_kernel q hodd hzI).ne_one
      have hzker : zL ∈ (q.comp i).ker := by rw [ht]; exact mem_top _
      exact (hn hzker).elim
  have hs0 := suzuki_surjective_of_bender_atExponent d.parameter_pos
    (d.normalizerCircle_model_atExponent Y hYJ hY)
    ((q.comp i).comp d.model.symm.toMonoidHom) (hqi.comp d.model.symm.injective)
  have hs : Function.Surjective (q.comp i) := by
    intro x
    obtain ⟨y, hy⟩ := hs0 x
    exact ⟨d.model.symm y, hy⟩
  have hmap : i.range.map q = ⊤ := by
    rw [← MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hs]
  let : Group.IsPerfect C := ⟨hp⟩
  have hr := perfect_le_of_map_le_of_central_kernel q
    (by rw [QuotientGroup.ker_mk']) (⊤ : Subgroup C) i.range
    (by rw [hmap]; exact le_top)
  exact MonoidHom.range_eq_top.mp (top_le_iff.mp hr)

/-- The literal ambient distinguished closure of N_G(Y) is L. -/
public theorem Context.normalizerCircle_eq_residual (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (hY : Y ≠ ⊥) :
    localCircleIn Z (normalizer (Y : Set G)) = residualGenerated M z t := by
  apply le_antisymm _ (d.residual_le_normalizerCircle Y hYJ)
  rintro x ⟨v, hv, rfl⟩
  obtain ⟨a, ha⟩ := d.normalizerCircleEmbedding_surjective Y hYJ hY ⟨v, hv⟩
  have he := congrArg (localCircleHom Z (normalizer (Y : Set G))) ha
  change (a : G) = (v : G) at he
  change (v : G) ∈ residualGenerated M z t
  rw [← he]
  exact a.property

/-- GLS4, Chapter 2, Lemma 14.2(d). The source local-recognition argument
in fact works for every nontrivial subgroup of J. -/
public theorem Context.normalizer_control_of_le_centralizer (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (hY : Y ≠ ⊥) :
    normalizer (Y : Set G) ≤ normalizer (residualGenerated M z t : Set G) := by
  rw [← d.normalizerCircle_eq_residual Y hYJ hY, localCircleIn_eq_closure]
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  exact subset_closure ⟨d.minimal.disconnected.invariant g x hx.1,
    (normalizer (Y : Set G)).mul_mem
      ((normalizer (Y : Set G)).mul_mem hg hx.2)
      ((normalizer (Y : Set G)).inv_mem hg)⟩

/-- The odd-order branch of Lemma 14.2(d), with no local-geometry or
recognition premise. The embedding of J into L is not needed for this branch. -/
public theorem Context.normalizer_control_odd (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hY : Y ≠ ⊥) (_hodd : Odd (Nat.card Y)) :
    normalizer (Y : Set G) ≤ normalizer (residualGenerated M z t : Set G) :=
  d.normalizer_control_of_le_centralizer Y hYJ hY

end BenderSuzuki.ZD.SuzukiExclusion

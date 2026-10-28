module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixAutomizer
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedHyperplanes
public import Theory.Representation.HexacodeAction.SmallFixedSpace
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.MaximalAction

/-!
# The original contained 12.7.10(2) rank parameters

The full automizer calculation identifies every small-corank local action
with an actual hexacode actor. A nontrivial actor fixing four dimensions
fixes a full-weight word in that same subspace, contradicting escape of
its centralizer. E.6.12 then excludes corank two. No transvections and an
even involution give the exact local parameter two, hence s(G,U)=2.

All subgroups, the chosen action and the point t remain the original ones.
Source: Aschbacher–Smith, 12.7.10(1–2), printed pp.842–843; E.6.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterE.Section06 ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem chart_subspace_rank (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (W : Subgroup G) (hWU : W ≤ U) :
    let c := tripleSixPointCoordinates D a
    let Q := AddSubgroup.toZModSubmodule 2
      (Subgroup.toAddSubgroup' ((W.subgroupOf U).map c.toMonoidHom))
    Module.finrank (ZMod 2) Q + subgroupCorank U W = 6 := by
  let := D.elementary
  dsimp only
  let c := tripleSixPointCoordinates D a
  let Q := AddSubgroup.toZModSubmodule 2
    (Subgroup.toAddSubgroup' ((W.subgroupOf U).map c.toMonoidHom))
  have hcQ : Nat.card Q = Nat.card W := by
    change Nat.card ((W.subgroupOf U).map c.toMonoidHom) = Nat.card W
    rw [card_map_of_injective c.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hWU).toEquiv
  have hcU : Nat.card U = 64 := (Nat.card_congr c.toEquiv).trans hexacode_card
  have hcount : Nat.card W * W.relIndex U = Nat.card U := by
    simpa only [relIndex_bot_left] using relIndex_mul_relIndex (⊥ : Subgroup G) W U bot_le hWU
  rw [← hcQ, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    relIndex_eq_two_pow_quotient_finrank, ← subgroupCorank_eq_quotient_finrank,
    ← pow_add, hcU] at hcount
  exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hcount

private theorem localCentralizer_eq_of_small_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (W : Subgroup G) (hWU : W ≤ U) (hW : W ≠ ⊥)
    (hcor : subgroupCorank U W ≤ 2)
    (hescape : ¬ centralizer (W : Set G) ≤ normalizer (K : Set G)) :
    normalizer (K : Set G) ⊓ centralizer (W : Set G) =
      normalizer (K : Set G) ⊓ centralizer (U : Set G) := by
  let := D.elementary
  have hE := original_chosen_hypothesisE61_at h structural D
  obtain ⟨f, hf, _, _, heq⟩ := original_tripleSix_full_automizer h structural D a
  let c := tripleSixPointCoordinates D a
  let Q := AddSubgroup.toZModSubmodule 2
    (Subgroup.toAddSubgroup' ((W.subgroupOf U).map c.toMonoidHom))
  have hdim : 4 ≤ Module.finrank (ZMod 2) Q := by
    have hh := chart_subspace_rank D a W hWU
    change Module.finrank (ZMod 2) Q + subgroupCorank U W = 6 at hh
    omega
  have hbot : inducedAutomizer U (normalizer (K : Set G) ⊓ centralizer (W : Set G)) = ⊥ := by
    apply bot_unique
    intro b hb
    change b = 1
    by_contra hbne
    have hfb : f b ≠ 1 := fun hh => hbne (hf (hh.trans f.map_one.symm))
    have hfix : ∀ w ∈ Q, Hexacode.action (f b) w = w := by
      intro w hw
      change Multiplicative.ofAdd w ∈ (W.subgroupOf U).map c.toMonoidHom at hw
      obtain ⟨u, hu, rfl⟩ := hw
      have hbu : b.val u = u := by
        obtain ⟨n, hn, rfl⟩ := hb
        apply Subtype.ext
        change (n : G) * (u : G) * (n : G)⁻¹ = u
        have hc : (u : G) * (n : G) = (n : G) * (u : G) :=
          (mem_centralizer_iff.mp hn.2) u hu
        rw [← hc, mul_inv_cancel_right]
      exact (heq b u).symm.trans (congrArg (fun z => (c z).toAdd) hbu)
    obtain ⟨w, hw, hweight⟩ := Hexacode.full_weight_mem_of_large_fixed_subspace
      (f b) hfb Q hdim hfix
    change Multiplicative.ofAdd w ∈ (W.subgroupOf U).map c.toMonoidHom at hw
    obtain ⟨u, hu, hcu⟩ := hw
    change (u : G) ∈ W at hu
    change c u = Multiplicative.ofAdd w at hcu
    have hweight' : hammingNorm (c u).toAdd.val = 6 := by
      rw [hcu]
      exact hweight
    exact hescape ((centralizer_le (Set.singleton_subset_iff.mpr hu)).trans
      (original_tripleSix_full_weight_centralizer_le D a t ht heven contained u hweight'))
  apply le_antisymm
  · exact le_inf inf_le_left ((inducedAutomizer_eq_bot_iff
      (hE.localCentralizer_le_normalizer hW hWU)).mp hbot)
  · exact inf_le_inf_left _ (centralizer_le hWU)

/-- The genuine original corank bound in the contained-centralizer branch. -/
theorem original_tripleSix_two_lt_globalR
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    (2 : ℕ∞) < globalR U := by
  let := D.elementary
  have hE := original_chosen_hypothesisE61_at h structural D
  have hr1 := original_tripleSix_one_lt_globalR h structural D a t ht heven contained
  by_contra hn
  have hr : globalR U ≤ 2 := le_of_not_gt hn
  have hfinite : globalR U ≠ ⊤ := ne_top_of_le_ne_top (by simp) hr
  obtain ⟨W, hWU, hescape, hcorEq⟩ := globalR_attained hfinite
  have hcor : subgroupCorank U W ≤ 2 := by exact_mod_cast hcorEq.le.trans hr
  have hW : W ≠ ⊥ := by
    intro hz
    have hcU : Nat.card U = 64 :=
      (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans hexacode_card
    norm_num [hz, subgroupCorank, relIndex_bot_left, hcU] at hcor
  have hescape' : ¬ centralizer (W : Set G) ≤ normalizer (K : Set G) :=
    fun hc => hescape ((hE.centralizer_le_iff hW hWU).mp hc)
  have hC := localCentralizer_eq_of_small_escape h structural D a t ht heven contained
    W hWU hW hcor hescape'
  obtain ⟨_, _, _, _, _, he⟩ := hE.hyperplane_escape_of_maximal_action
    (fun _ hW hmax hn => maximal_escape_action_knownSimple hE hW hmax hn)
    hW hWU hC hescape'
  rw [he] at hr1
  exact lt_irrefl _ hr1

set_option maxHeartbeats 400000 in
/-- The full original automizer has minimum involution codimension two. -/
theorem original_tripleSix_localM_eq_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction) :
    let := D.elementary
    localM U = 2 := by
  let := D.elementary
  obtain ⟨f, hf, _, himage, heq⟩ := original_tripleSix_full_automizer h structural D a
  let c := tripleSixPointCoordinates D a
  let E : Additive U ≃ₗ[ZMod 2] hexacode :=
    LinearEquiv.ofBijective (c.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) c.bijective
  have heq' (b : Automizer U) (v : Additive U) :
      E (automizerRepresentation U b v) = Hexacode.action (f b) (E v) := heq b v.toMul
  have hcost (b : Automizer U) :
      fixedCodim (automizerRepresentation U) (zpowers b) =
        fixedCodim Hexacode.action (zpowers (f b)) := by
    rw [fixedCodim_map_equivariant (automizerRepresentation U) Hexacode.action f E heq',
      MonoidHom.map_zpowers]
  obtain ⟨y, hyo⟩ := exists_prime_orderOf_dvd_card' (G := HexEvenAutomorphisms) 2
    (by rw [hexEven_card]; decide)
  have hy2 : y ^ 2 = 1 := by
    rw [← hyo]
    exact pow_orderOf_eq_one y
  have hyne : y ≠ 1 := by intro hy; simp [hy] at hyo
  have hyimage : y.val ∈ (inducedAutomizer U K).map f := himage.symm ▸ y.property
  obtain ⟨b, _, hb⟩ := hyimage
  have hb2 : b ^ 2 = 1 := by
    apply hf
    rw [map_pow, hb, map_one]
    exact congrArg Subtype.val hy2
  have hbne : b ≠ 1 := by
    intro hh
    have hh' : y.val = 1 := hb.symm.trans (hh ▸ f.map_one)
    exact hyne (Subtype.ext hh')
  have hbe : orderOf b = 2 := orderOf_eq_prime hb2 hbne
  have hycd : fixedCodim Hexacode.action (zpowers y.val) = 2 := by
    have hh := fixedCodim_add_finrank Hexacode.evenAction (zpowers y)
    rw [Hexacode.ProjectiveLineNormalizer.involution_fixedSpace_finrank y hy2 hyne,
      hexacode_finrank] at hh
    have he : fixedCodim Hexacode.evenAction (zpowers y) =
        fixedCodim Hexacode.action (zpowers y.val) := by
      change fixedCodim (Hexacode.action.comp hexSign.ker.subtype) _ = _
      unfold fixedCodim
      rw [fixedSpace_comp_map, MonoidHom.map_zpowers]
      rfl
    rw [he] at hh
    omega
  apply le_antisymm
  · change moduleM (automizerRepresentation U) ≤ 2
    have hh := moduleM_le_involution (automizerRepresentation U) hbe
    rwa [hcost, hb, hycd] at hh
  · change 2 ≤ moduleM (automizerRepresentation U)
    apply le_csInf ⟨_, Set.mem_insert _ _⟩
    rintro n (rfl | ⟨b, hb, rfl⟩)
    · have hd : Module.finrank (ZMod 2) (Additive U) = 6 :=
        E.finrank_eq.trans hexacode_finrank
      omega
    · have hbne : b ≠ 1 := by intro hh; simp [hh] at hb
      have hz : zpowers b ≠ ⊥ := by
        intro hh
        exact hbne (mem_bot.mp (hh ▸ mem_zpowers b))
      have hp := fixedCodim_pos_of_faithful (automizerRepresentation U)
        (automizerRepresentation_injective U) hz
      have hn := Hexacode.no_transvections (f b)
      rw [← hcost] at hn
      omega

/-- Original 12.7.10(2), with both numerical conclusions proved from the
 unchanged chosen module and its contained point centralizer. -/
theorem original_tripleSix_contained_rank_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let := D.elementary
    (2 : ℕ∞) < globalR U ∧ globalS U = 2 := by
  let := D.elementary
  have hr := original_tripleSix_two_lt_globalR h structural D a t ht heven contained
  refine ⟨hr, ?_⟩
  change min (globalR U) (localM U : ℕ∞) = 2
  rw [original_tripleSix_localM_eq_two h structural D a]
  exact min_eq_right hr.le

end CFSG.Quasithin.Chapter12.Section07

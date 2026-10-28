module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedRanks
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.Representation.HexacodeAction.ThreeSpaceCentralizers

/-!
# The actual actor at an escaping original corank-three subgroup

E.6.12 supplies nontrivial local action at the original subgroup. Containment
of all full-weight point centralizers excludes full-weight words from its
literal chart image. The hexacode three-space theorem therefore identifies
the original local automizer as one outer involution, and identifies its
fixed subgroup with the original subgroup W.

Source: Aschbacher--Smith, 12.7.10(4--5), printed pp.842--843.
No permutation class marking is asserted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterE.Section06 ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- An escaping original corank-three subgroup is exactly the fixed subgroup
of the unique nontrivial local automizer, which lies outside the K-image. -/
theorem original_tripleSix_escaping_threeSpace
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (W : Subgroup G) (hWU : W ≤ U) (hcor : subgroupCorank U W = 3)
    (hescape : ¬ centralizer (W : Set G) ≤ normalizer (K : Set G)) :
    ∃ b : Automizer U, b ≠ 1 ∧ b ^ 2 = 1 ∧ b ∉ inducedAutomizer U K ∧
      (∀ u : U, b.val u = u ↔ (u : G) ∈ W) ∧
      inducedAutomizer U (normalizer (K : Set G) ⊓ centralizer (W : Set G)) =
        zpowers b := by
  let := D.elementary
  let c := tripleSixPointCoordinates D a
  let Q := AddSubgroup.toZModSubmodule 2
    (Subgroup.toAddSubgroup' ((W.subgroupOf U).map c.toMonoidHom))
  have hdim : Module.finrank Bit Q = 3 := by
    have hcQ : Nat.card Q = Nat.card W := by
      change Nat.card ((W.subgroupOf U).map c.toMonoidHom) = Nat.card W
      rw [card_map_of_injective c.injective]
      exact Nat.card_congr (subgroupOfEquivOfLe hWU).toEquiv
    have hcU : Nat.card U = 64 := (Nat.card_congr c.toEquiv).trans hexacode_card
    have hcount : Nat.card W * W.relIndex U = Nat.card U := by
      simpa only [relIndex_bot_left] using
        relIndex_mul_relIndex (⊥ : Subgroup G) W U bot_le hWU
    rw [← hcQ, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      relIndex_eq_two_pow_quotient_finrank, ← subgroupCorank_eq_quotient_finrank,
      hcor, ← pow_add, hcU] at hcount
    have hh : Module.finrank Bit Q + 3 = 6 :=
      Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hcount
    omega
  have hWne : W ≠ ⊥ := by
    intro hh
    have hQ : Q = ⊥ := by
      ext v
      change Multiplicative.ofAdd v ∈ (W.subgroupOf U).map c.toMonoidHom ↔ v = 0
      simp [hh]
    rw [hQ, finrank_bot] at hdim
    omega
  have hE := original_chosen_hypothesisE61_at h structural D
  let C := normalizer (K : Set G) ⊓ centralizer (W : Set G)
  let B := inducedAutomizer U C
  have hCN : C ≤ normalizer (U : Set G) :=
    hE.localCentralizer_le_normalizer hWne hWU
  have hB : B ≠ ⊥ := by
    intro hh
    have hCU : C ≤ centralizer (U : Set G) :=
      (inducedAutomizer_eq_bot_iff hCN).mp hh
    have hC : normalizer (K : Set G) ⊓ centralizer (W : Set G) =
        normalizer (K : Set G) ⊓ centralizer (U : Set G) :=
      le_antisymm (le_inf inf_le_left hCU)
        (inf_le_inf_left _ (centralizer_le hWU))
    obtain ⟨_, _, _, _, _, hr⟩ := hE.hyperplane_escape_of_maximal_action
      (fun _ hX hmax hn => maximal_escape_action_knownSimple hE hX hmax hn)
      hWne hWU hC hescape
    have hgt := original_tripleSix_one_lt_globalR h structural D a t ht heven contained
    rw [hr] at hgt
    exact lt_irrefl _ hgt
  obtain ⟨b, hb, hbne⟩ := B.bot_or_exists_ne_one.resolve_left hB
  obtain ⟨f, hf, _, himage, heq⟩ := original_tripleSix_full_automizer h structural D a
  have hQmem (u : U) : (c u).toAdd ∈ Q ↔ (u : G) ∈ W := by
    change c u ∈ (W.subgroupOf U).map c.toMonoidHom ↔ (u : G) ∈ W
    constructor
    · rintro ⟨v, hv, hvu⟩
      have he : v = u := c.injective hvu
      exact he ▸ hv
    · intro hu
      exact ⟨u, hu, rfl⟩
  have hfull : ∀ w ∈ Q, hammingNorm (w : HexWord) ≠ 6 := by
    intro w hw hweight
    obtain ⟨u, hu⟩ := c.surjective (Multiplicative.ofAdd w)
    have huW : (u : G) ∈ W := (hQmem u).mp (by rw [hu]; exact hw)
    have huweight : hammingNorm (c u).toAdd.val = 6 := by rw [hu]; exact hweight
    exact hescape ((centralizer_le (Set.singleton_subset_iff.mpr huW)).trans
      (original_tripleSix_full_weight_centralizer_le D a t ht heven contained u huweight))
  have hfix (d : Automizer U) (hd : d ∈ B) :
      ∀ w ∈ Q, Hexacode.action (f d) w = w := by
    intro w hw
    obtain ⟨u, hu⟩ := c.surjective (Multiplicative.ofAdd w)
    have huW : (u : G) ∈ W := (hQmem u).mp (by rw [hu]; exact hw)
    have hdu : d.val u = u := by
      obtain ⟨n, hn, rfl⟩ := hd
      apply Subtype.ext
      change (n : G) * (u : G) * (n : G)⁻¹ = u
      have hc : (u : G) * (n : G) = (n : G) * (u : G) :=
        (mem_centralizer_iff.mp hn.2) u huW
      rw [← hc, mul_inv_cancel_right]
    have hh := (heq d u).symm.trans (congrArg (fun z => (c z).toAdd) hdu)
    change Hexacode.action (f d) (c u).toAdd = (c u).toAdd at hh
    rw [hu] at hh
    exact hh
  have hfb : f b ≠ 1 := fun hh => hbne (hf (hh.trans f.map_one.symm))
  obtain ⟨hodd, h2, hfixed, hkernel⟩ :=
    Hexacode.threeSpace_pointwise_kernel Q hdim hfull (f b) hfb (hfix b hb)
  have hb2 : b ^ 2 = 1 := hf (by rw [map_pow, h2, map_one])
  have hbnot : b ∉ inducedAutomizer U K := by
    intro hh
    have he : f b ∈ hexSign.ker := himage ▸ ⟨b, hh, rfl⟩
    change hexSign (f b) = 1 at he
    rw [he] at hodd
    exact (by decide : (1 : ℤˣ) ≠ -1) hodd
  refine ⟨b, hbne, hb2, hbnot, ?_, ?_⟩
  · intro u
    have he : b.val u = u ↔ Hexacode.action (f b) (c u).toAdd = (c u).toAdd := by
      constructor
      · intro hh
        exact (heq b u).symm.trans (congrArg (fun z => (c z).toAdd) hh)
      · intro hh
        apply c.injective
        exact (heq b u).trans hh
    rw [he, ← mem_fixedSpace_zpowers_iff, hfixed]
    exact hQmem u
  · apply map_injective hf
    rw [MonoidHom.map_zpowers]
    apply le_antisymm
    · rintro _ ⟨d, hd, rfl⟩
      rw [← hkernel]
      exact ⟨mem_top _, hfix d hd⟩
    · exact zpowers_le.mpr ⟨b, hb, rfl⟩

end CFSG.Quasithin.Chapter12.Section07

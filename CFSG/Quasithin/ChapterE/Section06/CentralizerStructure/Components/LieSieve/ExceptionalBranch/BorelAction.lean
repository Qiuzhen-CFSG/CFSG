module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.LocalSubgroups
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.BorelAction.Geometry
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The intrinsic PSL₂(4) Borel action

Suppose V fixes a Sylow two-subgroup S of L pointwise, where L is the genuine
PSL₂(4), and its Borel B normalizes V. Each element of V acts on L as an
inner automorphism induced by an element of S. Thus [V,B] lies in S. A
nontrivial action gives a nontrivial displacement, and the cubic Borel action
forces that displacement to be all of S. In particular S lies in V.

Removing this internal conjugator from an element of V gives the central
factor C_V(L). The centerless component makes the two factors disjoint.
Finally C_B(V) is exactly S, so the actual induced automizer has order three.
Both binary coranks are two. All subgroups and action images retain their
original embeddings; no exceptional-alternative record is assumed.

This is the intrinsic Borel calculation for Aschbacher–Smith, combined
manuscript (1 March 2004), E.6.8, printed pp.247–248 (PDF pp.258–259).
The ambient source assembly supplies the Borel intersection and the action
hypotheses; the separate Sylow-only branch is not used here.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.BorelAction
variable {G : Type*} [Group G] [Finite G] {V L B : Subgroup G}

private theorem inner_conjugator (e : L ≃* alternatingGroup (Fin 5))
    (hN : V ≤ normalizer (L : Set G)) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G))
    (v : G) (hv : v ∈ V) :
    ∃ s ∈ S, ∀ l : L, v * (l : G) * v⁻¹ = (s : G) * (l : G) * (s : G)⁻¹ := by
  obtain ⟨s, hs, he⟩ := Theory.PSL2.SylowFixedQuotients.sylow_fixed_inner_of_equiv_five e S
    (L.normalizerMonoidHom ⟨v, hN hv⟩) (by
      intro s hs
      exact Subtype.ext (hfix v hv ⟨s, hs⟩))
  refine ⟨s, hs, ?_⟩
  intro l
  exact congrArg Subtype.val (congrArg (fun a : MulAut L => a l) he)

omit [Finite G] in
private theorem commutator_inner (v : G) (s : L)
    (ha : ∀ l : L, v * (l : G) * v⁻¹ = (s : G) * (l : G) * (s : G)⁻¹)
    (b : L) : ⁅v, (b : G)⁆ = (⁅s, b⁆ : L) := by
  simp only [commutatorElement_def]
  rw [ha b]
  rfl

private theorem displacement_eq (e : L ≃* alternatingGroup (Fin 5))
    (hN : V ≤ normalizer (L : Set G)) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G))
    (hB : B = (normalizer (S : Set L)).map L.subtype)
    (hne : ¬ V ≤ centralizer (L : Set G)) :
    ⁅V, B⁆ = (S : Subgroup L).map L.subtype := by
  obtain ⟨_, _, _, hmove, hirr⟩ := sylow_borel_geometry e S
  have hle : ⁅V, B⁆ ≤ (S : Subgroup L).map L.subtype := by
    apply commutator_le.mpr
    intro v hv b hb
    obtain ⟨s, hs, ha⟩ := inner_conjugator e hN S hfix v hv
    obtain ⟨b, hbN, rfl⟩ := hB ▸ hb
    change ⁅v, (b : G)⁆ ∈ (S : Subgroup L).map L.subtype
    rw [commutator_inner v s ha b]
    refine mem_map.mpr ⟨⁅s, b⁆, ?_, rfl⟩
    change s * b * s⁻¹ * b⁻¹ ∈ (S : Subgroup L)
    simpa only [mul_assoc] using
      (S : Subgroup L).mul_mem hs ((hbN s⁻¹).mp ((S : Subgroup L).inv_mem hs))
  have hWL : ⁅V, B⁆ ≤ L := hle.trans (map_subtype_le _)
  have hWne : ⁅V, B⁆ ≠ ⊥ := by
    intro hbot
    apply hne
    intro v hv
    obtain ⟨s, hs, ha⟩ := inner_conjugator e hN S hfix v hv
    have hs1 : s = 1 := by
      by_contra hs1
      obtain ⟨b, hb, hm⟩ := hmove s hs hs1
      have hmem := commutator_mem_commutator hv (hB.symm ▸ mem_map_of_mem L.subtype hb)
      rw [hbot, mem_bot] at hmem
      change ⁅v, (b : G)⁆ = 1 at hmem
      rw [commutator_inner v s ha b] at hmem
      exact hm (Subtype.ext hmem)
    apply mem_centralizer_iff.mpr
    intro l hl
    have he := ha ⟨l, hl⟩
    simp only [hs1, OneMemClass.coe_one, one_mul, inv_one, mul_one] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hD : ⁅V, B⁆.subgroupOf L = S := by
    apply hirr
    · intro x hx
      obtain ⟨s, hs, he⟩ := hle hx
      exact (Subtype.ext he : s = x) ▸ hs
    · intro b hb x
      exact (normalizer_commutator_ge_right V B (hB.symm ▸ mem_map_of_mem L.subtype hb)) (x : G)
    · intro hd
      apply hWne
      have he := congrArg (Subgroup.map L.subtype) hd
      simpa only [map_subgroupOf_eq_of_le hWL, Subgroup.map_bot] using he
  have he := congrArg (Subgroup.map L.subtype) hD
  simpa only [map_subgroupOf_eq_of_le hWL] using he

private theorem decomposition (e : L ≃* alternatingGroup (Fin 5))
    (hN : V ≤ normalizer (L : Set G)) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G))
    (hPV : (S : Subgroup L).map L.subtype ≤ V) :
    DirectDecomposition V ((S : Subgroup L).map L.subtype) (V ⊓ centralizer (L : Set G)) := by
  have hc := (sylow_borel_geometry e S).2.1
  have hPL : (S : Subgroup L).map L.subtype ≤ L := map_subtype_le _
  refine ⟨le_antisymm (sup_le hPV inf_le_left) ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨s, hs, ha⟩ := inner_conjugator e hN S hfix v hv
    have hsP := mem_map_of_mem L.subtype hs
    have hcV : (s : G)⁻¹ * v ∈ V := V.mul_mem (V.inv_mem (hPV hsP)) hv
    have hcL : (s : G)⁻¹ * v ∈ centralizer (L : Set G) := by
      apply mem_centralizer_iff.mpr
      intro l hl
      have hh := ha ⟨l, hl⟩
      have hh' : ((s : G)⁻¹ * v) * l * ((s : G)⁻¹ * v)⁻¹ = l := by
        calc
          _ = (s : G)⁻¹ * (v * l * v⁻¹) * s := by group
          _ = (s : G)⁻¹ * ((s : G) * l * (s : G)⁻¹) * s := by rw [hh]
          _ = l := by group
      exact (mul_inv_eq_iff_eq_mul.mp hh').symm
    have hm := ( (S : Subgroup L).map L.subtype ⊔ (V ⊓ centralizer (L : Set G))).mul_mem
      (mem_sup_left hsP) (mem_sup_right ⟨hcV, hcL⟩)
    change (s : G) * ((s : G)⁻¹ * v) ∈
      (S : Subgroup L).map L.subtype ⊔ (V ⊓ centralizer (L : Set G)) at hm
    simpa only [mul_inv_cancel_left] using hm
  · apply bot_unique
    rintro x ⟨hxP, _, hxC⟩
    have hxL := hPL hxP
    have hh : (⟨x, hxL⟩ : L) ∈ center L := by
      apply mem_center_iff.mpr
      intro l
      exact Subtype.ext (mem_centralizer_iff.mp hxC l l.property)
    rw [hc] at hh
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hh))
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    exact le_centralizer_iff.mpr (inf_le_right.trans (centralizer_le hPL))

private theorem borel_centralizer (e : L ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G))
    (hPV : (S : Subgroup L).map L.subtype ≤ V)
    (hB : B = (normalizer (S : Set L)).map L.subtype) :
    B ⊓ centralizer (V : Set G) = (S : Subgroup L).map L.subtype := by
  have hcs := (sylow_borel_geometry e S).2.2.1
  apply le_antisymm
  · rintro x ⟨hxB, hxC⟩
    obtain ⟨b, hb, rfl⟩ := hB ▸ hxB
    apply mem_map_of_mem
    apply hcs
    apply mem_centralizer_iff.mpr
    intro s hs
    exact Subtype.ext (mem_centralizer_iff.mp hxC s (hPV (mem_map_of_mem L.subtype hs)))
  · rintro x ⟨s, hs, rfl⟩
    refine ⟨hB.symm ▸ mem_map_of_mem L.subtype ((S : Subgroup L).le_normalizer hs), ?_⟩
    apply mem_centralizer_iff.mpr
    intro v hv
    exact mul_inv_eq_iff_eq_mul.mp (hfix v hv ⟨s, hs⟩)

omit [Finite G] in
private theorem corank_of_decomposition [IsElementaryAbelian 2 V]
    (P : Subgroup G) (hc : Nat.card P = 4)
    (hd : DirectDecomposition V P (V ⊓ centralizer (L : Set G))) :
    actionCorank V L = 2 := by
  have hPV : P ≤ V := le_sup_left.trans hd.1.le
  have h := relIndex_sup_right (P.subgroupOf V)
    ((V ⊓ centralizer (L : Set G)).subgroupOf V)
  rw [← subgroupOf_sup hPV inf_le_left, hd.1,
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf hPV] at h
  have hi : (V ⊓ centralizer (L : Set G)).relIndex P = 4 := by
    rw [← inf_relIndex_right (V ⊓ centralizer (L : Set G)) P, inf_comm,
      hd.2.1, relIndex_bot_left, hc]
  change Nat.log 2 ((V ⊓ centralizer (L : Set G)).relIndex V) = 2
  rw [h, hi]
  decide

omit [Finite G] in
private theorem automizer_card (S : Sylow 2 L)
    (hS : Nat.card ((S : Subgroup L).map L.subtype) = 4)
    (hB : B = (normalizer (S : Set L)).map L.subtype)
    (hBc : Nat.card B = 12) (hBN : B ≤ normalizer (V : Set G))
    (hC : B ⊓ centralizer (V : Set G) = (S : Subgroup L).map L.subtype) :
    Nat.card (inducedAutomizer V B) = 3 := by
  have hPB : (S : Subgroup L).map L.subtype ≤ B := by
    rw [hB]
    exact map_mono (S : Subgroup L).le_normalizer
  have h := relIndex_mul_relIndex (⊥ : Subgroup G)
    ((S : Subgroup L).map L.subtype) B bot_le hPB
  rw [relIndex_bot_left, relIndex_bot_left, hS, hBc] at h
  unfold inducedAutomizer
  rw [← relIndex_ker, MonoidHom.ker_rangeRestrict, normalizerMonoidHom_ker,
    relIndex_subgroupOf hBN, ← inf_relIndex_right, inf_comm, hC]
  omega

/-- The intrinsic PSL₂(4) Borel action, retaining the actual embedded Sylow
four-group, displacement, central factor, and induced automizer. -/
theorem intrinsic_borel_action [IsElementaryAbelian 2 V]
    (hm : ClassicalGroup.IsPSL L 2 4)
    (hN : V ≤ normalizer (L : Set G)) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G))
    (hB : B = (normalizer (S : Set L)).map L.subtype)
    (hBN : B ≤ normalizer (V : Set G))
    (hne : ¬ V ≤ centralizer (L : Set G)) :
    ⁅V, B⁆ = (S : Subgroup L).map L.subtype ∧
    DirectDecomposition V ⁅V, B⁆ (V ⊓ centralizer (L : Set G)) ∧
    actionCorank V L = 2 ∧ subgroupCorank ⁅V, B⁆ ⊥ = 2 ∧
    Nonempty (inducedAutomizer V B ≃* Multiplicative (ZMod 3)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let eL := e.trans eA
  have hW := displacement_eq eL hN S hfix hB hne
  have hPV : (S : Subgroup L).map L.subtype ≤ V :=
    hW ▸ le_normalizer_iff_commutator_le_left.mp hBN
  have hd := decomposition eL hN S hfix hPV
  have hc : Nat.card ((S : Subgroup L).map L.subtype) = 4 := by
    rw [card_map_of_injective L.subtype_injective]
    exact Theory.PSL2.SylowFixedQuotients.sylow_card_of_equiv_five eL S
  have hBc : Nat.card B = 12 := by
    rw [hB, card_map_of_injective L.subtype_injective]
    exact (sylow_borel_geometry eL S).1
  have hAc := automizer_card S hc hB hBc hBN (borel_centralizer eL S hfix hPV hB)
  refine ⟨hW, hW.symm ▸ hd, corank_of_decomposition _ hc hd, ?_, ?_⟩
  · rw [hW, subgroupCorank, relIndex_bot_left, hc]
    decide
  · let : Fact (Nat.Prime 3) := ⟨by decide⟩
    let : IsCyclic (inducedAutomizer V B) := isCyclic_of_prime_card hAc
    exact ⟨mulEquivOfCyclicCardEq (by simpa using hAc)⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.BorelAction

module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LieSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.SmallRows
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.MathieuSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.Bender
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.PairBinary
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LargeSporadic.Mathieu24.Cubic
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LargeSporadic.Rudvalis.Cubic
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LargeSporadic.HS_Held.HS
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Ordinary
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115.Transport
/-!
# The original paired-five overcomponent census

Apply the actual marked 1.1.5 actor to the component of the original Phi
normalizer. The faithful block and its elementary sixteen exclude the odd,
alternating, binary and small sporadic rows. Native invariant escapes lift
through the literal component quotient in the rank-two and Mathieu rows.
Original opposite-block cubic centralizers exclude M24, HS and Rudvalis.
The precise remaining families are J4 and Held; their independent native
terminal producers are required to finish the source argument.

Source: Aschbacher–Smith 2.4.25, printed pp.542–543. No ambient Sylow bound
on the ordinary component is introduced.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}
private theorem simple_perfect_center_eq_bot {E : Type*} [Group E]
    [IsSimpleGroup E] [Group.IsPerfect E] : center E = ⊥ :=
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center E) inferInstance).resolve_right
    (fun h => Group.IsPerfect.not_isMulCommutative E (center_eq_top_iff.mp h))

theorem AlternatingPairSourceSetup.modelAction_overcomponent_remaining
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∀ (K : Subgroup GI), IsComponent GI K → L.subgroupOf GI ≤ K →
    SI S L ≤ normalizer (K.map GI.subtype : Set G) →
    ∀ a : MulAut K, ModelAction115 K a →
    ∃ name : ClassificationModels.SporadicName,
      (name = .j4 ∨ name = .he) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier) := by
  intro S L GI K hK hLK hNK a hm
  let : IsQuasisimple K := hK.2
  cases hm with
  | lie hs hm _ =>
    let : IsSimpleGroup K := hs
    have hz : center K = ⊥ := simple_perfect_center_eq_bot
    have hc : pCore 2 K = ⊥ := bot_unique ((IsQuasisimple.pCore_le_center 2).trans_eq hz)
    let e : (K ⧸ pCore 2 K) ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    rcases hm with hm | hm | ⟨n,hn,hm⟩
    · exact (c.bender_overcomponent_false hG T hM hTM hu hST hSM hMT hi K hK hLK
        (hm.of_mulEquiv e)).elim
    · exact (c.rank_two_quotient_overcomponent_false hG T hM hTM hu hST hSM hMT hi
        K hK hLK hNK hm ⟨e⟩).elim
    · rcases hn with rfl | rfl
      · apply False.elim
        exact c.no_block_overcomponent_false hG T hM hTM hu hST hSM hMT hi K hK hLK hNK
          (fun A hA hU => Chapter13.Section05.NormalBranch.DeletedFive.not_psl4Two_of_alternatingFive A hA hU hm)
          ⟨MulEquiv.refl K⟩
      · let ez : (K ⧸ center K) ≃* K :=
          (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
        exact (c.binary_five_overcomponent_false hG T hM hTM hu hST hSM hMT hi
          K hK hLK hNK (hm.of_mulEquiv ez)).elim
  | two_cover _ hc hm _ =>
    let e : (K ⧸ pCore 2 K) ≃* (K ⧸ center K) := QuotientGroup.quotientMulEquivOfEq hc.symm
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
    let : Group.IsPerfect (K ⧸ pCore 2 K) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 K))
    apply False.elim
    apply c.rank_two_quotient_overcomponent_false hG T hM hTM hu hST hSM hMT hi
      K hK hLK hNK (D := K ⧸ pCore 2 K) ?_ ⟨MulEquiv.refl _⟩
    rcases hm with hm | hm
    · exact .linear 2 (by decide) (by simpa using hm)
    · exact .g2 2 (by decide) (by simpa using hm)
  | six s _ hm =>
    apply False.elim
    exact c.no_block_overcomponent_false hG T hM hTM hu hST hSM hMT hi K hK hLK hNK
      (AlternatingTerminal.alternating_action_no_alternating_five_block a (Or.inl rfl) s hm)
      ⟨MulEquiv.refl K⟩
  | seven s _ hm =>
    apply False.elim
    exact c.no_block_overcomponent_false hG T hM hTM hu hST hSM hMT hi K hK hLK hNK
      (AlternatingTerminal.alternating_action_no_alternating_five_block a (Or.inr rfl) s hm)
      ⟨MulEquiv.refl K⟩
  | odd hm _ =>
    apply False.elim
    exact c.no_block_overcomponent_false hG T hM hTM hu hST hSM hMT hi K hK hLK hNK
      (AlternatingTerminal.odd_no_alternating_five_block hm) ⟨MulEquiv.refl K⟩
  | sporadic name hn hm _ =>
    cases name with
    | m11 => exact (c.small_sporadic_overcomponent_false hG T hM hTM hu hST hSM hMT hi
        K hK hLK hNK .m11 (Or.inl rfl) hm).elim
    | m12 => exact (c.small_sporadic_overcomponent_false hG T hM hTM hu hST hSM hMT hi
        K hK hLK hNK .m12 (Or.inr (Or.inl rfl)) hm).elim
    | m22 => exact (c.mathieu22_overcomponent_false hG T hM hTM hu hST hSM hMT hi
        K hK hLK hNK hm).elim
    | m23 => exact (c.mathieu23_overcomponent_false hG T hM hTM hu hST hSM hMT hi
        K hK hLK hNK hm).elim
    | m24 => exact (c.mathieu24_overcomponent_false hG T hM hTM hu hST hSM hMT hi
        K hK hLK hNK hm).elim
    | j2 => exact (c.small_sporadic_overcomponent_false hG T hM hTM hu hST hSM hMT hi
        K hK hLK hNK .j2 (Or.inr (Or.inr rfl)) hm).elim
    | j3 => exact (hn rfl).elim
    | j4 => exact ⟨.j4,Or.inl rfl,hm⟩
    | hs => exact (c.hs_overcomponent_false hG T hM hTM hu hST hSM hMT hi
        K hK hLK hNK hm).elim
    | he => exact ⟨.he,Or.inr rfl,hm⟩
    | ru => exact (c.rudvalis_overcomponent_false hG T hM hTM hu hST hSM hMT hi
        K hK hLK hNK hm).elim

/-- Original paired-source reduction, using its actual marked 1.1.5 actor. -/
theorem AlternatingPairSourceSetup.ordinary_overcomponent_remaining
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∀ (K : Subgroup GI), IsComponent GI K → L.subgroupOf GI ≤ K →
    SI S L ≤ normalizer (K.map GI.subtype : Set G) →
    ∃ name : ClassificationModels.SporadicName,
      (name = .j4 ∨ name = .he) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier) := by
  intro S L GI K hK hLK hNK
  obtain ⟨P,z,h115⟩ := c.phi_involution_marks hG T hM hTM hu hST hSM hMT hi
  obtain ⟨_,_,a,_,hm⟩ := Chapter1.lemma_1_1_5_three_knownSimple hG GI P M z h115 K hK
  exact c.modelAction_overcomponent_remaining hG T hM hTM hu hST hSM hMT hi
    K hK hLK hNK a hm
end CFSG.Quasithin.Chapter2

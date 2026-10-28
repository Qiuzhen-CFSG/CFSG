module

public import Theory.GroupTheory.ComponentLocalPrimeFree
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.LocalPair
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.LargeLocal.Seeds
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.LargeLocal.OrbitCalculations

/-!
# Large Ree invariant overgroups and relative block layers

The component stabilizer N_S(L), rather than all of S, normalizes the local
subgroup K. Distinct S-conjugates of L commute, so the corresponding conjugates
of K introduce no new prime divisors. Thus adjoining the whole Sylow two-subgroup
preserves the absence of three. An actual Suzuki quotient by O₂(K) supplies
this absence for the Suzuki-side local factor.

The root-defined fixed local factors supply a generating invariant pair. Their
nontrivial self-centralizing two-cores give HeOver membership after adjoining S.
The linear factor is perfect with simple quotient by its two-core, so every
escaping relative block contains a conjugate local factor. Its nonzero third
commutator survives in the block's intersection with the overgroup's two-core.

The final theorem assembles all these calculations from an actual exceptional
endomorphism, an equivalence with its fixed subgroup, and component simplicity.
The factors are those of F.1.12(I)(5), not full parabolics with torus factors.
No further geometry, quotient, invariance or block-exclusion premise remains.
The inner action supplied by 1.1.5(3)(a) is unnecessary for this calculation.

Source: Aschbacher–Smith 2.3.9(7), printed p.526, using F.1.12(I)(5) and (II),
printed pp.263–264. The classification parent still supplies the exceptional
endomorphism and applies `false_of_pair_calculations` for the final exclusion.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

variable {G : Type*} [Group G]

/-- The whole Sylow subgroup may be adjoined to a three-free invariant local
subgroup of a component, even if it permutes components. -/
public theorem local_overgroup_three_free {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (K : Subgroup L)
    (hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (K.map L.subtype : Set G))
    (hcard : ¬ 3 ∣ Nat.card K) :
    ¬ 3 ∣ Nat.card (K.map L.subtype ⊔ (S : Subgroup H).map H.subtype : Subgroup G) := by
  let := h.finite
  let K' := (K.map L.subtype).subgroupOf H
  have hKH : K.map L.subtype ≤ H := (map_subtype_le K).trans h.component_le
  have hK' : K' ≤ L.subgroupOf H := fun _ hx => map_subtype_le K hx
  have hinv' : (S : Subgroup H) ⊓ normalizer (L.subgroupOf H : Set H) ≤
      normalizer (K' : Set H) := by
    rw [← subgroupOf_normalizer_eq h.component_le]
    change (S : Subgroup H) ⊓ (normalizer (L : Set G)).subgroupOf H ≤
      normalizer ((K.map L.subtype).subgroupOf H : Set H)
    rw [← subgroupOf_normalizer_eq hKH]
    intro x hx
    exact hinv ⟨mem_map_of_mem H.subtype hx.1, hx.2⟩
  have hcard' : ¬ 3 ∣ Nat.card K' := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv,
      card_map_of_injective L.subtype_injective]
  have hS : ¬ 3 ∣ Nat.card (S : Subgroup H) := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hf := IsComponent.not_dvd_card_local_adjoin Nat.prime_three
    h.component hK' hinv' hcard' hS
  have hm : (K' ⊔ (S : Subgroup H)).map H.subtype =
      K.map L.subtype ⊔ (S : Subgroup H).map H.subtype := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKH]
  rw [← hm, card_map_of_injective H.subtype_injective]
  exact hf

/-- The Suzuki quotient calculation suffices for the order of the full-S
overgroup. The actual invariant local subgroup and its quotient isomorphism
remain explicit inputs, to be constructed in the Ree geometry calculation. -/
public theorem suzukiSide_overgroup_three_free {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (K : Subgroup L)
    (hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (K.map L.subtype : Set G))
    (m : ℕ) (hm : 1 ≤ m)
    (e : (K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    ¬ 3 ∣ Nat.card (K.map L.subtype ⊔ (S : Subgroup H).map H.subtype : Subgroup G) := by
  let := h.finite
  exact local_overgroup_three_free h K hinv (BenderSuzuki.MatrixGroups.three_free_of_suzuki_core_quotient m hm e)

/-- The large Ree local calculations on one actual invariant pair. Both factors
contain the component's Sylow intersection, and their overgroups contain the
whole S. Membership in HeOver includes nontriviality of the actual two-core.
The layer is normal relative to the block inside the right overgroup.

Component simplicity is supplied by source 1.1.5(3)(a); existence of the exact
exceptional endomorphism is the separate model-construction input. The conclusion
supplies every local premise of `false_of_pair_calculations`. -/
public theorem large_exists_local_calculations
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G} {m : ℕ}
    (h : LocalSetup H L M S z) [IsSimpleGroup L] (hm : 1 ≤ m)
    (d : ReeF4.LocalBlockInput m) (e : L ≃* d.fixedGroup) :
    ∃ p : InvariantPair L ((S : Subgroup H).map H.subtype),
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ p.left ∧
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ p.right ∧
      p.leftOver ∈ Chapter1.HeOver G
        (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) ∧
      p.rightOver ∈ Chapter1.HeOver G
        (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) ∧
      ¬ 3 ∣ Nat.card p.leftOver ∧
      ∀ B : Subgroup p.rightOver, ChapterC.IsBlock B →
        B.map p.rightOver.subtype =
          ⁅B.map p.rightOver.subtype,
            Stellmacher.elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype)⁆ →
        ¬ B.map p.rightOver.subtype ≤ M → HasNoncentralTwoLayer B := by
  obtain ⟨p, hleft, hright, hneLeft, hcentLeft, hneRight, hcentRight,
    ⟨qSuzuki⟩, hperfect, _, hsimple, hthird⟩ := exists_pair_of_localBlockInput d h hm e
  let := hperfect
  let := hsimple
  refine ⟨p, hleft, hright,
    local_overgroup_mem_HeOver h p.left p.invariant_left hneLeft hcentLeft,
    local_overgroup_mem_HeOver h p.right p.invariant_right hneRight hcentRight,
    suzukiSide_overgroup_three_free h p.left p.invariant_left m hm qSuzuki, ?_⟩
  intro B hB _ hout
  exact noncentralTwoLayer_of_local_block h p.right p.invariant_right hthird B hB hout

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

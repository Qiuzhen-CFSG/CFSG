module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Bounds
public import Theory.GroupTheory.SubgroupProductCard

/-!
# Orders of the Suzuki Sylow groups and their quotient

The literal disjoint product T = PU gives |T| = q²|U|. The supplied
isomorphism S/T ≃ M° then gives |S| = q³|U|. Applying the cardinality
formula for the kernel and range of S → M/M° gives |S/M°| = q²|U|.
Thus |U| = 2 will give the exact dimension 2n+1 used at the end of 14.9.

Source: GLS4, Chapter 2, (14B–14C), Lemma 14.6(b), and the final argument
of Lemma 14.9; `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The order of the direct product T = PU. -/
public theorem LocalGeometry.card_T (g : LocalGeometry Z M z t m) :
    Nat.card g.T = (2 ^ (2 * m + 1)) ^ 2 * Nat.card g.U := by
  have hc := card_set_mul_mul_card_inf (borelTwoCore M z t) g.U
  rw [← g.T_product, g.P_disjoint_U.eq_bot, card_bot, mul_one, g.P_card] at hc
  exact hc

/-- The actual ambient Sylow subgroup has order q³|U|. -/
public theorem Context.card_S (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) :
    Nat.card g.S = (2 ^ (2 * m + 1)) ^ 3 * Nat.card g.U := by
  let := s.T_normal
  obtain ⟨e⟩ := s.quotient_equiv
  have hc := (g.T.subgroupOf g.S).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe g.T_lt_S.le).toEquiv,
    index_eq_card, Nat.card_congr e.toEquiv, (d.closure_elementary_card g).2,
    g.card_T] at hc
  rw [← hc]
  ring

/-- The image of S in M/M° has order q²|U|. -/
public theorem Context.card_quotient_S (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) :
    let A := closure (Z ∩ (M : Set G))
    letI : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
    Nat.card ((g.S.subgroupOf M).map (QuotientGroup.mk' (A.subgroupOf M))) =
      (2 ^ (2 * m + 1)) ^ 2 * Nat.card g.U := by
  let A := closure (Z ∩ (M : Set G))
  let : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  let pi := QuotientGroup.mk' (A.subgroupOf M)
  let SM := g.S.subgroupOf M
  let f := pi.comp SM.subtype
  have hr : f.range = SM.map pi := by
    change (pi.comp SM.subtype).range = _
    rw [MonoidHom.range_comp, range_subtype]
  have hk : f.ker = (A.subgroupOf M).subgroupOf SM := by
    ext x
    exact QuotientGroup.eq_one_iff _
  have hkcard : Nat.card f.ker = Nat.card A := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe
      (subgroupOf_mono M g.closure_le_S)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe distinguishedClosure_le).toEquiv]
  have hc := f.ker.card_mul_index
  rw [index_ker, hkcard, hr,
    Nat.card_congr (subgroupOfEquivOfLe g.S_le_M).toEquiv,
    (d.closure_elementary_card g).2, d.card_S g s] at hc
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (by omega : 0 < 2) (2 * m + 1))
  change 2 ^ (2 * m + 1) * Nat.card (SM.map pi) = _
  rw [hc]
  ring

end BenderSuzuki.ZD.SuzukiExclusion

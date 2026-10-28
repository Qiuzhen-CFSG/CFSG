module

public import Theory.GroupAction.BinaryCyclicInvolution
public import Theory.Representation.InvertedOddSupportRank

/-!
# Involutions on small binary supports

These are the rank and equality arguments in Aschbacher--Smith,
*The Classification of Quasithin Groups*, D.2.11, printed p.183.
The action is explicit and faithful, and rank statements use the equivalent
orders of elementary abelian two-groups. No action-ratio definitions are needed.

Coprime action splits off the odd element's support. Inversion makes its
order the square of the involution displacement on that support. Equality
in the resulting bound forces the involution to fix the complementary
fixed space, and faithfulness then gives the centralizer conclusion.
-/

namespace CFSG.Quasithin.ChapterD

private theorem inverts_zpowers {G : Type*} [Group G] (x t : G)
    (hinv : t * x * t⁻¹ = x⁻¹) :
    ∀ r ∈ Subgroup.zpowers x, t * r * t⁻¹ = r⁻¹ := by
  intro r hr
  obtain ⟨z, rfl⟩ := hr
  rw [← conj_zpow, hinv, inv_zpow]

private theorem cyclic_support_ne_bot_of_faithful
    {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    (x : G) (hx : x ≠ 1) (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    commutatorAction (Subgroup.zpowers x) V ≠ ⊥ := by
  intro hbot
  have htrivial := actsTrivially_of_commutatorAction_eq_bot hbot
  have hfix : x ∈ fixingSubgroup G (Set.univ : Set V) := by
    rw [mem_fixingSubgroup_iff]
    intro v _
    exact htrivial ⟨x, Subgroup.mem_zpowers x⟩ v
  rw [hfaith] at hfix
  exact hx hfix

/-- Identity (*) in D.2.11, with both of its subgroup containments. -/
public theorem invertedOddElement_support_card_data
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x t : G) (hodd : Odd (orderOf x)) (ht : IsInvolution t)
    (hinv : t * x * t⁻¹ = x⁻¹) :
    Nat.card (commutatorAction (Subgroup.zpowers x) V) =
      Nat.card (commutatorSubgroup (Subgroup.zpowers t) V
        (commutatorAction (Subgroup.zpowers x) V)) ^ 2 ∧
    commutatorSubgroup (Subgroup.zpowers t) V
        (commutatorAction (Subgroup.zpowers x) V) ≤
      commutatorAction (Subgroup.zpowers x) V ∧
    commutatorSubgroup (Subgroup.zpowers t) V
        (commutatorAction (Subgroup.zpowers x) V) ≤
      commutatorAction (Subgroup.zpowers t) V :=
  invertedOddSubgroup_support_card_data (Subgroup.zpowers x)
    (by simpa only [Nat.card_zpowers] using hodd) t ht (inverts_zpowers x t hinv)

/-- The odd support rank is at most twice the involution support rank. -/
public theorem invertedOddElement_support_card_le_square
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x t : G) (hodd : Odd (orderOf x)) (ht : IsInvolution t)
    (hinv : t * x * t⁻¹ = x⁻¹) :
    Nat.card (commutatorAction (Subgroup.zpowers x) V) ≤
      Nat.card (commutatorAction (Subgroup.zpowers t) V) ^ 2 := by
  obtain ⟨hsquare, _, hle⟩ := invertedOddElement_support_card_data (V := V) x t hodd ht hinv
  rw [hsquare]
  exact Nat.pow_le_pow_left (Subgroup.card_le_of_le hle) 2

/-- The rank-two support assertion of D.2.11(1). The restriction on the
order of x is the separate small-dimensional linear-group argument. -/
public theorem invertedOddElement_support_card_four_of_involution_card_two
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x t : G) (hx : x ≠ 1) (hodd : Odd (orderOf x)) (ht : IsInvolution t)
    (hinv : t * x * t⁻¹ = x⁻¹)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers t) V) = 2)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    Nat.card (commutatorAction (Subgroup.zpowers x) V) = 4 := by
  obtain ⟨hsquare, _, hle⟩ := invertedOddElement_support_card_data (V := V) x t hodd ht hinv
  have hsmall := Subgroup.card_le_of_le hle
  rw [hcard] at hsmall
  have hnontrivial := cyclic_support_ne_bot_of_faithful x hx hfaith
  have hne : Nat.card (commutatorSubgroup (Subgroup.zpowers t) V
      (commutatorAction (Subgroup.zpowers x) V)) ≠ 1 := by
    intro hone
    rw [hone, one_pow] at hsquare
    exact hnontrivial (Subgroup.card_eq_one.mp hsquare)
  have hpos : 0 < Nat.card (commutatorSubgroup (Subgroup.zpowers t) V
      (commutatorAction (Subgroup.zpowers x) V)) := Nat.card_pos
  have heq : Nat.card (commutatorSubgroup (Subgroup.zpowers t) V
      (commutatorAction (Subgroup.zpowers x) V)) = 2 := by omega
  norm_num [hsquare, heq]

/-- An involution with support rank at most two inverts only odd elements
whose support has rank two or four. -/
public theorem invertedOddElement_support_card_four_or_sixteen
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x t : G) (hx : x ≠ 1) (hodd : Odd (orderOf x)) (ht : IsInvolution t)
    (hinv : t * x * t⁻¹ = x⁻¹)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers t) V) ≤ 4)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    Nat.card (commutatorAction (Subgroup.zpowers x) V) = 4 ∨
      Nat.card (commutatorAction (Subgroup.zpowers x) V) = 16 := by
  obtain ⟨hsquare, _, hle⟩ := invertedOddElement_support_card_data (V := V) x t hodd ht hinv
  let E := commutatorSubgroup (Subgroup.zpowers t) V (commutatorAction (Subgroup.zpowers x) V)
  have hsmall : Nat.card E ≤ 4 := (Subgroup.card_le_of_le hle).trans hcard
  have hnontrivial := cyclic_support_ne_bot_of_faithful x hx hfaith
  have hne : Nat.card E ≠ 1 := by
    intro hone
    change Nat.card (commutatorAction (Subgroup.zpowers x) V) = Nat.card E ^ 2 at hsquare
    rw [hone, one_pow] at hsquare
    exact hnontrivial (Subgroup.card_eq_one.mp hsquare)
  have heven : 2 ∣ Nat.card E :=
    ((IsElementaryAbelian.isPGroup 2 V).to_subgroup E).card_eq_or_dvd.resolve_left hne
  have hpos : 0 < Nat.card E := Nat.card_pos
  have hcases : Nat.card E = 2 ∨ Nat.card E = 4 := by
    obtain ⟨n, hn⟩ := heven
    omega
  change Nat.card (commutatorAction (Subgroup.zpowers x) V) = Nat.card E ^ 2 at hsquare
  rcases hcases with htwo | hfour
  · left
    norm_num [htwo] at hsquare
    exact hsquare
  · right
    norm_num [hfour] at hsquare
    exact hsquare

/-- D.2.11(3): equality of support ranks gives equality of displacements,
fixation of C_V(x), and centralization of C_G(x) ∩ C_G([V,x]). -/
public theorem invertedOddElement_full_support
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x t : G) (hodd : Odd (orderOf x)) (ht : IsInvolution t)
    (hinv : t * x * t⁻¹ = x⁻¹)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers x) V) =
      Nat.card (commutatorAction (Subgroup.zpowers t) V) ^ 2)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    commutatorAction (Subgroup.zpowers t) V =
      commutatorSubgroup (Subgroup.zpowers t) V (commutatorAction (Subgroup.zpowers x) V) ∧
    (∀ v ∈ FixedPoints.subgroup (Subgroup.zpowers x) V, t • v = v) ∧
    ∀ y : G, Commute y x →
      (∀ v ∈ commutatorAction (Subgroup.zpowers x) V, y • v = v) → Commute y t := by
  obtain ⟨heq, hfix, hcentral⟩ := invertedOddSubgroup_full_support (Subgroup.zpowers x)
    (by simpa only [Nat.card_zpowers] using hodd) t ht (inverts_zpowers x t hinv) hcard hfaith
  refine ⟨heq, hfix, fun y hy => hcentral y ?_⟩
  intro r hr
  obtain ⟨z, rfl⟩ := hr
  exact hy.zpow_right z

end CFSG.Quasithin.ChapterD

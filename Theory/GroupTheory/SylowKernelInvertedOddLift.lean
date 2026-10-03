module

public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.InvertedOddLift
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# Inverted odd lifts normalizing a Sylow-kernel intersection

Let a finite group map onto a group of order six with trivial two-core.
An involution in a supplied Sylow two-subgroup with nontrivial image inverts
an odd-order element whose image has order three. The lift can be chosen to
normalize the intersection of that Sylow subgroup with the kernel, without
any restriction on the kernel's order.

The intersection is the ambient image of a Sylow subgroup of the kernel.
Frattini's argument makes its normalizer surject onto the quotient, and the
supplied involution belongs to this normalizer. Identify the quotient with
`Equiv.Perm (Fin 3)` using the action on three Sylow cosets, then apply odd
extraction from a product of involutions inside the normalizer.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, printed p.388,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup

/-- Frattini makes the normalizer of a Sylow-kernel intersection surject onto
the image, for every prime and with no hypothesis on the kernel. -/
public theorem Sylow.surjective_normalizer_inf_ker
    {H K : Type*} [Group H] [Finite H] [Group K]
    {p : ℕ} [Fact p.Prime] (P : Sylow p H)
    (f : H →* K) (hf : Function.Surjective f) :
    Function.Surjective (f.comp (normalizer (((P : Subgroup H) ⊓ f.ker : Subgroup H) : Set H)).subtype) := by
  obtain ⟨Q, hQ⟩ := P.exists_sylow_map_eq_inf_of_normal f.ker
  have hfr : normalizer (((P : Subgroup H) ⊓ f.ker : Subgroup H) : Set H) ⊔ f.ker = ⊤ := by
    simpa only [hQ] using Q.normalizer_sup_eq_top
  intro k
  obtain ⟨h, rfl⟩ := hf k
  obtain ⟨n, hn, z, hz, hnz⟩ := mem_sup_of_normal_right.mp
    (show h ∈ normalizer (((P : Subgroup H) ⊓ f.ker : Subgroup H) : Set H) ⊔ f.ker by rw [hfr]; trivial)
  refine ⟨⟨n, hn⟩, ?_⟩
  change f n = f h
  rw [← hnz, map_mul, (show f z = 1 from hz), mul_one]

/-- An involution above the symmetric group on three letters inverts an odd
lift with order-three image, within the Sylow-kernel normalizer. -/
public theorem Sylow.exists_inverted_odd_normalizing_inf_ker_of_surjective_perm_three
    {H : Type*} [Group H] [Finite H]
    (P : Sylow 2 H) (f : H →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (w : H) (hwP : w ∈ (P : Subgroup H)) (hw : w ^ 2 = 1) (hfw : f w ≠ 1) :
    ∃ r : H, r ∈ normalizer (((P : Subgroup H) ⊓ f.ker : Subgroup H) : Set H) ∧
      Odd (orderOf r) ∧ orderOf (f r) = 3 ∧ w * r * w⁻¹ = r⁻¹ := by
  let N := normalizer (((P : Subgroup H) ⊓ f.ker : Subgroup H) : Set H)
  have hwN : w ∈ N := inf_normalizer_le_normalizer_inf
    ⟨le_normalizer hwP, subset_normalizer_of_normal (Set.mem_univ w)⟩
  obtain ⟨r, hro, hfr, hinv⟩ := exists_inverted_odd_of_surjective_perm_three
    (f.comp N.subtype) (P.surjective_normalizer_inf_ker f hf) ⟨w, hwN⟩
    (Subtype.ext hw) hfw
  refine ⟨r, r.property, ?_, hfr, ?_⟩
  · change Odd (orderOf (N.subtype r))
    rwa [orderOf_injective N.subtype Subtype.coe_injective]
  · exact congrArg Subtype.val hinv

/-- A group of order six with trivial two-core is the symmetric group on
three letters, via the index-three Sylow coset action. -/
public theorem nonempty_mulEquiv_perm_three_of_card_six_core_eq_bot
    {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 6) (hcore : pCore 2 K = ⊥) :
    Nonempty (K ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := K)
  have hS : Nat.card (S : Subgroup K) = 2 := by
    rw [S.card_eq_multiplicity, hK]
    decide +kernel
  have hi : (S : Subgroup K).index = 3 := by
    have hc := (S : Subgroup K).index_mul_card
    rw [hS, hK] at hc
    omega
  have hproper : pCore 2 K < (S : Subgroup K) := by
    rw [hcore, bot_lt_iff_ne_bot]
    exact (one_lt_card_iff_ne_bot _).mp (by omega)
  obtain ⟨e⟩ := sylow_index_three_core_quotient S hi hproper
  exact ⟨QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hcore).symm.trans e)⟩

/-- An involution above a two-core-free group of order six inverts an odd
lift of an element of order three, normalizing the Sylow-kernel intersection. -/
public theorem Sylow.exists_inverted_odd_normalizing_inf_ker_of_card_six
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    (P : Sylow 2 H) (f : H →* K) (hf : Function.Surjective f)
    (hK : Nat.card K = 6) (hcore : pCore 2 K = ⊥)
    (w : H) (hwP : w ∈ (P : Subgroup H)) (hw : w ^ 2 = 1) (hfw : f w ≠ 1) :
    ∃ r : H, r ∈ normalizer (((P : Subgroup H) ⊓ f.ker : Subgroup H) : Set H) ∧
      Odd (orderOf r) ∧ orderOf (f r) = 3 ∧ w * r * w⁻¹ = r⁻¹ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_perm_three_of_card_six_core_eq_bot hK hcore
  let g := e.toMonoidHom.comp f
  have hker : g.ker = f.ker := by
    ext x
    change e (f x) = 1 ↔ f x = 1
    exact e.map_eq_one_iff
  have hgw : g w ≠ 1 := by
    change e (f w) ≠ 1
    exact fun h => hfw (e.map_eq_one_iff.mp h)
  obtain ⟨r, hr, hro, hgr, hinv⟩ :=
    P.exists_inverted_odd_normalizing_inf_ker_of_surjective_perm_three g
      (e.surjective.comp hf) w hwP hw hgw
  refine ⟨r, ?_, hro, ?_, hinv⟩
  · rwa [hker] at hr
  · change orderOf (e (f r)) = 3 at hgr
    rwa [e.orderOf_eq] at hgr

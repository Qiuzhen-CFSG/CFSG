module

public import Theory.GroupTheory.PrimeRankProduct
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupAction.SubgroupConjugation


/-!
# Two-rank in a central product of conjugate factors

If an elementary central kernel admits involutory lifts, the full preimage
of an elementary quotient subgroup is elementary. A vector-space complement
to the kernel has the same order as that quotient subgroup. For two commuting
conjugate factors, these complements intersect trivially, since the factor
intersection lies in the center. Their join gives twice the quotient rank,
even when the factors themselves have nontrivial intersection.

A second lemma shows that a commuting product of conjugate centerless factors
is centerless. These are the central-product steps in Aschbacher–Smith,
16.3.9, combined manuscript of 1 March 2004, printed p.1180.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

/-- A maximal elementary quotient subgroup lifts to a subgroup disjoint from the kernel. -/
theorem exists_elementary_disjoint_kernel_of_involution_lifts {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N ≤ center G) [IsElementaryAbelian 2 N]
    (hlift : ∀ x : G ⧸ N, x ^ 2 = 1 →
      ∃ y : G, QuotientGroup.mk' N y = x ∧ y ^ 2 = 1) :
    ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ Disjoint A N ∧
      Nat.card A = 2 ^ primeRank 2 (G ⧸ N) := by
  obtain ⟨E, hE, hEc⟩ := exists_elementaryAbelian_card_primeRank (G := G ⧸ N) (p := 2)
  let := hE
  let q := QuotientGroup.mk' N
  let P := E.comap q
  let : IsElementaryAbelian 2 P :=
    IsElementaryAbelian.comap_quotient_of_central_involution_lifts N hN E
      (fun x _ hx => hlift x hx)
  let f : P →* E := q.restrict (fun _ hx => hx)
  have hf : Function.Surjective f := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N e
    exact ⟨⟨x, by change q x ∈ E; rw [hx]; exact e.property⟩, Subtype.ext hx⟩
  obtain ⟨B, hB⟩ := IsElementaryAbelian.exists_isCompl 2 P f.ker
  let fB := f.comp B.subtype
  have hi : Function.Injective fB := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    exact Subtype.ext (disjoint_def.mp hB.disjoint hx x.property)
  have hs : Function.Surjective fB := by
    change Function.Surjective (f.comp B.subtype)
    apply MonoidHom.range_eq_top.mp
    have he := congrArg (Subgroup.map f) hB.sup_eq_top
    simpa only [Subgroup.map_sup, Subgroup.map_ker_self, bot_sup_eq,
      ← MonoidHom.range_eq_map, MonoidHom.range_comp, range_subtype,
      MonoidHom.range_eq_top.mpr hf] using he
  let A := B.map P.subtype
  let : IsElementaryAbelian 2 B := { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 P) x) }
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map P.subtype
  refine ⟨A, inferInstance, ?_, ?_⟩
  · apply disjoint_def.mpr
    rintro x ⟨b, hb, rfl⟩ hn
    have hk : b ∈ f.ker := by
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr hn
    exact congrArg Subtype.val (disjoint_def.mp hB.disjoint hk hb)
  · rw [card_map_of_injective Subtype.val_injective]
    exact (Nat.card_congr (MulEquiv.ofBijective fB ⟨hi, hs⟩).toEquiv).trans hEc



/-- Commuting conjugate central covers contribute twice their quotient two-rank. -/
theorem Subgroup.two_rank_conjugate_join_ge {G : Type*} [Group G] [Finite G]
    (J : Subgroup G) (z : G)
    (hcomm : J ≤ centralizer (J.conjBy z : Set G))
    [IsElementaryAbelian 2 (center J)]
    (hlift : ∀ x : J ⧸ center J, x ^ 2 = 1 →
      ∃ y : J, QuotientGroup.mk' (center J) y = x ∧ y ^ 2 = 1) :
    2 * primeRank 2 (J ⧸ center J) ≤ primeRank 2 (J ⊔ J.conjBy z : Subgroup G) := by
  obtain ⟨A, hA, hd, hcard⟩ := exists_elementary_disjoint_kernel_of_involution_lifts (center J) le_rfl hlift
  let := hA
  let E := A.map J.subtype
  have hEJ : E ≤ J := map_subtype_le A
  have hEq : primeRank 2 E = primeRank 2 (J ⧸ center J) := by
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.map J.subtype
    have hc : Nat.card E = 2 ^ primeRank 2 (J ⧸ center J) := by
      rw [card_map_of_injective Subtype.val_injective]
      exact hcard
    let : CommGroup E := IsMulCommutative.instCommGroup
    exact le_antisymm (IsElementaryAbelian.primeRank_le_of_card_le E hc.le)
      (primeRank_ge_of_elementary_embedding
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E))
        hc (MonoidHom.id E) Function.injective_id)
  have hdis : Disjoint E (E.conjBy z) := by
    apply disjoint_def.mpr
    intro x hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    have hyJ : (a : G) ∈ J.conjBy z := map_mono hEJ hy
    have haz : a ∈ center J := by
      apply mem_center_iff.mpr
      intro j
      apply Subtype.ext
      exact (hcomm j.property a hyJ).symm
    exact congrArg Subtype.val (disjoint_def.mp hd ha haz)
  have hcommE : E ≤ centralizer (E.conjBy z : Set G) := by
    exact hEJ.trans (hcomm.trans (centralizer_le (show (E.conjBy z : Set G) ⊆ J.conjBy z from map_mono hEJ)))
  have hr := E.primeRank_sup_eq_add_of_disjoint_commuting (E.conjBy z) hdis hcommE 2
  have hconj : primeRank 2 (E.conjBy z) = primeRank 2 E :=
    (primeRank_equiv 2 ((MulAut.conj z).subgroupMap E)).symm
  have hle : E ⊔ E.conjBy z ≤ J ⊔ J.conjBy z := sup_le_sup hEJ (map_mono hEJ)
  have hi := primeRank_le_of_injective 2 (inclusion hle) (inclusion_injective hle)
  rw [hr, hconj, hEq] at hi
  omega

private theorem center_bot_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : center A = ⊥) : center B = ⊥ := by
  apply eq_bot_iff.mpr
  intro b hb
  let hc := (centerCongr e).symm ⟨b, hb⟩
  have he : hc = 1 := by
    apply Subtype.ext
    exact mem_bot.mp (h ▸ hc.property)
  have hf := congrArg (centerCongr e) he
  have hb1 : (⟨b, hb⟩ : center B) = 1 := by simpa [hc] using hf
  exact congrArg Subtype.val hb1

/-- A commuting join of conjugate centerless factors is centerless. -/
theorem Subgroup.center_conjugate_join_eq_bot {G : Type*} [Group G] (J : Subgroup G) (z : G)
    (hcomm : J ≤ centralizer (J.conjBy z : Set G))
    (hZ : center J = ⊥) : center (J ⊔ J.conjBy z : Subgroup G) = ⊥ := by
  have hdis : Disjoint J (J.conjBy z) := by
    apply disjoint_def.mpr
    intro x hx hy
    have hc : (⟨x,hx⟩ : J) ∈ center J := by
      apply mem_center_iff.mpr
      intro j
      exact Subtype.ext (hcomm j.property x hy).symm
    exact congrArg (fun j : J => (j : G)) (show (⟨x,hx⟩ : J) = 1 from mem_bot.mp (hZ ▸ hc))
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting J (J.conjBy z) hdis hcomm
  apply center_bot_equiv e
  have hZ2 : center (J.conjBy z) = ⊥ := center_bot_equiv ((MulAut.conj z).subgroupMap J) hZ
  rw [Subgroup.center_prod, hZ, hZ2]
  exact bot_prod_bot

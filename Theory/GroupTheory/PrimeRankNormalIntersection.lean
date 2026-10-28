module
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupAction.SubgroupCentralizerCongruence
/-!
# Normal intersections in groups of prime rank at most two

An elementary abelian subgroup E of order p² must meet every normal
subgroup K whose order is divisible by p. Otherwise the conjugation action
of E on K has a centralizer of order divisible by p. A Cauchy element in
that centralizer joins E to an elementary subgroup of order p³.

Consequently an external line X of E generates E modulo K. The last
lemma combines this intersection argument with Sylow transport through
coprime kernels: an elementary plane quotient is generated modulo K by
its normal external line and the image of the quotient kernel.

This is the elementary prime-rank argument used in the external case of
Aschbacher–Smith, The Classification of Quasithin Groups, 13.8.20, p.954.
-/

public section
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A normalizing elementary plane meets every p-divisible subgroup in
an ambient group of p-rank at most two. -/
theorem Subgroup.inf_ne_bot_of_elementary_plane (E K : Subgroup G) [IsElementaryAbelian p E]
    (hn : E ≤ normalizer (K : Set G)) (hK : p ∣ Nat.card K)
    (hE : Nat.card E = p ^ 2) (hr : primeRank p G ≤ 2) : E ⊓ K ≠ ⊥ := by
  intro hbot
  have hmod := card_modEq_card_inf_centralizer E K (IsElementaryAbelian.isPGroup p E) hn
  have hd : p ∣ Nat.card (K ⊓ centralizer (E : Set G) : Subgroup G) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans hK.modEq_zero_nat)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
  have hxG : orderOf (x : G) = p :=
    (orderOf_injective (K ⊓ centralizer (E : Set G)).subtype Subtype.val_injective x).trans hx
  have hnot : (x : G) ∉ E := by
    intro hxE
    have he := hbot.le ⟨hxE, x.property.1⟩
    have ho : orderOf (x : G) = 1 := (mem_bot.mp he) ▸ orderOf_one
    have := (Fact.out : p.Prime).one_lt
    omega
  have hfix : E ≤ centralizer ({(x : G)} : Set G) := by
    intro e he
    exact mem_centralizer_singleton_iff.mpr (x.property.2 e he)
  have h := IsElementaryAbelian.primeRank_ge_of_fixed_join E x hxG hnot hfix hE
  omega


/-- An external line of an elementary plane generates that plane modulo
a p-divisible normalized subgroup when the ambient p-rank is at most two. -/
theorem Subgroup.elementary_plane_le_sup_of_external_line (E K X : Subgroup G) [IsElementaryAbelian p E]
    (hn : E ≤ normalizer (K : Set G)) (hK : p ∣ Nat.card K)
    (hE : Nat.card E = p ^ 2) (hr : primeRank p G ≤ 2)
    (hXE : X ≤ E) (hX : Nat.card X = p) (hXK : ¬ X ≤ K) : E ≤ K ⊔ X := by
  have hp := (Fact.out : p.Prime)
  have hne := Subgroup.inf_ne_bot_of_elementary_plane E K hn hK hE hr
  have hd : Nat.card (E ⊓ K : Subgroup G) ∣ p ^ 2 := hE ▸ card_dvd_of_le inf_le_left
  obtain ⟨j, hj, he⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hjpos : 1 ≤ j := by
    by_contra hjpos
    have hz : j = 0 := by omega
    exact hne (card_eq_one.mp (by simpa [hz] using he))
  have hsize : p ≤ Nat.card (E ⊓ K : Subgroup G) := by
    rw [he]
    simpa using Nat.pow_le_pow_right hp.pos hjpos
  have hdis : Disjoint (E ⊓ K) X := by
    have hdvd : Nat.card ((E ⊓ K) ⊓ X : Subgroup G) ∣ p :=
      hX ▸ card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · exact disjoint_iff.mpr (card_eq_one.mp h1)
    · have heq : (E ⊓ K) ⊓ X = X := eq_of_le_of_card_ge inf_le_right (by omega)
      exact (hXK (heq.symm.le.trans (inf_le_left.trans inf_le_right))).elim
  have hc : X ≤ centralizer ((E ⊓ K : Subgroup G) : Set G) := by
    intro x hx a ha
    exact congrArg Subtype.val (mul_comm' (⟨a, ha.1⟩ : E) ⟨x, hXE hx⟩)
  have heq : E ⊓ K ⊔ X = E := by
    apply eq_of_le_of_card_ge (sup_le inf_le_left hXE)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (hc.trans (centralizer_le_normalizer _)) hdis, hX, hE, pow_two]
    exact Nat.mul_le_mul_right p hsize
  rw [← heq]
  exact sup_le_sup inf_le_right le_rfl

-- A Sylow subgroup maps isomorphically to an elementary quotient with coprime kernel.
private theorem sylow_elementary_of_quotient (N : Subgroup G) [N.Normal]
    [IsElementaryAbelian p (G ⧸ N)] (hc : Nat.Coprime p (Nat.card N))
    (S : Sylow p G) : IsElementaryAbelian p S ∧ Nat.card S = Nat.card (G ⧸ N) ∧
      N ⊔ (S : Subgroup G) = ⊤ := by
  let q := QuotientGroup.mk' N
  have hmap : (S : Subgroup G).map q = ⊤ :=
    top_unique (((IsElementaryAbelian.isPGroup p (G ⧸ N)).to_subgroup ⊤).le_sylow_of_normal
      (S.mapSurjective (QuotientGroup.mk'_surjective N)))
  let m := q.comp (S : Subgroup G).subtype
  have hi : Function.Injective m := injective_comp_subtype_of_coprime_ker q
    (by simpa [q] using hc) S S.isPGroup'
  have hs : Function.Surjective m := by
    intro y
    have hy : y ∈ (S : Subgroup G).map q := hmap ▸ mem_top y
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x,hx⟩, hxy⟩
  let e := MulEquiv.ofBijective m ⟨hi,hs⟩
  have hel : IsElementaryAbelian p S := {
    toIsMulCommutative := ⟨⟨fun x y => hi (by
      simp only [map_mul]
      exact mul_comm' _ _)⟩⟩
    exponent_dvd_p := by
      rw [Monoid.exponent_eq_of_mulEquiv e]
      exact IsElementaryAbelian.exponent_dvd_p p (G ⧸ N) }
  refine ⟨hel, Nat.card_congr e.toEquiv, ?_⟩
  have h := congrArg (Subgroup.comap q) hmap
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top, sup_comm] using h

private theorem sylow_image_contains_normal {J : Type*} [Group J]
    (f : G →* J) (S : Sylow p G) (X : Subgroup J) [X.Normal]
    (hX : IsPGroup p X) (hXR : X ≤ f.range) : X ≤ (S : Subgroup G).map f := by
  let R := f.range
  let S' : Sylow p R := S.mapSurjective f.rangeRestrict_surjective
  have hh : X.subgroupOf R ≤ (S' : Subgroup R) := hX.comap_subtype.le_sylow_of_normal S'
  have hm := map_mono (f := R.subtype) hh
  rw [map_subgroupOf_eq_of_le hXR] at hm
  simpa only [S', Sylow.coe_mapSurjective, map_map, R, MonoidHom.subtype_comp_rangeRestrict] using hm


/-- In rank two, an elementary plane modulo a prime-to-p normal subgroup
is generated modulo K by its normal external line. -/
theorem MonoidHom.range_le_sup_of_elementary_plane_quotient {J : Type*} [Group J] [Finite J]
    (N : Subgroup G) [N.Normal] [IsElementaryAbelian p (G ⧸ N)]
    (hN : Nat.Coprime p (Nat.card N)) (hcard : Nat.card (G ⧸ N) = p ^ 2)
    (f : G →* J) (hf : Nat.Coprime p (Nat.card f.ker))
    (K X P : Subgroup J) [K.Normal] [X.Normal]
    (hK : p ∣ Nat.card K) (hr : primeRank p J ≤ 2)
    (hX : Nat.card X = p) (hXR : X ≤ f.range) (hXK : ¬ X ≤ K)
    (hNP : N.map f ≤ P) : f.range ≤ K ⊔ (X ⊔ P) := by
  let S : Sylow p G := Sylow.nonempty.some
  obtain ⟨hS, hcS, hgen⟩ := sylow_elementary_of_quotient N hN S
  let : IsElementaryAbelian p S := hS
  let E := (S : Subgroup G).map f
  let : IsElementaryAbelian p E := IsElementaryAbelian.map f
  let m := f.comp (S : Subgroup G).subtype
  have hi : Function.Injective m := injective_comp_subtype_of_coprime_ker f hf S S.isPGroup'
  have he : m.range = E := by rw [MonoidHom.range_comp, range_subtype]
  have hcE : Nat.card E = p ^ 2 := by
    rw [← he]
    exact (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans (hcS.trans hcard)
  have hXE : X ≤ E := sylow_image_contains_normal f S X
    (IsPGroup.iff_card.mpr ⟨1, by simpa using hX⟩) hXR
  have hEKX : E ≤ K ⊔ X := Subgroup.elementary_plane_le_sup_of_external_line E K X (by rw [normalizer_eq_top]; exact le_top) hK hcE hr hXE hX hXK
  have hm := congrArg (Subgroup.map f) hgen
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map] at hm
  rw [← hm]
  exact sup_le (hNP.trans (le_sup_right.trans le_sup_right))
    (hEKX.trans (sup_le le_sup_left (le_sup_left.trans le_sup_right)))

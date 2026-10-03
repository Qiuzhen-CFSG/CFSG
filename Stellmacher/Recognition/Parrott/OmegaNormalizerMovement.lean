module
public import Stellmacher.Recognition.Parrott.OuterCentralizerOmega
public import Mathlib.GroupTheory.Nilpotent

/-!
# The omega normalizer moves Parrott's central involution

Let H=C_G(z) satisfy the original Parrott hypotheses. For an involution
y in H outside its two-core J that is conjugate to z in G, put
P=C_H(y) and let X be the actual ambient image of Ω₁(P). Then N_G(X) is
not contained in H. No simplicity or N₂ hypothesis is required.

The outer-centralizer theorem makes P a two-group. A Sylow two-subgroup
of H containing P also contains J, whereas J cannot centralize y because
y fixes only eight of the thirty-two elements of E. Thus P is smaller
than a Sylow two-subgroup of H. Conjugacy gives equal centralizer orders
for z and y, so P is also smaller than a Sylow two-subgroup of C_G(y).
The finite nilpotent normalizer condition supplies an element of C_G(y)
normalizing the mapped P but outside it. Such an element lies outside H,
since C_G(y) intersected with H is that mapped P. Conjugation preserves
the order-two generators of its mapped omega subgroup, so it normalizes X.

Source: David Parrott, *A characterization of the Tits' simple group*
(1972), Lemma 3, p.675, and Lemma 5, p.676, the normalizer enlargement. All centralizers,
subgroups, and ambient embeddings are the original constructions.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- The mapped omega of a fused outer involution centralizer has a normalizer
outside H, without a restriction on the core involutions. -/
public theorem parrott_outer_omega_normalizer_not_le_centralizer
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ y : H, orderOf y = 2 → y ∉ J → IsConj z (y : G) →
      let P := centralizer ({y} : Set H)
      let X := (omega₁ P (p := 2)).map (H.subtype.comp P.subtype)
      ¬ normalizer (X : Set G) ≤ H := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  change ∀ y : H, orderOf y = 2 → y ∉ J → IsConj z (y : G) → _
  intro y hy hyJ hconj
  let P := centralizer ({y} : Set H)
  let embed : P →* G := H.subtype.comp P.subtype
  let X := (omega₁ P (p := 2)).map embed
  let C := centralizer ({(y : G)} : Set G)
  let R := P.map H.subtype
  change ¬ normalizer (X : Set G) ≤ H
  have hembed : Function.Injective embed := H.subtype_injective.comp P.subtype_injective
  have hPp : IsPGroup 2 P := parrott_outer_centralizer_isPGroup z h y hy hyJ
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (K := commutator J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans
        (parrott_centralizer_structure z h).2.2.2.2.2.2.1
  have hJnot : ¬ J ≤ P := by
    intro hJP
    have hEC : E ≤ C := by
      rintro x ⟨d, _, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg H.subtype (mem_centralizer_singleton_iff.mp (hJP d.property))
    have hfixed := parrott_outer_involution_fixed_card z h y hy hyJ
    have htop : C.subgroupOf E = ⊤ := subgroupOf_eq_top.mpr hEC
    change Nat.card (C.subgroupOf E) = 8 at hfixed
    rw [htop, card_top, hEcard] at hfixed
    omega
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  have hJS : J ≤ (S : Subgroup H) := pCore_isPGroup.le_sylow_of_normal S
  have hPlt : Nat.card P < Nat.card S := by
    by_contra hlt
    have heq : P = (S : Subgroup H) := eq_of_le_of_card_ge hPS (Nat.le_of_not_gt hlt)
    exact hJnot (heq ▸ hJS)
  have hCcard : Nat.card C = Nat.card H := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    let f : G ≃* G := MulAut.conj c
    have hfz : f z = (y : G) := hc
    apply (Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)).symm
    intro a
    change a ∈ centralizer ({z} : Set G) ↔ f a ∈ centralizer ({(y : G)} : Set G)
    simp only [mem_centralizer_singleton_iff]
    constructor
    · intro ha
      simpa only [map_mul, hfz] using congrArg f ha
    · intro ha
      apply f.injective
      simpa only [map_mul, hfz] using ha
  have hRC : R ≤ C := by
    rintro a ⟨b, hb, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg H.subtype (mem_centralizer_singleton_iff.mp hb))
  let K := R.subgroupOf C
  have hKR : K.map C.subtype = R := map_subgroupOf_eq_of_le hRC
  have hKcard : Nat.card K = Nat.card P :=
    (Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv).trans
      (card_map_of_injective H.subtype_injective)
  have hKp : IsPGroup 2 K :=
    (hPp.map H.subtype).of_injective
      (subgroupOfEquivOfLe hRC).toMonoidHom (subgroupOfEquivOfLe hRC).injective
  obtain ⟨T, hKT⟩ := hKp.exists_le_sylow
  have hTcard : Nat.card T = Nat.card S := by
    rw [T.card_eq_multiplicity, S.card_eq_multiplicity, hCcard]
  have hproper : K.subgroupOf (T : Subgroup C) < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    intro hTK
    have hh := card_le_of_le hTK
    rw [hKcard, hTcard] at hh
    omega
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent
    (K.subgroupOf (T : Subgroup C)) hproper
  obtain ⟨u, huN, huK⟩ := SetLike.exists_of_lt hlt
  have huNK : (u : C) ∈ normalizer (K : Set C) := by
    rw [← subgroupOf_normalizer_eq hKT] at huN
    exact huN
  let g : G := ((u : C) : G)
  have hgR : g ∈ normalizer (R : Set G) := by
    rw [← hKR]
    exact K.le_normalizer_map C.subtype (mem_map_of_mem C.subtype huNK)
  have hgnotR : g ∉ R := huK
  have hgnotH : g ∉ H := by
    intro hgH
    apply hgnotR
    refine ⟨⟨g, hgH⟩, ?_, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (u : C).property)
  have hgX : g ∈ normalizer (X : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · change ((omega₁ P (p := 2)).map embed).map (MulAut.conj g).toMonoidHom ≤ X
      rw [map_map, map_le_iff_le_comap]
      change closure {a : P | a ^ (2 ^ 1) = 1} ≤
        X.comap ((MulAut.conj g).toMonoidHom.comp embed)
      refine (closure_le _).mpr ?_
      intro a ha
      have ha2 : a ^ (2 ^ 1) = 1 := ha
      have hconjR : (MulAut.conj g) (embed a) ∈ R :=
        (hgR (embed a)).mp (mem_map_of_mem H.subtype a.property)
      obtain ⟨b, hb, hbe⟩ := hconjR
      let bP : P := ⟨b, hb⟩
      have hbe' : embed bP = (MulAut.conj g) (embed a) := hbe
      have hb2 : bP ^ (2 ^ 1) = 1 := by
        apply hembed
        rw [map_pow, map_one, hbe', ← map_pow, ← map_pow, ha2, map_one, map_one]
      change (MulAut.conj g) (embed a) ∈ X
      rw [← hbe']
      exact mem_map_of_mem embed (subset_closure hb2)
    · exact (card_map_of_injective (MulAut.conj g).injective).ge
  exact fun hN => hgnotH (hN hgX)

/-- The original Lemma 3 interface, retained for consumers using the
core-involution contradiction hypothesis. -/
public theorem parrott_omega_normalizer_not_le_centralizer
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    (∀ t : G, t ∈ J.map H.subtype → orderOf t = 2 → t ∈ E) →
    ∀ y : H, orderOf y = 2 → y ∉ J → IsConj z (y : G) →
      let P := centralizer ({y} : Set H)
      let X := (omega₁ P (p := 2)).map (H.subtype.comp P.subtype)
      ¬ normalizer (X : Set G) ≤ H := by
  dsimp only
  intro _
  exact parrott_outer_omega_normalizer_not_le_centralizer z h

end Stellmacher.Recognition

module

public import Theory.GroupTheory.ElementaryCommutingCoprime
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Binary commuting components through odd normal quotients

Let N be an odd-order normal subgroup of a finite group H. Suppose H/N
has a normal two-subgroup R containing an elementary binary subgroup D
of order at least eight. Every elementary binary subgroup A of H of order
at least eight is then connected to each of its conjugates in the actual
rank-two elementary commuting graph.

Choose a Sylow two-subgroup S containing A. Its quotient image contains R,
and the quotient map is injective on S because N has odd order. Lift D
inside S to B. The subgroups A and B are connected inside S. Put K equal
to the inverse image of R and P = S ∩ K. Then P is Sylow in K and
K = N P. The odd-subgroup component theorem controls N; the rank-three
vertex B in P makes the full normalizer of P preserve the same component.
Frattini's argument H = K N_H(P) completes the proof.

This combines the component-stabilizer argument in GLS2, Section 22,
Lemma 22.2 (`refs/KGroup/GLS2/ChapterF.tex`) with Sylow restriction and the
normal-subgroup Frattini argument. A normal elementary four-group in the
quotient also suffices: its Sylow lift is normalized by the rank-three actor,
so the action-kernel path replaces rank-three connectivity inside the lift.
No solvability hypothesis is needed.
-/

namespace Subgroup

/-- A normal two-subgroup of elementary rank at least three in an odd normal
quotient forces every conjugate of a rank-three binary subgroup to lie in
its elementary commuting component. -/
public theorem elementaryCommutingConnected_conj_of_normal_odd_quotient
    {H : Type*} [Group H] [Finite H]
    (N A : Subgroup H) [N.Normal] [IsElementaryAbelian 2 A]
    (hN : Odd (Nat.card N)) (hA : 8 ≤ Nat.card A)
    (R D : Subgroup (H ⧸ N)) [R.Normal] (hR : IsPGroup 2 R)
    [IsElementaryAbelian 2 D] (hD : 8 ≤ Nat.card D) (hDR : D ≤ R)
    (g : H) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  let f : S →* H ⧸ N := q.comp (S : Subgroup H).subtype
  have hdisj : Disjoint (S : Subgroup H) N := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact hN.coprime_two_left.pow_left n
  have hfinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have hxN : (x : H) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    exact mem_bot.mp ((disjoint_iff.mp hdisj).le ⟨x.property, hxN⟩)
  have hRrange : R ≤ f.range := by
    rw [MonoidHom.range_comp, range_subtype]
    exact hR.le_sylow_of_normal (S.mapSurjective (QuotientGroup.mk'_surjective N))
  let K := R.comap q
  let P := (R.comap f).map (S : Subgroup H).subtype
  have hP : P = (S : Subgroup H) ⊓ K := by
    change (K.subgroupOf (S : Subgroup H)).map (S : Subgroup H).subtype = _
    rw [subgroupOf_map_subtype, inf_comm]
  have hPS : P ≤ S := map_subtype_le _
  have hPtwo : IsPGroup 2 P := S.isPGroup'.to_le hPS
  have hPmap : P.map q = R := by
    rw [map_map]
    exact map_comap_eq_self hRrange
  have hsup : N ⊔ P = K := by
    have hh := congrArg (Subgroup.comap q) hPmap
    simpa only [q, QuotientGroup.comap_map_mk'] using hh
  let DS := D.comap f
  let e : DS ≃* D := MulEquiv.ofBijective (f.subgroupComap D) (by
    constructor
    · intro x y h
      apply Subtype.ext
      exact hfinj (congrArg Subtype.val h)
    · intro y
      obtain ⟨x, hx⟩ := hRrange (hDR y.property)
      exact ⟨⟨x, by change f x ∈ D; rw [hx]; exact y.property⟩, Subtype.ext hx⟩)
  let : IsElementaryAbelian 2 DS := {
    toIsMulCommutative := D.comap_injective_isMulCommutative hfinj
    exponent_dvd_p := by
      rw [Monoid.exponent_eq_of_mulEquiv e]
      exact IsElementaryAbelian.exponent_dvd_p 2 D }
  let B := DS.map (S : Subgroup H).subtype
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map_subtype
  have hB : 8 ≤ Nat.card B := by
    rw [card_map_of_injective (S : Subgroup H).subtype_injective,
      Nat.card_congr e.toEquiv]
    exact hD
  have hBP : B ≤ P := map_mono (comap_mono hDR)
  have hAB : ElementaryCommutingConnected 2 A B :=
    elementaryCommutingConnected_of_le_twoGroup S A B S.isPGroup' hA hB hAS
      (hBP.trans hPS)
  have hnormalizer : normalizer (P : Set H) ≤
      elementaryCommutingStabilizer 2 A (by omega) := by
    rw [elementaryCommutingStabilizer_eq_of_connected A B (by omega) (by omega) hAB]
    exact normalizer_le_elementaryCommutingStabilizer_of_le_twoGroup P B hPtwo hB hBP
  have hNstab : N ≤ elementaryCommutingStabilizer 2 A (by omega) :=
    odd_le_elementaryCommutingStabilizer_of_normalized A N hA hN (by
      rw [normalizer_eq_top]
      exact le_top)
  have hKstab : K ≤ elementaryCommutingStabilizer 2 A (by omega) := by
    rw [← hsup]
    exact sup_le hNstab (P.le_normalizer.trans hnormalizer)
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal K
  have hTP : (T : Subgroup K).map K.subtype = P := by
    rw [hT, subgroupOf_map_subtype, hP]
  have hfrattini : normalizer (P : Set H) ⊔ K = ⊤ := by
    simpa only [hTP] using T.normalizer_sup_eq_top
  have htop : (⊤ : Subgroup H) ≤ elementaryCommutingStabilizer 2 A (by omega) := by
    rw [← hfrattini]
    exact sup_le hnormalizer hKstab
  exact htop (mem_top g)

/-- A normal elementary four-group in an odd normal quotient suffices for
conjugation invariance of the rank-three commuting component. Its lift to a
Sylow subgroup is a four-group normalized by that Sylow subgroup. -/
public theorem elementaryCommutingConnected_conj_of_normal_four_odd_quotient
    {H : Type*} [Group H] [Finite H]
    (N A : Subgroup H) [N.Normal] [IsElementaryAbelian 2 A]
    (hN : Odd (Nat.card N)) (hA : 8 ≤ Nat.card A)
    (R : Subgroup (H ⧸ N)) [R.Normal] [IsElementaryAbelian 2 R]
    (hRcard : Nat.card R = 4) (g : H) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj g).toMonoidHom) := by
  have hR : IsPGroup 2 R := IsElementaryAbelian.isPGroup 2 R
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  let f : S →* H ⧸ N := q.comp (S : Subgroup H).subtype
  have hdisj : Disjoint (S : Subgroup H) N := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact hN.coprime_two_left.pow_left n
  have hfinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have hxN : (x : H) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    exact mem_bot.mp ((disjoint_iff.mp hdisj).le ⟨x.property, hxN⟩)
  have hRrange : R ≤ f.range := by
    rw [MonoidHom.range_comp, range_subtype]
    exact hR.le_sylow_of_normal (S.mapSurjective (QuotientGroup.mk'_surjective N))
  let K := R.comap q
  let P := (R.comap f).map (S : Subgroup H).subtype
  have hP : P = (S : Subgroup H) ⊓ K := by
    change (K.subgroupOf (S : Subgroup H)).map (S : Subgroup H).subtype = _
    rw [subgroupOf_map_subtype, inf_comm]
  have hPS : P ≤ S := map_subtype_le _
  have hPtwo : IsPGroup 2 P := S.isPGroup'.to_le hPS
  have hPmap : P.map q = R := by
    rw [map_map]
    exact map_comap_eq_self hRrange
  have hsup : N ⊔ P = K := by
    have hh := congrArg (Subgroup.comap q) hPmap
    simpa only [q, QuotientGroup.comap_map_mk'] using hh
  let RP := R.comap f
  let e : RP ≃* R := MulEquiv.ofBijective (f.subgroupComap R) (by
    constructor
    · intro x y h
      apply Subtype.ext
      exact hfinj (congrArg Subtype.val h)
    · intro y
      obtain ⟨x, hx⟩ := hRrange y.property
      exact ⟨⟨x, by change f x ∈ R; rw [hx]; exact y.property⟩, Subtype.ext hx⟩)
  let : IsElementaryAbelian 2 RP := {
    toIsMulCommutative := R.comap_injective_isMulCommutative hfinj
    exponent_dvd_p := by
      rw [Monoid.exponent_eq_of_mulEquiv e]
      exact IsElementaryAbelian.exponent_dvd_p 2 R }
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map_subtype (H := RP)
  have hPcard : Nat.card P = 4 := by
    rw [card_map_of_injective (S : Subgroup H).subtype_injective]
    exact (Nat.card_congr e.toEquiv).trans hRcard
  have hAP : A ≤ normalizer (P : Set H) := by
    rw [hP]
    exact (le_inf (hAS.trans (S : Subgroup H).le_normalizer)
      (le_normalizer_of_normal (H := K))).trans inf_normalizer_le_normalizer_inf
  have hconn : ElementaryCommutingConnected 2 A P :=
    elementaryCommutingConnected_of_normalizes_four A P hA hPcard hAP
  have hnormalizer : normalizer (P : Set H) ≤
      elementaryCommutingStabilizer 2 A (by omega) :=
    normalizer_le_elementaryCommutingStabilizer A P (by omega) hconn
  have hNstab : N ≤ elementaryCommutingStabilizer 2 A (by omega) :=
    odd_le_elementaryCommutingStabilizer_of_normalized A N hA hN (by
      rw [normalizer_eq_top]
      exact le_top)
  have hKstab : K ≤ elementaryCommutingStabilizer 2 A (by omega) := by
    rw [← hsup]
    exact sup_le hNstab (P.le_normalizer.trans hnormalizer)
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal K
  have hTP : (T : Subgroup K).map K.subtype = P := by
    rw [hT, subgroupOf_map_subtype, hP]
  have hfrattini : normalizer (P : Set H) ⊔ K = ⊤ := by
    simpa only [hTP] using T.normalizer_sup_eq_top
  have htop : (⊤ : Subgroup H) ≤ elementaryCommutingStabilizer 2 A (by omega) := by
    rw [← hfrattini]
    exact sup_le hnormalizer hKstab
  exact htop (mem_top g)

end Subgroup

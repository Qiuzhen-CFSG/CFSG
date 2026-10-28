module
public import ABG.ChapterII.Section2.Defs
public import ABG.ChapterII.Section2.QuasiFrameTransport
public import FeitThompson.PCore.PPrimeCore

/-!
# Sylow shape in the odd-core quotient

ABG Chapter II Section 2 Proposition 2 begins by passing a finite QD group
`G` to `G / O(G)` and asserting that its Sylow two-subgroups remain
quasi-dihedral or wreathed. Here `O(G)` is `pPrimeCore 2 G`.

Take the Sylow subgroup supplied by the full QD fusion witness and map it
through the quotient homomorphism. The odd core has cardinality coprime to
two, while the Sylow subgroup has two-power order, so their intersection is
trivial. Thus the quotient map restricts to a multiplicative equivalence from
the original Sylow subgroup to its actual Sylow image. The semidihedral
transport from `QuasiFrameTransport` and the analogous presentation transport
for wreathed groups preserve the required shape. The Sylow quotient
equivalence is also public for the enlarged Q-group odd-core reduction,
where the same shape is supplied independently of a QD fusion witness.

This establishes the Sylow-shape part of the source's reduction. Transport of
the complete QD fusion pattern and the final simple normal subgroup assertion
are separate steps in the Proposition 2 assembly. The wreathed equivalence
transport is public for the normal-subgroup part of that assembly as well,
with independent source and target universes for finite universe reduction.
-/

namespace ABG

universe u

variable {G H : Type*} [Group G] [Group H]

/-- Wreathed presentations transport along multiplicative equivalences. -/
public theorem wreathed_equiv (e : G ≃* H) {n : ℕ} (hG : IsWreathedOfHeight G n) :
    IsWreathedOfHeight H n := by
  obtain ⟨hn, hc, s, t, z, hs, ht, hz, hzs, hzt, hst, hgen⟩ := hG
  refine ⟨hn, (Nat.card_congr e.toEquiv).symm.trans hc, e s, e t, e z,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg e hs
  · simpa using congrArg e ht
  · simpa using congrArg e hz
  · simpa using congrArg e hzs
  · simpa using congrArg e hzt
  · simpa using congrArg e hst
  · have h := congrArg (Subgroup.map e.toMonoidHom) hgen
    simpa only [MonoidHom.map_closure, MulEquiv.coe_toMonoidHom, Set.image_insert_eq,
      Set.image_singleton, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using h

public theorem sylow_quotient_equiv [Finite G] (S : Sylow 2 G) (N : Subgroup G)
    [N.Normal] (hN : Nat.Coprime 2 (Nat.card N)) :
    Nonempty (S ≃* S.mapSurjective (f := QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)) := by
  let q := QuotientGroup.mk' N
  let f := q.comp (S : Subgroup G).subtype
  have hdis : Disjoint (S : Subgroup G) N := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    exact hN.pow_left n
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    have hx1 : (x : G) = 1 := (Subgroup.disjoint_def.mp hdis) x.property hxN
    exact Subtype.ext hx1
  let R : Sylow 2 (G ⧸ N) := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have hrange : f.range = (R : Subgroup (G ⧸ N)) := by
    rw [Sylow.coe_mapSurjective]
    exact (MonoidHom.range_comp q (S : Subgroup G).subtype).trans
      (congrArg (Subgroup.map q) (S : Subgroup G).range_subtype)
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

/-- The odd-core quotient of a finite QD group has an actual quasi-dihedral
or wreathed Sylow two-subgroup. -/
public theorem IsQDGroup.sylow_shape_oddCore_quotient [Finite G]
    (hG : IsQDGroup G) :
    ∃ S : Sylow 2 (G ⧸ pPrimeCore 2 G),
      Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S := by
  let N : Subgroup G := pPrimeCore 2 G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hN : Nat.Coprime 2 (Nat.card N) := pPrimeCore_coprime_card
  rcases hG with ⟨S, T, Q, hframe, _⟩ | ⟨S, n, U, V, hframe, _⟩
  · let R : Sylow 2 (G ⧸ N) :=
      S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
    obtain ⟨e⟩ := sylow_quotient_equiv S N hN
    exact ⟨R, Or.inl (semidihedral_equiv e hframe.1)⟩
  · let R : Sylow 2 (G ⧸ N) :=
      S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
    obtain ⟨e⟩ := sylow_quotient_equiv S N hN
    exact ⟨R, Or.inr ⟨n, wreathed_equiv e hframe.1⟩⟩

end ABG

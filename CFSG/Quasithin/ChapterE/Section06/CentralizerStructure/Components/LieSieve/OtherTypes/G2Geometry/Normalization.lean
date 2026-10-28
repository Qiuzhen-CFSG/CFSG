module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.AtlasPort.LinearGroups.G2.BinaryThreeRank.CubicWitness
public import Theory.AtlasPort.LinearGroups.G2.BinaryFieldEmbedding
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# A three-local criterion for normalization of the G₂ components

The obstruction centralizer has three-rank at most two. If one of its ordinary
components were moved, it would commute with its distinct conjugate. A
nonabelian three-subgroup of the component contains an elementary nine. Every
cubic element in the conjugate component must then belong to the first
component: otherwise it and the nine generate an elementary subgroup of order
27. Such an element centralizes its own component, contradicting a noncentral
cubic in the three-subgroup.

Schur–Zassenhaus lifts an arbitrary three-subgroup through a normal two-group
kernel. Thus the criterion applies to every central two-cover without bounding
its center or replacing it with a selected model.

The three model entry points discharge the intrinsic witness using the actual
G₂(2)′ three-subgroup and the coefficientwise embedding of binary octonion
automorphisms into every characteristic-two field. They prove normalization
for full G₂(2^f), f ≥ 2, the genuine G₂(2)′ carrier, and every central two-cover
of G₂(4). No parabolic family, E.6.8 exclusion, or additional Chapter 1 input
is used. The argument adapts the rank method in
`Hyperplanes/ComponentBalance/SevenLifting/Rank.lean`; the separate geometry
owner assembles the parabolic families and the final E.6.8 exclusion.

The concrete model witnesses use the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), the invocation of 1.2.1(3).
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.G2Geometry.Normalization

variable {G : Type*} [Group G] [Finite G]

private theorem elementaryNine_of_noncommuting_threeGroup
    {P : Subgroup G} (hp : IsPGroup 3 P) {x y : P} (hne : x*y ≠ y*x) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 3^2 := by
  have hn : ¬ IsCyclic P := by
    intro hc
    let := hc
    exact hne (mul_comm' x y)
  obtain ⟨E, _, hc, he⟩ :=
    hp.exists_normal_elementary_prime_sq_of_odd_not_isCyclic (by decide) hn
  let := he
  refine ⟨E.map P.subtype, IsElementaryAbelian.map_subtype, ?_⟩
  simpa only [card_map_of_injective P.subtype_injective] using hc

private theorem cubic_mem_of_centralizes_nine
    (hr : primeRank 3 G ≤ 2) {L : Subgroup G}
    (hE : ∃ E : Subgroup L, IsElementaryAbelian 3 E ∧ Nat.card E = 3^2)
    {x : G} (hx : x^3 = 1) (hc : x ∈ centralizer (L : Set G)) : x ∈ L := by
  by_cases hx1 : x = 1
  · simp [hx1]
  have ho : orderOf x = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx) |>.resolve_left
      (fun he => hx1 (orderOf_eq_one_iff.mp he))
  obtain ⟨E, he, hcard⟩ := hE
  let := he
  let A := E.map L.subtype
  let _ : IsElementaryAbelian 3 A := IsElementaryAbelian.map_subtype
  by_contra hn
  have hxa : x ∉ A := fun ha => hn (map_subtype_le E ha)
  have hfix : A ≤ centralizer ({x} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp hc) a (map_subtype_le E ha))
  have hcardA : Nat.card A = 3^2 := by
    simpa only [A, card_map_of_injective L.subtype_injective] using hcard
  have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join A x ho hxa hfix hcardA
  omega

private theorem normal_of_cubic_threeGroup
    (hr : primeRank 3 G ≤ 2) {L : Subgroup G} (hL : IsComponent G L)
    (P : Subgroup L) (hp : IsPGroup 3 P)
    (x y : P) (hx : x^3=1) (hne : x*y ≠ y*x) : L.Normal := by
  have hE := elementaryNine_of_noncommuting_threeGroup hp hne
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra he
  have hc := commutator_eq_bot_iff_le_centralizer.mp
    (hL.commutator_eq_bot_of_ne (hL.map_conj g) (Ne.symm he))
  let a := MulAut.conj g
  have hxL : a ((x : L) : G) ∈ L := by
    apply cubic_mem_of_centralizes_nine hr hE
    · rw [← map_pow]
      have he : (((x : L) : G))^3 = 1 := congrArg (fun t : P => ((t : L) : G)) hx
      rw [he, map_one]
    · exact le_centralizer_iff.mp hc
        (mem_map_of_mem a.toMonoidHom (x : L).property)
  have hxy : a ((x : L) : G) * a ((y : L) : G) =
      a ((y : L) : G) * a ((x : L) : G) :=
    ((mem_centralizer_iff.mp (hc hxL)) _
      (mem_map_of_mem a.toMonoidHom (y : L).property)).symm
  apply hne
  apply Subtype.ext
  apply Subtype.ext
  apply a.injective
  change a (((x : L) : G) * ((y : L) : G)) =
    a (((y : L) : G) * ((x : L) : G))
  simpa only [map_mul] using hxy

private theorem three_subgroup_lifts
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (P : Subgroup (G ⧸ N)) (hp : IsPGroup 3 P) :
    ∃ f : P →* G, Function.Injective f := by
  let q := QuotientGroup.mk' N
  let A := P.comap q
  let K := N.subgroupOf A
  have hNA : N ≤ A := by
    intro x hx
    change q x ∈ P
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact P.one_mem
  let f : A →* P :=
    { toFun := fun x => ⟨q x, x.property⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun x y => Subtype.ext (map_mul q (x : G) (y : G)) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N y.val
    exact ⟨⟨x, by change q x ∈ P; rw [hx]; exact y.property⟩, Subtype.ext hx⟩
  have hk : f.ker = K := by
    ext x
    change (⟨q x, x.property⟩ : P) = 1 ↔ (x : G) ∈ N
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff x.val
  let e : A ⧸ K ≃* P := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hKcard : Nat.card K = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe hNA).toEquiv
  have hc : Nat.Coprime (Nat.card K) K.index := by
    rw [hKcard, index_eq_card, Nat.card_congr e.toEquiv]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hN
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hp
    rw [hn, hm]
    exact ((by decide : Nat.Coprime 2 3).pow_left n).pow_right m
  obtain ⟨C, hC⟩ := exists_right_complement'_of_coprime hc
  let j : P ≃* C := e.symm.trans hC.symm.QuotientMulEquiv
  exact ⟨A.subtype.comp (C.subtype.comp j.toMonoidHom),
    A.subtype_injective.comp (C.subtype_injective.comp j.injective)⟩

private theorem normal_of_embedded_cubic_threeGroup
    (hr : primeRank 3 G ≤ 2) {L : Subgroup G} (hL : IsComponent G L)
    {P : Type*} [Group P] (hp : IsPGroup 3 P)
    (f : P →* L) (hf : Function.Injective f)
    (x y : P) (hx : x^3=1) (hne : x*y ≠ y*x) : L.Normal := by
  let e := MonoidHom.ofInjective hf
  apply normal_of_cubic_threeGroup hr hL f.range
    (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective) (e x) (e y)
  · rw [← map_pow, hx, map_one]
  · intro he
    exact hne (e.injective (by simpa only [map_mul] using he))

variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

/-- A concrete three-group embedding with a noncentral cubic forces the whole
obstruction centralizer to normalize the component, hence also the source Q.
The intrinsic model witness remains an explicit premise of this reduction. -/
theorem component_normalizer_of_cubic_threeGroup
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    {P : Type*} [Group P] (hp : IsPGroup 3 P)
    (f : P →* L) (hf : Function.Injective f)
    (x y : P) (hx : x^3=1) (hne : x*y ≠ y*x) :
    Q ≤ normalizer (L : Set G) := by
  let H := centralizer (U : Set G)
  let e := (subgroupOfEquivOfLe hL.1).symm
  have hr := (h.obstructionCentralizer_sqtk hU).stronglyQuasithin 3 (by decide) (by decide)
  have hn := normal_of_embedded_cubic_threeGroup hr hL.2 hp
    (e.toMonoidHom.comp f) (e.injective.comp hf) x y hx hne
  have hHN : H ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hL.1).mp hn
  apply le_trans _ hHN
  rw [hQ]
  exact inf_le_right.trans (centralizer_le hU.1)

/-- The same normalization criterion for a quotient by any normal two-group.
The three-subgroup is lifted by a genuine injective homomorphism; in particular
this reduction does not discard any central two-cover. -/
theorem component_normalizer_of_quotient_cubic_threeGroup
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (N : Subgroup L) [N.Normal] (hN : IsPGroup 2 N)
    (P : Subgroup (L ⧸ N)) (hp : IsPGroup 3 P)
    (x y : P) (hx : x^3=1) (hne : x*y ≠ y*x) :
    Q ≤ normalizer (L : Set G) := by
  obtain ⟨f, hf⟩ := three_subgroup_lifts N hN P hp
  exact component_normalizer_of_cubic_threeGroup h hU hL hQ hp f hf x y hx hne

private theorem cubic_three_subgroup_of_g2 {X : Type*} [Group X] {f : ℕ}
    (hm : ClassificationModels.IsG2At X (2 ^ f)) :
    ∃ P : Subgroup X, IsPGroup 3 P ∧
      ∃ x y : P, x ^ 3 = 1 ∧ x * y ≠ y * x := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let := hF
  let := hfin
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨P, hp, x, y, hx, hxy⟩ :=
    Atlas.G2.BinaryThreeRank.exists_noncentral_cubic_three_subgroup
  let D := commutator (Atlas.G2.Model (ZMod 2))
  let i : P →* X := e.symm.toMonoidHom.comp
    (Atlas.G2.binaryFieldEmbedding.comp (D.subtype.comp P.subtype))
  have hi : Function.Injective i := e.symm.injective.comp
    (Atlas.G2.binaryFieldEmbedding_injective.comp
      (D.subtype_injective.comp P.subtype_injective))
  let ei := MonoidHom.ofInjective hi
  refine ⟨i.range, hp.of_surjective i.rangeRestrict i.rangeRestrict_surjective,
    ei x, ei y, ?_, ?_⟩
  · rw [← map_pow, hx, map_one]
  · intro he
    exact hxy (ei.injective (by simpa only [map_mul] using he))

/-- The full G₂(2^f) branch of the normalization step in E.6.8.
The binary three-subgroup embeds through the actual defining field. -/
theorem component_normalizer_of_g2
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    {f : ℕ} (_hf : 2 ≤ f) (hm : ClassificationModels.IsG2At L (2 ^ f)) :
    Q ≤ normalizer (L : Set G) := by
  obtain ⟨P, hp, x, y, hx, hxy⟩ := cubic_three_subgroup_of_g2 hm
  exact component_normalizer_of_cubic_threeGroup h hU hL hQ
    hp P.subtype P.subtype_injective x y hx hxy

/-- The binary endpoint uses precisely G₂(2)′, retaining its derived carrier. -/
theorem component_normalizer_of_derived
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hm : Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    Q ≤ normalizer (L : Set G) := by
  obtain ⟨e⟩ := hm
  obtain ⟨P, hp, x, y, hx, hxy⟩ :=
    Atlas.G2.BinaryThreeRank.exists_noncentral_cubic_three_subgroup
  exact component_normalizer_of_cubic_threeGroup h hU hL hQ hp
    (e.symm.toMonoidHom.comp P.subtype) (e.symm.injective.comp P.subtype_injective)
    x y hx hxy

/-- Every central two-cover of G₂(4) is normalized, including trivial center.
The whole center is the lifting kernel; its order is unrestricted. -/
theorem component_normalizer_of_cover
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hz : IsPGroup 2 (center L))
    (hm : ClassificationModels.IsG2At (L ⧸ center L) 4) :
    Q ≤ normalizer (L : Set G) := by
  obtain ⟨P, hp, x, y, hx, hxy⟩ := cubic_three_subgroup_of_g2 (f := 2) hm
  exact component_normalizer_of_quotient_cubic_threeGroup h hU hL hQ
    (center L) hz P hp x y hx hxy

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.G2Geometry.Normalization

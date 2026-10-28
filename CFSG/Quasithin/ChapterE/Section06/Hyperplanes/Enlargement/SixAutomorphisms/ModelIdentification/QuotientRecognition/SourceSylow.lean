module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Source
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.SylowBridge
public import Theory.GroupTheory.SylowLocalCore
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.TwoCentralSubspace.Lift
/-!
# A common Sylow order for all nonidentity enlargement actors

For each nontrivial actor in the elementary order-eight image of V, its
cyclic inverse image has corank two. The source small-corank theorem makes
Q = C_T(V) Sylow in its ambient centralizer. Relative normality of Y then
identifies a Sylow subgroup of the actor's fixed group with the same literal
intersection Q ∩ Y. Consequently all such fixed groups have equal two-parts.

Everything is proved on Y itself. In particular no fixed points are lifted
from Y/Z(Y) through a possible central two-cover. This comparison retains
the original subspaces and conjugation maps for the exceptional model tests.

Source: Aschbacher–Smith, E.6.5 and E.6.23, printed pp.246 and 254
(PDF pp.257 and 265).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
variable {G : Type*} [Group G] [Finite G] {M V U A X Y : Subgroup G} {g : G}

/-- Restrict the original common Sylow subgroup using the relative normality of Y. -/
theorem fixed_centralizer_sylow [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hY : NormalComponentExtension U A X g Y)
    {B : Subgroup G} (h1B : intersection A U g ≤ B) (hBV : B ≤ V)
    (hc : subgroupCorank V B < localM V) :
    ∃ P : Sylow 2 ↥(Y ⊓ centralizer (B : Set G)),
      (P : Subgroup ↥(Y ⊓ centralizer (B : Set G))).map
        (Y ⊓ centralizer (B : Set G)).subtype = sylowCentralizer (T : Subgroup G) V ⊓ Y := by
  obtain ⟨S, hS⟩ := smallCentralizer_sylow h hBV hc
  have hnY : centralizer (B : Set G) ≤ normalizer (Y : Set G) :=
    (Subgroup.centralizer_le h1B).trans
      ((normal_subgroupOf_iff_le_normalizer hY.component.1).mp hY.normal)
  obtain ⟨P, hP⟩ := S.exists_map_subtype_eq_inf_of_normalizes
    (show Y ⊓ centralizer (B : Set G) ≤ centralizer (B : Set G) from inf_le_right)
    ((le_inf hnY (centralizer (B : Set G)).le_normalizer).trans
      inf_normalizer_le_normalizer_inf)
  refine ⟨P, ?_⟩
  rw [hS] at hP
  have hQC : sylowCentralizer (T : Subgroup G) V ≤ centralizer (B : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hBV)
  exact hP.trans (by rw [← inf_assoc, inf_eq_left.mpr (inf_le_left.trans hQC)])

/-- Two small subspaces above the same intersection give equal fixed Sylow orders. -/
theorem fixed_centralizer_sylow_card_eq [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hY : NormalComponentExtension U A X g Y)
    {B C : Subgroup G}
    (h1B : intersection A U g ≤ B) (hBV : B ≤ V)
    (hB : subgroupCorank V B < localM V)
    (h1C : intersection A U g ≤ C) (hCV : C ≤ V)
    (hC : subgroupCorank V C < localM V)
    (P : Sylow 2 ↥(Y ⊓ centralizer (B : Set G)))
    (R : Sylow 2 ↥(Y ⊓ centralizer (C : Set G))) : Nat.card P = Nat.card R := by
  obtain ⟨P', hP⟩ := fixed_centralizer_sylow h hY h1B hBV hB
  obtain ⟨R', hR⟩ := fixed_centralizer_sylow h hY h1C hCV hC
  have hp := Subgroup.card_map_of_injective
    (f := (Y ⊓ centralizer (B : Set G)).subtype)
    (K := (P' : Subgroup ↥(Y ⊓ centralizer (B : Set G))))
    (Y ⊓ centralizer (B : Set G)).subtype_injective
  have hr := Subgroup.card_map_of_injective
    (f := (Y ⊓ centralizer (C : Set G)).subtype)
    (K := (R' : Subgroup ↥(Y ⊓ centralizer (C : Set G))))
    (Y ⊓ centralizer (C : Set G)).subtype_injective
  rw [hP] at hp
  rw [hR] at hr
  exact (Nat.card_congr (P.equiv P').toEquiv).trans
    (hp.symm.trans (hr.trans (Nat.card_congr (R'.equiv R).toEquiv)))
/-- The cyclic inverse image of any nonidentity actor has corank two. -/
theorem subspace_of_actor [IsElementaryAbelian 2 V]
    {L : Subgroup G} {g : G} (c : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y)
    {a : MulAut Y} (ha : a ∈ actionImage V Y) (ha1 : a ≠ 1)
    :
    ∃ B : Subgroup G, intersection A U g ≤ B ∧ B ≤ V ∧ subgroupCorank V B = 2 ∧
      actionImage B Y = zpowers a := by
  have hn := hY.normalized_by_V c.subspace_mem.1
  let ρ := Y.normalizerMonoidHom.comp (inclusion hn)
  let S := zpowers a
  let W := S.comap ρ
  let B := W.map V.subtype
  have hSρ : S ≤ ρ.range := zpowers_le.mpr ((actionImage_eq_range hn) ▸ ha)
  have hcardρ : Nat.card ρ.range = 8 := by
    rw [← actionImage_eq_range hn]
    exact whole_action_order c hY
  let _ := elementary_actionImage hn
  have ha2 : a ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (actionImage V Y)) ⟨a, ha⟩)
  have hcardS : Nat.card S = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha2 ha1
  have hBimage : actionImage B Y = S := by
    rw [actionImage_map hn, map_comap_eq, inf_eq_right.mpr hSρ]
  have hindexS : S.relIndex ρ.range = 4 := by
    have hp := relIndex_mul_relIndex (⊥ : Subgroup (MulAut Y)) S ρ.range bot_le hSρ
    rw [relIndex_bot_left, relIndex_bot_left, hcardS, hcardρ] at hp
    omega
  have hindexB : B.relIndex V = 4 := by
    have htop : (⊤ : Subgroup V).map V.subtype = V := by rw [← MonoidHom.range_eq_map, V.range_subtype]
    change (W.map V.subtype).relIndex V = 4
    conv_lhs => rhs; rw [← htop]
    rw [relIndex_map_map_of_injective _ _ V.subtype_injective,
      relIndex_top_right, index_comap]
    exact hindexS
  refine ⟨B, ?_, map_subtype_le W, ?_, hBimage⟩
  · intro x hx
    have hxC : x ∈ V ⊓ centralizer (Y : Set G) := (fixed_space c hY).symm ▸ hx
    refine ⟨⟨x, hxC.1⟩, ?_, rfl⟩
    have hk : ρ ⟨x, hxC.1⟩ = 1 := by
      change (⟨x, hxC.1⟩ : V) ∈ ρ.ker
      rw [conjugation_ker]
      exact hxC.2
    change ρ ⟨x, hxC.1⟩ ∈ S
    rw [hk]
    exact one_mem S
  · rw [subgroupCorank, hindexB]
    decide


omit [Finite G] in
/-- The cyclic conjugation image has exactly the literal fixed subgroup. -/
theorem actor_fixed_subgroup_eq {a : MulAut Y} {B : Subgroup G}
    (hn : B ≤ normalizer (Y : Set G)) (hb : actionImage B Y = zpowers a) :
    a.fixedSubgroup = (centralizer (B : Set G)).subgroupOf Y := by
  rw [← fixed_subgroup_eq B Y hn, hb]
  ext x
  constructor
  · intro hx b
    have hle : zpowers a ≤ MulAction.stabilizer (MulAut Y) x := zpowers_le.mpr ((MulAut.mem_fixedSubgroup _ _).mp hx)
    exact hle b.property
  · intro hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hx ⟨a, mem_zpowers a⟩)

/-- A nonidentity actor has a fixed Sylow subgroup with ambient image Q ∩ Y. -/
theorem actor_fixed_sylow [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V) {L : Subgroup G}
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y)
    {a : MulAut Y} (ha : a ∈ actionImage V Y) (ha1 : a ≠ 1) :
    ∃ P : Sylow 2 a.fixedSubgroup,
      ((P : Subgroup a.fixedSubgroup).map a.fixedSubgroup.subtype).map Y.subtype =
        sylowCentralizer (T : Subgroup G) V ⊓ Y := by
  obtain ⟨B, h1B, hBV, hc, he⟩ := subspace_of_actor d hY ha ha1
  have hm := (lemma_E_6_16_1 h h15 d.hyperplane d.hyperplane_mem.2.2.1).2.1
  obtain ⟨P, hP⟩ := fixed_centralizer_sylow h hY h1B hBV (hc ▸ hm)
  have hf := actor_fixed_subgroup_eq
    (hBV.trans (hY.normalized_by_V d.subspace_mem.1)) he
  let e : ↥(Y ⊓ centralizer (B : Set G)) ≃* a.fixedSubgroup := {
    toFun x := ⟨⟨x.val, x.property.1⟩, hf.ge x.property.2⟩
    invFun x := ⟨x.val.val, x.val.property, hf.le x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (((P : Subgroup ↥(Y ⊓ centralizer (B : Set G))).map e.toMonoidHom).map
    a.fixedSubgroup.subtype).map Y.subtype = _
  rw [map_map, map_map]
  exact hP


/-- Every Sylow subgroup of the actor fixed group has the source intersection order. -/
theorem actor_fixed_sylow_card [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V) {L : Subgroup G}
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y)
    {a : MulAut Y} (ha : a ∈ actionImage V Y) (ha1 : a ≠ 1)
    (P : Sylow 2 a.fixedSubgroup) :
    Nat.card P = Nat.card (sylowCentralizer (T : Subgroup G) V ⊓ Y : Subgroup G) := by
  obtain ⟨R, hR⟩ := actor_fixed_sylow h h15 d hY ha ha1
  have hm : Nat.card (((R : Subgroup a.fixedSubgroup).map
      a.fixedSubgroup.subtype).map Y.subtype) = Nat.card R :=
    (card_map_of_injective Y.subtype_injective).trans
      (card_map_of_injective a.fixedSubgroup.subtype_injective)
  rw [hR] at hm
  exact (Nat.card_congr (P.equiv R).toEquiv).trans hm.symm

/-- The actual E.6.23 configuration equates the two-parts for every pair of nontrivial actors. -/
theorem actor_fixed_twoPart_eq [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V) {L : Subgroup G}
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y)
    {a b : MulAut Y} (ha : a ∈ actionImage V Y) (ha1 : a ≠ 1)
    (hb : b ∈ actionImage V Y) (hb1 : b ≠ 1) :
    2 ^ (Nat.card a.fixedSubgroup).factorization 2 =
      2 ^ (Nat.card b.fixedSubgroup).factorization 2 := by
  let P : Sylow 2 a.fixedSubgroup := Classical.choice inferInstance
  let R : Sylow 2 b.fixedSubgroup := Classical.choice inferInstance
  rw [← P.card_eq_multiplicity, ← R.card_eq_multiplicity]
  exact (actor_fixed_sylow_card h h15 d hY ha ha1 P).trans
    (actor_fixed_sylow_card h h15 d hY hb hb1 R).symm

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen

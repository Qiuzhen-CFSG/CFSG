module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.Quasithin.Rank
public import Theory.PGroupCore

/-!
# Three-rank from an outer complement fixing a cubic element

Pull the complement back along conjugation on a centerless normal subgroup.
The resulting subgroup maps isomorphically onto the overgroup quotient and
centralizes an independent element of order three. Every elementary abelian
subgroup in that quotient therefore gains one rank in the overgroup.

The last theorem removes the characteristic two-core before applying this
argument. Coprime quotient lifting and the third isomorphism theorem preserve
the exact relative quotient and allow arbitrary central two-extensions.
The model complement is explicit data that callers must construct.

Source: the normal-block inference in Aschbacher--Smith, combined manuscript
(1 March 2004), proof of E.6.14, printed p.251, using C.1.7--13.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.NormalBlockRank

/-- An actual complement to inner automorphisms, fixing a cubic element. -/
structure CubicOuterComplement (L : Type*) [Group L] where
  center_eq_bot : center L = ⊥
  outer : Subgroup (MulAut L)
  disjoint : Disjoint (MulAut.innerSubgroup L) outer
  factor : ∀ a : MulAut L, ∃ (l : L) (b : MulAut L), b ∈ outer ∧ a = MulAut.conj l * b
  cubic : L
  cubic_order : orderOf cubic = 3
  fixed : ∀ b ∈ outer, b cubic = cubic

/-- Transport the actual automorphism complement and its fixed element. -/
noncomputable def CubicOuterComplement.congr {L M : Type*} [Group L] [Group M]
    (e : L ≃* M) (d : CubicOuterComplement M) : CubicOuterComplement L where
  center_eq_bot := by
    apply bot_unique
    intro x hx
    have hm : e x ∈ center M := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
    rw [d.center_eq_bot] at hm
    exact e.injective (hm.trans (map_one e).symm)
  outer := d.outer.comap (MulAut.congr e).toMonoidHom
  disjoint := by
    apply disjoint_def.mpr
    intro a ha hb
    obtain ⟨x, rfl⟩ := ha
    have hi : MulAut.congr e (MulAut.conj x) ∈ MulAut.innerSubgroup M := by
      rw [MulAut.congr_conj]
      exact ⟨e x, rfl⟩
    exact (MulAut.congr e).injective
      ((d.disjoint.le_bot ⟨hi, hb⟩).trans (map_one _).symm)
  factor := by
    intro a
    obtain ⟨m, b, hb, ha⟩ := d.factor (MulAut.congr e a)
    refine ⟨e.symm m, (MulAut.congr e).symm b, ?_, ?_⟩
    · change MulAut.congr e ((MulAut.congr e).symm b) ∈ d.outer
      simpa only [MulEquiv.apply_symm_apply] using hb
    · apply (MulAut.congr e).injective
      rw [map_mul, MulAut.congr_conj, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact ha
  cubic := e.symm d.cubic
  cubic_order := (orderOf_injective e.symm.toMonoidHom e.symm.injective _).trans d.cubic_order
  fixed := by
    intro b hb
    apply e.injective
    have h := d.fixed (MulAut.congr e b) hb
    change e (b (e.symm d.cubic)) = d.cubic at h
    simpa only [MulEquiv.apply_symm_apply] using h

variable {G : Type*} [Group G] [Finite G]

/-- A subgroup mapping isomorphically onto the quotient and centralizing an
independent cubic element gives one additional unit of three-rank. -/
theorem rank_add_one_le_of_centralizing_section (N D : Subgroup G) [N.Normal]
    (hD : Function.Bijective ((QuotientGroup.mk' N).comp D.subtype))
    (x : G) (hx : orderOf x = 3) (hxD : x ∉ D)
    (hfix : D ≤ centralizer ({x} : Set G)) :
    primeRank 3 (G ⧸ N) + 1 ≤ primeRank 3 G := by
  let e : D ≃* G ⧸ N := MulEquiv.ofBijective _ hD
  obtain ⟨E, hE, hcard⟩ := exists_elementaryAbelian_card_primeRank (G := D) (p := 3)
  let := hE
  let A := E.map D.subtype
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map_subtype
  have hc : Nat.card A = 3 ^ primeRank 3 D := by
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact hcard
  have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join A x hx
    (fun ha => hxD (Subgroup.map_subtype_le E ha))
    ((Subgroup.map_subtype_le E).trans hfix) hc
  rwa [primeRank_congr 3 e] at hh

/-- Pulling an outer complement back along conjugation splits any extension of
the centerless normal subgroup. Its fixed cubic element then lowers quotient
three-rank by one. No faithfulness of the overgroup action is assumed. -/
theorem rank_add_one_le_of_cubicOuterComplement (N : Subgroup G) [N.Normal]
    (d : CubicOuterComplement N) : primeRank 3 (G ⧸ N) + 1 ≤ primeRank 3 G := by
  let a : G →* MulAut N := MulAut.conjNormal
  let D := d.outer.comap a
  have hdis : Disjoint N D := by
    apply disjoint_def.mpr
    intro g hgN hgD
    have hi : a g ∈ MulAut.innerSubgroup N :=
      ⟨⟨g, hgN⟩, MulAut.conjNormal_val.symm⟩
    have he : a g = 1 := d.disjoint.le_bot ⟨hi, hgD⟩
    have hz : (⟨g, hgN⟩ : N) ∈ center N := by
      apply mem_center_iff.mpr
      intro n
      have hn := congrArg Subtype.val (DFunLike.congr_fun he n)
      apply Subtype.ext
      change (n : G) * g = g * n
      change g * (n : G) * g⁻¹ = (n : G) at hn
      exact (mul_inv_eq_iff_eq_mul.mp hn).symm
    have hg : (⟨g, hgN⟩ : N) = 1 := by
      rw [d.center_eq_bot] at hz
      exact hz
    exact congrArg Subtype.val hg
  have hq : Function.Bijective ((QuotientGroup.mk' N).comp D.subtype) := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff]
      apply bot_unique
      intro g hg
      have hgN : (g : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hg
      exact Subtype.ext (hdis.le_bot ⟨hgN, g.property⟩)
    · intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
      obtain ⟨n, b, hb, hab⟩ := d.factor (a g)
      have hn : a (n : G) = MulAut.conj n := MulAut.conjNormal_val
      have hmem : (n : G)⁻¹ * g ∈ D := by
        change a ((n : G)⁻¹ * g) ∈ d.outer
        rw [map_mul, map_inv, hn, hab, inv_mul_cancel_left]
        exact hb
      refine ⟨⟨(n : G)⁻¹ * g, hmem⟩, ?_⟩
      change QuotientGroup.mk' N ((n : G)⁻¹ * g) = QuotientGroup.mk' N g
      have hnq : QuotientGroup.mk' N (n : G) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr n.property
      rw [map_mul, map_inv, hnq, inv_one, one_mul]
  apply rank_add_one_le_of_centralizing_section N D hq (d.cubic : G)
  · exact (orderOf_injective N.subtype Subtype.val_injective d.cubic).trans d.cubic_order
  · intro hx
    have he : (d.cubic : G) = 1 := hdis.le_bot ⟨d.cubic.property, hx⟩
    have hc : d.cubic = 1 := Subtype.ext he
    have ho := d.cubic_order
    rw [hc, orderOf_one] at ho
    omega
  · intro g hg
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg Subtype.val (d.fixed (a g) hg)
    change g * (d.cubic : G) * g⁻¹ = (d.cubic : G) at he
    exact mul_inv_eq_iff_eq_mul.mp he

/-- Removing the characteristic two-core loses no three-rank. The outer
complement is needed only for the resulting normal subgroup, so arbitrary
central two-extensions of the model remain covered. -/
theorem rank_add_one_le_of_core_quotient (N : Subgroup G) [N.Normal]
    (d : CubicOuterComplement (N ⧸ pCore 2 N)) :
    primeRank 3 (G ⧸ N) + 1 ≤ primeRank 3 G := by
  let K : Subgroup G := (pCore 2 N).map N.subtype
  let : K.Normal := ConjAct.normal_of_characteristic_of_normal
  let q := QuotientGroup.mk' K
  let R := N.map q
  let : R.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective K)
  let f : N →* R := q.subgroupMap N
  have hf : Function.Surjective f := q.subgroupMap_surjective N
  have hk : f.ker = pCore 2 N := by
    ext n
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    change (QuotientGroup.mk (n : G) : G ⧸ K) = 1 ↔ n ∈ pCore 2 N
    rw [QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨m, hm, hmn⟩
      exact (Subtype.ext hmn : m = n) ▸ hm
    · intro hn
      exact ⟨n, hn, rfl⟩
  let e : (N ⧸ pCore 2 N) ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hr := rank_add_one_le_of_cubicOuterComplement R (d.congr e.symm)
  let eq : ((G ⧸ K) ⧸ R) ≃* G ⧸ N :=
    QuotientGroup.quotientQuotientEquivQuotient K N (Subgroup.map_subtype_le _)
  rw [primeRank_congr 3 eq] at hr
  have hcop : Nat.Coprime 3 (Nat.card K) := by
    have hp : IsPGroup 2 K := (pCore_isPGroup (p := 2) (G := N)).map N.subtype
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact hr.trans (primeRank_quotient_le_of_coprime 3 K hcop)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.NormalBlockRank

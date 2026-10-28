module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.SourceDefs
public import CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.Cubic
public import Theory.Representation.BinaryIrreducibleRank
public import Theory.GroupTheory.PrimeRankCentralCover
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.Representation.Mathieu.M22James.Classification
public import Theory.Mathieu.M22.BinaryCovers
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# Degree windows for the genuine M₂₂ source action

Schur's lemma and central descent bound the ambient two-rank by five and the
component two-rank by four. An actual cubic offender therefore has fixed
codimension at most ten. The generalized-Fitting condition also bounds the
ambient/component index by two. Three-conjugate inner and four-conjugate ambient
displacement estimates would then give the simple-cover window of thirty;
those representation estimates remain explicit in that conditional theorem.

For the triple cover, the proved extraspecial displacement calculation supplies
the inner estimate unconditionally. Every outer actor inverts the actual central
scalar and hence moves at least half the module. This gives the sharper window
of twenty-four without recognition or a hypothesis on the full linear normalizer.
The known minimum degree and divisibility by six leave 12, 18, and 24.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
pp.15–16, and Aschbacher–Smith, Chapter K, printed pp.451–452 and 457.
The arbitrary-module degree exclusions needed to reduce these windows to twelve
are separate mathematical obligations, not consequences of small-degree recognition.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

omit [FiniteDimensional (ZMod 2) V] in
/-- The two-rank bound applies to the given ambient actor, including its outer elements. -/
theorem source_twoRank_le_five (h : SourceHypotheses ρ L) : primeRank 2 G ≤ 5 := by
  let : L.Normal := h.component.symm ▸ inferInstance
  let := h.quasisimple
  let := h.irreducible
  obtain ⟨e⟩ := h.quotient
  have hr := BinaryIrreducibleCentralizer.primeRank_le_automorphisms ρ L h.faithful
  have hq := automorphism_primeRank_le_quotient_center (E := L) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at hq
  exact hr.trans (hq.trans m22_automorphism_twoRank_le_five)

omit [FiniteDimensional (ZMod 2) V] in
/-- The central kernel has odd order, so the component inherits the simple quotient’s bound. -/
theorem source_component_twoRank_le_four (h : SourceHypotheses ρ L) : primeRank 2 L ≤ 4 := by
  let := h.quasisimple
  let := h.irreducible
  obtain ⟨e⟩ := h.quotient
  have hc := M22BinaryCovers.center_card_eq_one_or_three_of_binary_irreducible
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) e
  have hz : primeRank 2 (center L) = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr (by
    rcases hc with hc | hc <;> rw [hc] <;> decide)
  have hr := primeRank_le_ker_add (p := 2) (QuotientGroup.mk' (center L))
  rw [QuotientGroup.ker_mk', hz, zero_add, primeRank_equiv 2 e] at hr
  exact hr.trans m22_twoRank_le_four

omit [FiniteDimensional (ZMod 2) V] in
/-- An elementary actor contained in the actual component has rank at most four. -/
theorem source_inner_actor_rank_le_four (h : SourceHypotheses ρ L)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hAL : A ≤ L) : rank A ≤ 4 := by
  let := hA.2
  let E := A.subgroupOf L
  have hE : IsElementaryAbelian 2 E := by
    exact IsElementaryAbelian.of_surjective (Subgroup.subgroupOfEquivOfLe hAL).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAL).symm.surjective
  have hc := (primeRank_le_iff_elementary_card_le L).mp
    (source_component_twoRank_le_four ρ L h) E hE
  have hr := Nat.log_mono_right (b := 2) hc
  have hr' : rank E ≤ 4 := by
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hr
  rwa [rank_subgroupOf hAL] at hr'

/-- The source cubic ratio supplies one actor and simultaneous bounds for all its elements. -/
theorem source_cubic_actor (h : SourceHypotheses ρ L) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ IsCubic ρ A ∧ rank A ≤ 5 ∧
      fixedCodim ρ A ≤ 2 * rank A ∧
      ∀ t ∈ A, fixedCodim ρ (zpowers t) ≤ 2 * rank A := by
  obtain ⟨A, hA, hc, hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic
  have hcard := (primeRank_le_iff_elementary_card_le G).mp
    (source_twoRank_le_five ρ L h) A hA.2
  have hr : rank A ≤ 5 := by
    have hh := Nat.log_mono_right (b := 2) hcard
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh
  refine ⟨A, hA, hc, hr, hd, ?_⟩
  intro t ht
  have hfix : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
    intro v hv b
    exact hv ⟨b, (zpowers_le.mpr ht) b.property⟩
  have hm := Submodule.finrank_mono hfix
  have h₁ := fixedCodim_add_finrank ρ A
  have h₂ := fixedCodim_add_finrank ρ (zpowers t)
  omega

/-- Every source action contains an involution moving at most ten dimensions. -/
theorem source_small_involution (h : SourceHypotheses ρ L) :
    ∃ t : G, orderOf t = 2 ∧ fixedCodim ρ (zpowers t) ≤ 10 := by
  obtain ⟨A, hA, _, hr, _, hall⟩ := source_cubic_actor ρ L h
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  refine ⟨t, orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t ht) ht1, ?_⟩
  exact (hall t ht).trans (by omega)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Irreducibility on the component implies irreducibility of the ambient action. -/
theorem source_irreducible (h : SourceHypotheses ρ L) : ρ.IsIrreducible := by
  let := h.irreducible
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp L.subtype)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation (ρ.comp L.subtype) :=
    ⟨S.toSubmodule, fun e _ hv => S.apply_mem_toSubmodule e hv⟩
  rcases eq_bot_or_eq_top T with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation (ρ.comp L.subtype) => U.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation (ρ.comp L.subtype) => U.toSubmodule) h

omit [FiniteDimensional (ZMod 2) V] in
/-- The actual quotient G/L has order dividing two, by generalized-Fitting self-centralization. -/
theorem source_index_dvd_two (h : SourceHypotheses ρ L) : L.index ∣ 2 := by
  let : L.Normal := h.component.symm ▸ inferInstance
  let := h.quasisimple
  obtain ⟨e⟩ := h.quotient
  have hinj : Function.Injective (MulAut.outerAction L) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    change (QuotientGroup.map _ _ _ _).ker = ⊥
    rw [QuotientGroup.ker_map, MulAut.conjNormal_comap_innerSubgroup,
      sup_eq_left.mpr (show centralizer (L : Set G) ≤ L from by
        rw [h.component]
        exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le),
      QuotientGroup.map_mk'_self]
  rw [Subgroup.index_eq_card]
  exact (card_dvd_of_injective (MulAut.outerAction L) hinj).trans
    ((card_dvd_of_injective (MulAut.centralQuotientOuter e)
      (MulAut.centralQuotientOuter_injective e)).trans
        M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two)

/-- The inner and ambient displacement estimates imply the degree window of thirty.
The estimates remain explicit; this does not assert conjugate generation for M₂₂. -/
theorem source_finrank_le_thirty_of_involution_bounds (h : SourceHypotheses ρ L)
    (hinner : ∀ t ∈ L, orderOf t = 2 →
      Module.finrank (ZMod 2) V ≤ 3 * fixedCodim ρ (zpowers t))
    (hall : ∀ t : G, orderOf t = 2 →
      Module.finrank (ZMod 2) V ≤ 4 * fixedCodim ρ (zpowers t)) :
    Module.finrank (ZMod 2) V ≤ 30 := by
  obtain ⟨A, hA, _, hr, _, hcodim⟩ := source_cubic_actor ρ L h
  let := hA.2
  by_cases hex : ∃ t : G, t ∈ A ∧ t ∈ L ∧ t ≠ 1
  · obtain ⟨t, htA, htL, ht1⟩ := hex
    have ht : orderOf t = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t htA) ht1
    have hd := hinner t htL ht
    have hc := hcodim t htA
    omega
  · let : L.Normal := h.component.symm ▸ inferInstance
    let f : A →* G ⧸ L := (QuotientGroup.mk' L).comp A.subtype
    have hf : Function.Injective f := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply _root_.eq_bot_iff.mpr
      intro t ht
      apply Subtype.ext
      by_contra ht1
      exact hex ⟨t, t.property, (QuotientGroup.eq_one_iff (t : G)).mp ht, ht1⟩
    have hcard := Nat.card_le_card_of_injective f hf
    have hi := Nat.le_of_dvd (by decide : 0 < 2) (source_index_dvd_two ρ L h)
    rw [← L.index_eq_card] at hcard
    have hr' : rank A ≤ 1 := by
      have hh := Nat.log_mono_right (b := 2) (hcard.trans hi)
      exact hh.trans (by decide)
    obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have ho : orderOf t = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
    have hd := hall t ho
    have hc := hcodim t ht
    omega

omit [FiniteDimensional (ZMod 2) V] in
/-- Every element outside the component inverts the scalar given by the same cover marking. -/
theorem source_outer_inverts_scalar (h : SourceHypotheses ρ L)
    (e : L ≃* M22TripleCover) (t : G) (ht : t ∉ L) :
    t * (e.symm M22TripleCover.scalar : G) * t⁻¹ =
      (e.symm M22TripleCover.scalar : G)⁻¹ := by
  let : L.Normal := h.component.symm ▸ inferInstance
  let a : MulAut L := MulAut.conjNormal t
  let b := MulAut.congr e a
  have hfix : b M22TripleCover.scalar ≠ M22TripleCover.scalar := by
    intro hb
    obtain ⟨y, hy⟩ := M22TripleCover.ScalarAutomorphisms.inner_of_fixes_scalar b hb
    have ha : a = MulAut.conj (e.symm y) := by
      apply (MulAut.congr e).injective
      simpa only [MulAut.congr_conj, e.apply_symm_apply] using hy
    have hm : t ∈ (MulAut.innerSubgroup L).comap (MulAut.conjNormal : G →* MulAut L) :=
      ⟨e.symm y, ha.symm⟩
    rw [MulAut.conjNormal_comap_innerSubgroup] at hm
    apply ht
    apply (sup_le le_rfl (show centralizer (L : Set G) ≤ L from ?_)) hm
    rw [h.component]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hb := (M22TripleCover.ScalarAutomorphisms.scalar_eq_or_inv b).resolve_left hfix
  have ha : a (e.symm M22TripleCover.scalar) = (e.symm M22TripleCover.scalar)⁻¹ := by
    apply e.injective
    simpa only [b, MulAut.congr_apply, MulEquiv.trans_apply, map_inv, e.apply_symm_apply] using hb
  exact congrArg Subtype.val ha

/-- The source triple-cover action has binary degree at most twenty-four, without recognition. -/
theorem source_triple_finrank_le_twenty_four (h : SourceHypotheses ρ L)
    (hc : Nat.card (center L) = 3) : Module.finrank (ZMod 2) V ≤ 24 := by
  let := h.quasisimple
  let := h.irreducible
  let := source_irreducible ρ L h
  let hL : ChapterH.Section10To12.IsTripleM22 L := ⟨h.quasisimple, hc, h.quotient⟩
  obtain ⟨A, hA, _, hr, _, hcodim⟩ := source_cubic_actor ρ L h
  let := hA.2
  by_cases hAL : A ≤ L
  · have hr4 := source_inner_actor_rank_le_four ρ L h A hA hAL
    obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have ho : orderOf t = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
    have hd := ChapterH.Section10To12.TripleDisplacement.finrank_le_three_mul_fixedCodim_involution
      L hL h.component.symm ρ h.faithful t ho
    have htbound := hcodim t ht
    omega
  · obtain ⟨t, htA, htL⟩ := SetLike.not_le_iff_exists.mp hAL
    obtain ⟨e⟩ := M22TripleCover.nonempty_mulEquiv hc h.quotient
    let z := e.symm M22TripleCover.scalar
    have hz : z ∈ center L := M22TripleCover.scalar_mem_center_of_equiv e
    have ho : orderOf (z : G) = 3 :=
      (Subgroup.orderOf_coe z).trans (M22TripleCover.scalar_order_of_equiv e)
    have hi := source_outer_inverts_scalar ρ L h e t htL
    have hd := ChapterH.Section10To12.TripleDisplacement.finrank_le_twice_of_inverts_center
      L hL h.component.symm ρ h.faithful z t (mem_map_of_mem L.subtype hz) ho hi
    have htbound := hcodim t htA
    omega


/-- The triple-cover source action has one of three remaining numerical degrees.
Exclusion of eighteen and twenty-four still requires arbitrary-module representation theory. -/
theorem source_triple_finrank_cases (h : SourceHypotheses ρ L)
    (hc : Nat.card (center L) = 3) :
    Module.finrank (ZMod 2) V = 12 ∨ Module.finrank (ZMod 2) V = 18 ∨
      Module.finrank (ZMod 2) V = 24 := by
  let := h.quasisimple
  let := h.irreducible
  let := source_irreducible ρ L h
  let hL : ChapterH.Section10To12.IsTripleM22 L := ⟨h.quasisimple, hc, h.quotient⟩
  obtain ⟨e⟩ := M22TripleCover.nonempty_mulEquiv hc h.quotient
  have hlo := M22TripleCover.faithful_irreducible_finrank_ge_twelve_of_equiv e
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective)
  have hhi := source_triple_finrank_le_twenty_four ρ L h hc
  have hd := ChapterH.Section10To12.TripleDisplacement.six_dvd_finrank
    L hL h.component.symm ρ h.faithful
  omega
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source

module
public import Theory.Representation.BinaryOffender.CubicConjugateBound
public import Theory.Alternating.SevenInvolutionGeneration
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry.TwoConjugates
public import Theory.Representation.BinaryOffender.SubgroupConjugateDimension
import Mathlib.Tactic.IntervalCases
/-!
# A degree bound for simple binary seven-point actions

A faithful simple module for a group containing the marked A₇ has no component-fixed vectors. Three conjugates of an inner involution and two conjugates of a rank-three actor give dimension at most twelve under the small fixed-codimension bound. This extends the existing Chapter K degree argument to ambient irreducibility, the exact situation in 13.8.24.

Source: Aschbacher–Smith 13.8.24, printed pp.958–959, and Guralnick–Malle (2002), §2, (2.5)–(2.6).
-/

public section
open Subgroup Equiv Representation Representation.BinaryOffender Theory.GroupTheory
namespace Representation.AlternatingSevenSmallQuadratic
private def HasInvolutionCommutator (t : Perm (Fin 7)) : Prop :=
  ∃ s : Perm (Fin 7), s ∈ alternatingGroup (Fin 7) ∧
    t * s * t⁻¹ * s⁻¹ ≠ 1 ∧ (t * s * t⁻¹ * s⁻¹) ^ 2 = 1

private theorem commutator_conjugate {t u : Perm (Fin 7)}
    (h : IsConj t u) (ht : HasInvolutionCommutator t) : HasInvolutionCommutator u := by
  obtain ⟨q, hq⟩ := isConj_iff.mp h
  let e := MulAut.conj q
  have he : e t = u := hq
  obtain ⟨s, hs, hn, hsq⟩ := ht
  refine ⟨e s, (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem s hs q, ?_, ?_⟩
  · have hn' := e.injective.ne hn
    simpa only [map_mul, map_inv, map_one, he] using hn'
  · have hh := congrArg e hsq
    simpa only [map_pow, map_mul, map_inv, map_one, he] using hh

/-- Every nonidentity involution on seven letters has an even commutator
which is again a nonidentity involution. -/
private theorem permutation_involution_commutator (t : Perm (Fin 7))
    (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ s : alternatingGroup (Fin 7),
      t * s.val * t⁻¹ * s.val⁻¹ ≠ 1 ∧ (t * s.val * t⁻¹ * s.val⁻¹) ^ 2 = 1 := by
  have ho : orderOf t = 2 := orderOf_eq_prime ht2 ht
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hbound := t.sum_cycleType_le
  rw [hk] at hbound
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hbound
  have hb : k ≤ 2 := by omega
  have hh : HasInvolutionCommutator t := by
    interval_cases k
    · apply commutator_conjugate (t := swap 0 1)
      · apply Perm.isConj_iff_cycleType_eq.mpr
        rw [hk]
        decide +kernel
      · refine ⟨swap 0 2 * swap 1 3, ?_⟩
        rw [Perm.mem_alternatingGroup]
        decide +kernel
    · apply commutator_conjugate (t := swap 0 1 * swap 2 3)
      · apply Perm.isConj_iff_cycleType_eq.mpr
        rw [hk]
        decide +kernel
      · refine ⟨swap 0 2 * swap 4 5, ?_⟩
        rw [Perm.mem_alternatingGroup]
        decide +kernel
    · apply commutator_conjugate (t := swap 0 1 * swap 2 3 * swap 4 5)
      · apply Perm.isConj_iff_cycleType_eq.mpr
        rw [hk]
        decide +kernel
      · refine ⟨swap 0 2 * swap 4 5, ?_⟩
        rw [Perm.mem_alternatingGroup]
        decide +kernel
  obtain ⟨s, hs, hne, hsq⟩ := hh
  exact ⟨⟨s, hs⟩, hne, hsq⟩


variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
  {L : Subgroup G} [L.Normal]
  (f : G →* Perm (Fin 7)) (hf : Function.Injective f)
  (e : L ≃* alternatingGroup (Fin 7))
  (hmark : ∀ l : L, f l.val = (e l).val)

omit [Finite G] in
private theorem fixedSpace_normal [Nontrivial L] (hfρ : Function.Injective ρ) :
    fixedSpace ρ L = ⊥ := by
  by_contra hn
  have hk := ρ.le_ker_of_normal_invariants_ne_bot L hn
  obtain ⟨x, hx⟩ := exists_ne (1 : L)
  apply hx
  apply Subtype.ext
  exact hfρ ((hk x.property).trans ρ.map_one.symm)

variable [FiniteDimensional (ZMod 2) V]
omit [Finite G] in
/-- Every component involution bounds the degree through its three conjugates. -/
theorem finrank_le_three_mul_component_displacement (hfρ : Function.Injective ρ)
    (e : L ≃* alternatingGroup (Fin 7)) (t : L) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    Module.finrank (ZMod 2) V ≤ 3 * fixedCodim ρ (zpowers t.val) := by
  obtain ⟨g, k, hgk⟩ := alternatingGroup.SevenInvolutionGeneration.three_conjugates_generate
    (e t) (by simpa only [map_one] using e.injective.ne ht) (by rw [← map_pow, ht2, map_one])
  have heq := congrArg (Subgroup.map e.symm.toMonoidHom) hgk
  rw [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] at heq
  simp only [Subgroup.map_sup, MonoidHom.map_zpowers,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul, map_inv,
    e.symm_apply_apply] at heq
  have hm := congrArg (Subgroup.map L.subtype) heq
  simp only [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, L.range_subtype,
    map_mul, map_inv] at hm
  let c : Fin 3 → G := ![1, (e.symm g).val, (e.symm k).val]
  have hgen : L ≤ closure (Set.range fun i => c i * t.val * (c i)⁻¹) := by
    apply hm.ge.trans
    refine sup_le (sup_le ?_ ?_) ?_
    · apply zpowers_le.mpr
      exact subset_closure ⟨0, by simp [c]⟩
    · apply zpowers_le.mpr
      exact subset_closure ⟨1, by simp [c]⟩
    · apply zpowers_le.mpr
      exact subset_closure ⟨2, by simp [c]⟩
  let : Nontrivial L := ⟨⟨t, 1, ht⟩⟩
  exact finrank_le_mul_fixedCodim_of_conjugate_generation ρ L
    (fixedSpace_normal ρ hfρ) t.val c hgen

include f hf in
/-- Every marked seven-point group has two-rank at most three. -/
theorem ambient_two_rank_le_three : primeRank 2 G ≤ 3 :=
  (primeRank_le_of_injective 2 f hf).trans_eq
    AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_symmetric

omit [Finite G] in
/-- An inner involution of an actor bounds the degree by six times its rank. -/
theorem finrank_le_six_mul_rank_of_inner_actor (hfρ : Function.Injective ρ)
    (e : L ≃* alternatingGroup (Fin 7)) (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) (hne : A ⊓ L ≠ ⊥) :
    Module.finrank (ZMod 2) V ≤ 6 * rank A := by
  obtain ⟨t, ht, ht1⟩ := (A ⊓ L).bot_or_exists_ne_one.resolve_left hne
  let : IsElementaryAbelian 2 A := hA.2
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht.1
  have hle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
    intro v hv a
    exact hv ⟨a, (zpowers_le.mpr ht.1) a.property⟩
  have hmono := Submodule.finrank_mono hle
  have hdimA := fixedCodim_add_finrank ρ A
  have hdimt := fixedCodim_add_finrank ρ (zpowers t)
  have hb := finrank_le_three_mul_component_displacement ρ hfρ e ⟨t, ht.2⟩
    (fun hh => ht1 (congrArg Subtype.val hh)) (Subtype.ext ht2)
  change Module.finrank (ZMod 2) V ≤ 3 * fixedCodim ρ (zpowers t) at hb
  omega

include f hf in
/-- A source cubic actor meeting L gives the degree bound eighteen. -/
theorem finrank_le_eighteen_of_inner_actor (hfρ : Function.Injective ρ)
    (e : L ≃* alternatingGroup (Fin 7)) (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) (hne : A ⊓ L ≠ ⊥) :
    Module.finrank (ZMod 2) V ≤ 18 := by
  have hr := rank_le_of_primeRank_le hA (ambient_two_rank_le_three f hf)
  exact (finrank_le_six_mul_rank_of_inner_actor ρ hfρ e A hA hsmall hne).trans (by omega)

omit [FiniteDimensional (ZMod 2) V] in
omit [Finite G] [L.Normal] in
include f hf hmark in
/-- The elementary actors disjoint from the component have rank at most one. -/
theorem rank_le_one_of_disjoint
    (A : Subgroup G) (hAL : A ⊓ L = ⊥) :
    rank A ≤ 1 := by
  let s : A →* ℤˣ := Perm.sign.comp (f.comp A.subtype)
  have hs : Function.Injective s := by
    apply (MonoidHom.ker_eq_bot_iff s).mp
    apply le_bot_iff.mp
    intro a ha
    have hev : f a.val ∈ alternatingGroup (Fin 7) := MonoidHom.mem_ker.mp ha
    let l := e.symm ⟨f a.val, hev⟩
    have hfa : f l.val = f a.val := (hmark l).trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨f a.val, hev⟩))
    have hal : a.val ∈ L := hf hfa ▸ l.property
    have hab : a.val ∈ A ⊓ L := ⟨a.property, hal⟩
    rw [hAL, mem_bot] at hab
    exact Subtype.ext hab
  have hc : Nat.card A ≤ 2 := (Nat.card_le_card_of_injective s hs).trans_eq (by rw [Nat.card_eq_fintype_card]; decide)
  have hh := Nat.log_mono_right (b := 2) hc
  exact hh.trans_eq (by decide)

omit [Finite G] in
include f hf hmark in
/-- In the disjoint-actor case, an involutory component commutator gives
an even stronger upper bound, without restricting the ambient cubic ratio. -/
theorem finrank_le_twelve_of_disjoint_actor (hfρ : Function.Injective ρ)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) (hAL : A ⊓ L = ⊥) :
    Module.finrank (ZMod 2) V ≤ 12 := by
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  let : IsElementaryAbelian 2 A := hA.2
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  obtain ⟨s, hs1, hs2⟩ := permutation_involution_commutator (f t)
    (fun hh => ht1 (hf (hh.trans f.map_one.symm))) (by rw [← map_pow, ht2, map_one])
  let l := e.symm s
  let x := t * l.val * t⁻¹ * l.val⁻¹
  have hxL : x ∈ L := L.mul_mem ((inferInstance : L.Normal).conj_mem _ l.property t)
    (L.inv_mem l.property)
  have hfx : f x = f t * s.val * (f t)⁻¹ * s.val⁻¹ := by
    simp only [x, map_mul, map_inv, hmark, l, e.apply_symm_apply]
  have hx1 : x ≠ 1 := fun hh => hs1 (hfx.symm.trans (by rw [hh, map_one]))
  have hx2 : x ^ 2 = 1 := hf (by rw [map_pow, hfx, hs2, map_one])
  have hr := rank_le_one_of_disjoint f hf e hmark A hAL
  have hcodim : fixedCodim ρ (zpowers t) ≤ 2 := by
    have hle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
      intro v hv a
      exact hv ⟨a, (zpowers_le.mpr ht) a.property⟩
    have hmono := Submodule.finrank_mono hle
    have hdimA := fixedCodim_add_finrank ρ A
    have hdimt := fixedCodim_add_finrank ρ (zpowers t)
    omega
  have hd := fixedCodim_commutator_le_twice ρ t l.val
  have hb := finrank_le_three_mul_component_displacement ρ hfρ e ⟨x, hxL⟩
    (fun hh => hx1 (congrArg Subtype.val hh)) (Subtype.ext hx2)
  change fixedCodim ρ (zpowers x) ≤ _ at hd
  change Module.finrank (ZMod 2) V ≤ 3 * fixedCodim ρ (zpowers x) at hb
  omega

omit [Finite G] [L.Normal] in
include f hf hmark in
/-- The rank-three actor and one conjugate by an element of the actual
component generate the original ambient group. -/
theorem exists_generating_conjugate 
    (A : Subgroup G)
    (hA : IsElementaryTwo A) (hr : rank A = 3) :
    ∃ l : L, A ⊔ A.map (MulAut.conj l.val).toMonoidHom = ⊤ := by
  let B := A.map f
  let : IsElementaryAbelian 2 A := hA.2
  have hB : IsElementaryTwo B :=
    ⟨fun hb => hA.1 ((Subgroup.map_eq_bot_iff_of_injective A hf).mp hb),
      IsElementaryAbelian.map f⟩
  have hrB : rank B = 3 := by
    unfold rank
    rw [Subgroup.card_map_of_injective hf]
    exact hr
  obtain ⟨q, hq, hgen⟩ :=
    AlternatingSevenConjugatePair.ElementaryGeometry.rank_three_two_even_conjugates B hB hrB
  let l := e.symm ⟨q, hq⟩
  have hfl : f l.val = q := (hmark l).trans
    (congrArg Subtype.val (e.apply_symm_apply ⟨q, hq⟩))
  have he : (A.map (MulAut.conj l.val).toMonoidHom).map f =
      B.map (MulAut.conj q).toMonoidHom := by
    change (A.map (MulAut.conj l.val).toMonoidHom).map f =
      (A.map f).map (MulAut.conj q).toMonoidHom
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, hfl]
  have htop : (A ⊔ A.map (MulAut.conj l.val).toMonoidHom).map f = ⊤ := by
    rw [Subgroup.map_sup, he]
    exact hgen
  refine ⟨l, top_unique ?_⟩
  intro x _
  obtain ⟨a, ha, hax⟩ := (show f x ∈
    (A ⊔ A.map (MulAut.conj l.val).toMonoidHom).map f by rw [htop]; trivial)
  exact hf hax ▸ ha

omit [Finite G] in
include f hf hmark in
/-- Two component conjugates bound the degree by twice the fixed codimension
of the original rank-three actor. -/
theorem finrank_le_twice_fixedCodim (hfρ : Function.Injective ρ)
    (A : Subgroup G)
    (hA : IsElementaryTwo A) (hr : rank A = 3) :
    Module.finrank (ZMod 2) V ≤ 2 * fixedCodim ρ A := by
  obtain ⟨l, hl⟩ := exists_generating_conjugate f hf e hmark A hA hr
  let : Nontrivial L := e.symm.injective.nontrivial
  let c : Bool → G := fun b => if b then 1 else l.val
  have hc : L ≤ ⨆ b, A.map (MulAut.conj (c b)).toMonoidHom := by
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    simp only [iSup_bool_eq, c, Bool.false_eq_true, ite_false, ite_true, hid,
      Subgroup.map_id, hl]
    exact le_top
  simpa only [Fintype.card_bool] using
    finrank_le_card_mul_fixedCodim_of_subgroup_conjugates ρ L A
      (fixedSpace_normal ρ hfρ) c hc


include f hf hmark in
/-- Every faithful simple binary module between A₇ and S₇ with a small
nontrivial elementary actor has dimension at most twelve. -/
theorem finrank_le_twelve (hfρ : Function.Injective ρ)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V ≤ 12 := by
  have hr := rank_le_of_primeRank_le hA (ambient_two_rank_le_three f hf)
  by_cases hi : A ⊓ L = ⊥
  · exact finrank_le_twelve_of_disjoint_actor ρ f hf e hmark hfρ A hA hsmall hi
  by_cases he : rank A = 3
  · have hb := finrank_le_twice_fixedCodim ρ f hf e hmark hfρ A hA he
    omega
  · have hb := finrank_le_six_mul_rank_of_inner_actor ρ hfρ e A hA hsmall hi
    omega

end Representation.AlternatingSevenSmallQuadratic

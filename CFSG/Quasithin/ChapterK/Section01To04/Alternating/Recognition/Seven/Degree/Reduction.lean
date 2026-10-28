module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Inputs
public import Theory.Representation.BinaryOffender.CubicConjugateBound
public import Theory.Alternating.SevenInvolutionGeneration
public import Theory.Alternating.Aut
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry

import Mathlib.Tactic.IntervalCases

/-!
# A degree window for the actual ambient A₇ action

Self-centralization of F*(G) and the trivial center of A₇ make conjugation on
L faithful. Aut(A₇) = S₇ therefore gives a seven-point embedding of G whose
restriction is the specified component isomorphism.

An elementary actor meeting L contains an involution whose three component
conjugates generate L; the degree is at most six times the actor rank, hence
at most eighteen. A disjoint actor injects into the sign group and has rank
at most one. Every nonidentity seven-point involution has a commutator with
an even permutation which is again an involution. Its displacement is at most
twice the original displacement, giving degree at most twelve in this case.

The original cubic bound supplies the actor in both cases. Above degree twelve,
`exists_rank_three_cubic_actor` supplies its exact rank and fixed-codimension
bound to the remaining fourteen-dimensional exclusion. No bound on the
restricted cubic ratio, representation catalogue, or FF classification is used.

Source: Aschbacher–Smith K.1.2, printed p.452 (PDF p.463); the conjugate
estimate is Guralnick–Malle, Classification of 2F-modules I, §2, (2.5)–(2.6).
The existing `SevenInvolutionGeneration` supplies the A₇ generating triples;
only the three explicit permutation commutators below require finite checking.
-/

public section

open Subgroup Equiv Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterK.Alternating.SevenDegreeReduction

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
  (ρ : Representation (ZMod 2) G V) {K : GroupClass} {L : Subgroup G}

/-- The source component determines a faithful seven-point ambient action,
with the given component isomorphism as its exact restriction. -/
theorem exists_permutation_embedding (h : Input ρ K L)
    (e : L ≃* alternatingGroup (Fin 7)) :
    ∃ f : G →* Perm (Fin 7), Function.Injective f ∧
      ∀ l : L, f l.val = (e l).val := by
  let : L.Normal := by rw [h.fitting]; infer_instance
  let E : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  let f : G →* Perm (Fin 7) := E.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := L)))
  have hmark (l : L) : f l.val = (e l).val := by
    apply E.injective
    change E (E.symm ((MulAut.congr e) (MulAut.conjNormal l.val))) = _
    rw [E.apply_symm_apply]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (e (⟨l.val * (e.symm x).val * l.val⁻¹, _⟩ : L)).val = _
    change (e (l * e.symm x * l⁻¹)).val = (e l).val * x.val * (e l).val⁻¹
    simp only [map_mul, map_inv, e.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro g hg
    have hg' : MulAut.conjNormal (H := L) g = 1 := by
      apply (MulAut.congr e).injective
      apply E.symm.injective
      change f g = E.symm ((MulAut.congr e) 1)
      simpa only [map_one] using (MonoidHom.mem_ker.mp hg)
    have hc : g ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro l hl
      have hh := congrArg (fun a : MulAut L => (a ⟨l, hl⟩).val) hg'
      change g * l * g⁻¹ = l at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hgl : g ∈ L := by
      rw [h.fitting] at hc ⊢
      exact centralizer_generalizedFitting_le G hc
    have hz : e ⟨g, hgl⟩ ∈ center (alternatingGroup (Fin 7)) := by
      rw [mem_center_iff]
      intro x
      have hh := mem_centralizer_iff.mp hc (e.symm x).val (e.symm x).property
      have hh' : e.symm x * (⟨g, hgl⟩ : L) = ⟨g, hgl⟩ * e.symm x := Subtype.ext hh
      simpa only [map_mul, e.apply_symm_apply] using congrArg e hh'
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hz
    have hl : (⟨g, hgl⟩ : L) = 1 := e.injective (hz.trans e.map_one.symm)
    exact congrArg Subtype.val hl
  exact ⟨f, hfi, hmark⟩

variable [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
/-- Every component involution bounds the degree through its three conjugates. -/
theorem finrank_le_three_mul_component_displacement (h : Input ρ K L)
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
    (fixedSpace_eq_bot_of_faithful_irreducible_on ρ L h.faithful h.irreducible) t.val c hgen

omit [FiniteDimensional (ZMod 2) V] in
/-- The original ambient actor embeds in S₇, so its two-rank is at most three. -/
theorem ambient_two_rank_le_three (h : Input ρ K L)
    (e : L ≃* alternatingGroup (Fin 7)) : primeRank 2 G ≤ 3 := by
  obtain ⟨f, hf, _⟩ := exists_permutation_embedding ρ h e
  exact (primeRank_le_of_injective 2 f hf).trans_eq
    AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_symmetric

omit [Finite G] in
/-- An inner involution of an actor bounds the degree by six times its rank. -/
theorem finrank_le_six_mul_rank_of_inner_actor (h : Input ρ K L)
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
  have hb := finrank_le_three_mul_component_displacement ρ h e ⟨t, ht.2⟩
    (fun hh => ht1 (congrArg Subtype.val hh)) (Subtype.ext ht2)
  change Module.finrank (ZMod 2) V ≤ 3 * fixedCodim ρ (zpowers t) at hb
  omega

/-- A source cubic actor meeting L gives the degree bound eighteen. -/
theorem finrank_le_eighteen_of_inner_actor (h : Input ρ K L)
    (e : L ≃* alternatingGroup (Fin 7)) (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) (hne : A ⊓ L ≠ ⊥) :
    Module.finrank (ZMod 2) V ≤ 18 := by
  have hr := rank_le_of_primeRank_le hA (ambient_two_rank_le_three ρ h e)
  exact (finrank_le_six_mul_rank_of_inner_actor ρ h e A hA hsmall hne).trans (by omega)

omit [FiniteDimensional (ZMod 2) V] in
/-- The elementary actors disjoint from the component have rank at most one. -/
theorem rank_le_one_of_disjoint (h : Input ρ K L)
    (e : L ≃* alternatingGroup (Fin 7)) (A : Subgroup G) (hAL : A ⊓ L = ⊥) :
    rank A ≤ 1 := by
  obtain ⟨f, hf, hmark⟩ := exists_permutation_embedding ρ h e
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

/-- In the disjoint-actor case, an involutory component commutator gives
an even stronger upper bound, without restricting the ambient cubic ratio. -/
theorem finrank_le_twelve_of_disjoint_actor (h : Input ρ K L)
    (e : L ≃* alternatingGroup (Fin 7)) (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) (hAL : A ⊓ L = ⊥) :
    Module.finrank (ZMod 2) V ≤ 12 := by
  let : L.Normal := by rw [h.fitting]; infer_instance
  obtain ⟨f, hf, hmark⟩ := exists_permutation_embedding ρ h e
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
  have hr := rank_le_one_of_disjoint ρ h e A hAL
  have hcodim : fixedCodim ρ (zpowers t) ≤ 2 := by
    have hle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
      intro v hv a
      exact hv ⟨a, (zpowers_le.mpr ht) a.property⟩
    have hmono := Submodule.finrank_mono hle
    have hdimA := fixedCodim_add_finrank ρ A
    have hdimt := fixedCodim_add_finrank ρ (zpowers t)
    omega
  have hd := fixedCodim_commutator_le_twice ρ t l.val
  have hb := finrank_le_three_mul_component_displacement ρ h e ⟨x, hxL⟩
    (fun hh => hx1 (congrArg Subtype.val hh)) (Subtype.ext hx2)
  change fixedCodim ρ (zpowers x) ≤ _ at hd
  change Module.finrank (ZMod 2) V ≤ 3 * fixedCodim ρ (zpowers x) at hb
  omega

/-- An unconditional degree window for the original Chapter K input.
No representation catalogue or bound for the restricted cubic ratio is used. -/
theorem finrank_le_eighteen (h : Input ρ K L) (e : L ≃* alternatingGroup (Fin 7)) :
    Module.finrank (ZMod 2) V ≤ 18 := by
  obtain ⟨A, hA, _, hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic_bound
  by_cases hi : A ⊓ L = ⊥
  · exact (finrank_le_twelve_of_disjoint_actor ρ h e A hA hsmall hi).trans (by decide)
  · exact finrank_le_eighteen_of_inner_actor ρ h e A hA hsmall hi

/-- Above degree twelve a genuine cubic actor has rank three. This supplies
exactly the ambient actor needed by the independent fourteen-space exclusion. -/
theorem exists_rank_three_cubic_actor (h : Input ρ K L)
    (e : L ≃* alternatingGroup (Fin 7)) (hd : 12 < Module.finrank (ZMod 2) V) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ IsCubic ρ A ∧ rank A = 3 ∧
      A ⊓ L ≠ ⊥ ∧ fixedCodim ρ A ≤ 6 := by
  obtain ⟨A, hA, hc, hs⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic_bound
  have hi : A ⊓ L ≠ ⊥ := by
    intro hi
    exact (not_le_of_gt hd) (finrank_le_twelve_of_disjoint_actor ρ h e A hA hs hi)
  have hr := rank_le_of_primeRank_le hA (ambient_two_rank_le_three ρ h e)
  have hb := finrank_le_six_mul_rank_of_inner_actor ρ h e A hA hs hi
  exact ⟨A, hA, hc, by omega, hi, by omega⟩

end CFSG.Quasithin.ChapterK.Alternating.SevenDegreeReduction

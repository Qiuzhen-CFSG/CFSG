module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.Selection
public import BenderSuzuki.ZD.RankOne
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms
public import Theory.GroupAction.SimpleCosets
public import Theory.GroupTheory.ZStar.InvolutionSupplement
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
/-!
# The fusion deductions in GLS IV, Chapter 2, Corollary 16.6

Double transitivity and rank one of the literal two-point stabilizer move
every involution into the selected involution centralizer. The three local
classes there then force the marked fusion u ~ uz by Glauberman Z-star.
The local class census is still an explicit earlier-source input.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem involution_isConj {x y : G} (hx : PFAppendixIII.IsInvolution x)
    (hc : IsConj x y) : PFAppendixIII.IsInvolution y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  have hi := IsInvolution.map_of_injective hx (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  change PFAppendixIII.IsInvolution (MulAut.conj g x) at hi
  simpa only [MulAut.conj_apply, hg] using hi

/-- The elementary two-point fusion step in source 16.6(c). -/
public theorem source16_involution_conjugate_into_centralizer
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {t u : G} (htM : t ∉ M)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hD : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    {s : G} (hs : PFAppendixIII.IsInvolution s) :
    ∃ v ∈ centralizer ({u} : Set G), IsConj s v := by
  let : IsSimpleGroup G := r.simple
  let : FaithfulSMul G (G ⧸ M) := M.faithfulSMul_quotient_of_simple h.proper
  have hmove : ∃ a : G ⧸ M, s • a ≠ a := by
    by_contra hn
    push Not at hn
    exact hs.ne_one (faithfulSMul_iff.mp inferInstance s hn)
  obtain ⟨a, hsa⟩ := hmove
  let alpha : G ⧸ M := QuotientGroup.mk 1
  let beta : G ⧸ M := t⁻¹ • alpha
  have hab : alpha ≠ beta := by
    intro he
    apply htM
    rw [← baseCoset_stabilizer M]
    exact (inv_smul_eq_iff.mp he.symm).symm
  obtain ⟨g, hga, hgb⟩ := MulAction.is_two_pretransitive_iff.mp ha.two_transitive hsa.symm hab
  let v := MulAut.conj g s
  have hva : v • alpha = beta := by
    rw [← hga, ← hgb]
    simp only [v, MulAut.conj_apply, mul_smul, inv_smul_smul]
  have hvb : v • beta = alpha := by
    rw [← hva, ← mul_smul]
    have hvv : v * v = 1 := by
      rw [← pow_two]
      exact (involution_isConj hs (isConj_iff.mpr ⟨g, rfl⟩)).sq_eq_one
    rw [hvv, one_smul]
  have hvi : PFAppendixIII.IsInvolution v := involution_isConj hs (isConj_iff.mpr ⟨g, rfl⟩)
  let D := residualPairStabilizer M t
  have hDmem (x : G) : x ∈ D ↔ x • alpha = alpha ∧ x • beta = beta := by
    have hM : M = MulAction.stabilizer G alpha := (baseCoset_stabilizer M).symm
    have hMt : rightConjugate M t = MulAction.stabilizer G beta :=
      (congrArg (fun K : Subgroup G => rightConjugate K t) hM).trans
        (rightConjugate_stabilizer alpha t)
    exact and_congr ((congrArg (x ∈ ·) hM).to_iff) ((congrArg (x ∈ ·) hMt).to_iff)
  have hvN : v ∈ normalizer (D : Set G) := by
    apply mem_normalizer_iff.mpr
    have hm (x : G) (hx : x ∈ D) : v * x * v⁻¹ ∈ D := by
      obtain ⟨hxa, hxb⟩ := (hDmem x).mp hx
      apply (hDmem _).mpr
      rw [hvi.inv_eq_self]
      simp only [mul_smul, hva, hvb, hxa, hxb, and_self]
    intro x
    constructor
    · exact hm x
    · intro hx
      have hh := hm _ hx
      have he : v * (v * x * v⁻¹) * v⁻¹ = x := by
        calc
          v * (v * x * v⁻¹) * v⁻¹ = (v * v) * x * (v * v)⁻¹ := by group
          _ = x := by rw [show v * v = 1 from by simpa only [pow_two] using hvi.sq_eq_one]; simp
      rwa [he] at hh
  let f := D.normalizerMonoidHom ⟨v, hvN⟩
  have hf2 : f ^ 2 = 1 := by
    rw [← map_pow, show (⟨v, hvN⟩ : normalizer (D : Set G)) ^ 2 = 1 from Subtype.ext hvi.sq_eq_one, map_one]
  let uD : D := ⟨u, huD⟩
  have huDi : PFAppendixIII.IsInvolution uD :=
    ⟨fun hh => hu.ne_one (congrArg Subtype.val hh), Subtype.ext hu.sq_eq_one⟩
  have heven : Even (Nat.card D) := by
    rw [even_iff_two_dvd, ← orderOf_eq_prime huDi.sq_eq_one huDi.ne_one]
    exact orderOf_dvd_natCard uD
  obtain ⟨w, hwf, hw⟩ := exists_fixed_involution_of_even f hf2 heven
  obtain ⟨d, hd⟩ := involutions_conjugate_of_not_twoRank hD hw huDi
  have hvw : Commute v (w : G) := by
    have hh := congrArg D.subtype ((MulAut.mem_fixedSubgroup f w).mp hwf)
    change v * (w : G) * v⁻¹ = (w : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  let e := MulAut.conj (d : G)
  have hew : e (w : G) = u := congrArg D.subtype hd
  refine ⟨e v, ?_, (isConj_iff.mpr ⟨g, rfl⟩ : IsConj s v).trans (isConj_iff.mpr ⟨(d : G), rfl⟩)⟩
  apply mem_centralizer_singleton_iff.mpr
  have hc := hvw.map e.toMonoidHom
  change Commute (e v) (e (w : G)) at hc
  simpa only [hew] using hc.eq
/-- The Z-star fusion in source 16.6(c), from the three local classes in C(u). -/
public theorem source16_marked_fusion
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {u z : G} (hu : PFAppendixIII.IsInvolution u) (huZ : u ∉ Z)
    (hcensus : ∀ v ∈ centralizer ({u} : Set G), PFAppendixIII.IsInvolution v →
      v = u ∨ v ∈ Z ∨ IsConj (u * z) v) : IsConj u (u * z) := by
  by_contra hnot
  have hcore : pPrimeCore 2 G = ⊥ := by
    rcases r.simple.eq_bot_or_eq_top_of_normal (pPrimeCore 2 G) inferInstance with hb | ht
    · exact hb
    · have hd := (pPrimeCore 2 G).orderOf_dvd_natCard (ht ▸ mem_top u)
      rw [orderOf_eq_prime hu.sq_eq_one hu.ne_one] at hd
      exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp
        (pPrimeCore_coprime_card (p := 2))) hd)
  have huC : u ∈ center G := by
    apply Glauberman.ZStar.central_of_isolated_of_oddCore_eq_bot hu hcore
    intro g hg
    let v := g * u * g⁻¹
    have huv : IsConj u v := isConj_iff.mpr ⟨g, rfl⟩
    rcases hcensus v (mem_centralizer_singleton_iff.mpr hg.eq)
      (involution_isConj hu huv) with he | hvZ | hcv
    · exact he
    · have hh := h.invariant g⁻¹ v hvZ
      exact False.elim (huZ (by simpa only [v, MulAut.conj_apply, inv_inv, mul_assoc,
        inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hh))
    · exact False.elim (hnot (huv.trans hcv.symm))
  rw [r.center_eq_bot h, mem_bot] at huC
  exact hu.ne_one huC
end BenderSuzuki.ZD

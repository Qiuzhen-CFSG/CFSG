module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.BasicSubgroups
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.CocodeActions
/-!
# Uniqueness of Parker triality normal-form words

The action on the first axis induces the affine Golay map
`a ↦ ᾱ(a + e.code)`. Together with the second axis this recovers the code
parts of `d` and `e`. Loop sandwiches depend only on the code, and standard
automorphisms fix both signs of the identity; these facts recover the signs
and the full automorphism. The permutation of axes detects its parity.

This proves uniqueness, and the exact `NPlus` membership criterion, for the
concrete words defined in `BasicSubgroups`. Existence is a separate collection
argument; no surjectivity or subgroup presentation is assumed here.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.4(4), printed pp. 61–62,
and the defining permutations and parity convention on pp. 58–59.
-/

@[expose] public section
open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin

private theorem loop_mul_twice (a d : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply a d) d =
      parkerSign (golayQuarterWeight d.1) a := by
  rw [parkerLoopMultiply_associator, parkerTripleIntersection_repeat, parkerSign_zero,
    parkerLoopMultiply_square]
  have hs : (0, golayQuarterWeight d.1) = parkerSign (golayQuarterWeight d.1) loopOne := by
    simp [parkerSign, loopOne]
  rw [hs, parkerLoopMultiply_sign_right, loopOne, parkerLoopMultiply_one_right]

theorem normalForm_sandwich (d a : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply (loopInverse d) a) (loopInverse d) =
      parkerSign (golayQuarterWeight d.1 + golayHalfOverlap d.1 a.1) a := by
  rw [parkerLoopMultiply_commutator (loopInverse d) a,
    parkerLoopMultiply_sign_left, loop_mul_twice, parkerSign_add]
  exact congrArg (fun s => parkerSign s a) (add_comm _ _)

theorem parkerStandard_preserves_inverse (α : ParkerStandardGroup) (x : ParkerLoop) :
    α.val (loopInverse x) = loopInverse (α.val x) := by
  apply (loopRight (α.val x)).injective
  change parkerLoopMultiply (α.val (loopInverse x)) (α.val x) =
    parkerLoopMultiply (loopInverse (α.val x)) (α.val x)
  rw [← α.prop.1, loopInverse_mul, loopInverse_mul]
  exact α.prop.2.1 0

private theorem flip1_diagonal (α : ParkerStandardGroup) :
    flip1 * diagonal α.val = diagonal α.val * flip1 := by
  ext ⟨a,b,c⟩ : 1
  simp only [Equiv.Perm.mul_apply, flip1, diagonal, Equiv.coe_fn_mk,
    Equiv.prodCongr_apply]
  have hi (a : LoopZero) : inverseZero (a.map α.val) = (inverseZero a).map α.val := by
    cases a with
    | none => rfl
    | some a => simpa using congrArg some (parkerStandard_preserves_inverse α a).symm
  exact Prod.ext (hi a) (Prod.ext (hi c) (hi b))

private def straightWord (d e : ParkerLoop) (α : ParkerStandardGroup) : Equiv.Perm Triple :=
  diagonal α.val * psi2 e * psi1 d

private theorem straightWord_axis1 (d e a : ParkerLoop) (α : ParkerStandardGroup) :
    straightWord d e α (axis1 a) = axis1 (α.val (parkerLoopMultiply
      (parkerSign (golayQuarterWeight d.1 + golayHalfOverlap d.1 a.1) a) e)) := by
  simp [straightWord, axis1, diagonal, normalForm_sandwich]

private theorem straightWord_axis2 (d e a : ParkerLoop) (α : ParkerStandardGroup) :
    straightWord d e α (axis2 a) = axis2 (α.val
      (parkerSign (golayQuarterWeight e.1 + golayHalfOverlap e.1
        (parkerLoopMultiply d a).1) (parkerLoopMultiply d a))) := by
  simp [straightWord, axis2, diagonal, normalForm_sandwich]

private theorem straightWord_injective {d e d' e' : ParkerLoop}
    {α α' : ParkerStandardGroup} (h : straightWord d e α = straightWord d' e' α') :
    d = d' ∧ e = e' ∧ α = α' := by
  have h1 (a : ParkerLoop) : α.val (parkerLoopMultiply
      (parkerSign (golayQuarterWeight d.1 + golayHalfOverlap d.1 a.1) a) e) =
      α'.val (parkerLoopMultiply
      (parkerSign (golayQuarterWeight d'.1 + golayHalfOverlap d'.1 a.1) a) e') := by
    have ht := congrArg (fun f : Equiv.Perm Triple => (f (axis1 a)).1) h
    rw [straightWord_axis1, straightWord_axis1] at ht
    exact Option.some.inj ht
  have h1c (a : golay) :
      parkerCodeEquiv (parkerStandardProjection α) (a + e.1) =
      parkerCodeEquiv (parkerStandardProjection α') (a + e'.1) := by
    have ht := congrArg Prod.fst (h1 (a,0))
    simpa only [parkerStandardProjection_spec, parkerLoopMultiply, parkerMultiply, parkerSign] using ht
  have h0 : parkerCodeEquiv (parkerStandardProjection α) e.1 =
      parkerCodeEquiv (parkerStandardProjection α') e'.1 := by
    simpa only [zero_add] using h1c 0
  have hproj : parkerStandardProjection α = parkerStandardProjection α' := by
    apply parkerCodeEquiv_faithful
    intro a
    have ht := h1c a
    rw [map_add, map_add, h0] at ht
    exact add_right_cancel ht
  have he : e.1 = e'.1 := by
    rw [hproj] at h0
    exact (parkerCodeEquiv _).injective h0
  have h2 (a : ParkerLoop) : α.val
      (parkerSign (golayQuarterWeight e.1 + golayHalfOverlap e.1
        (parkerLoopMultiply d a).1) (parkerLoopMultiply d a)) = α'.val
      (parkerSign (golayQuarterWeight e'.1 + golayHalfOverlap e'.1
        (parkerLoopMultiply d' a).1) (parkerLoopMultiply d' a)) := by
    have ht := congrArg (fun f : Equiv.Perm Triple => (f (axis2 a)).2.1) h
    rw [straightWord_axis2, straightWord_axis2] at ht
    exact Option.some.inj ht
  have hd : d.1 = d'.1 := by
    have ht := congrArg Prod.fst (h2 loopOne)
    simp only [loopOne, parkerLoopMultiply_one_right, parkerStandardProjection_spec] at ht
    change parkerCodeEquiv (parkerStandardProjection α) d.1 =
      parkerCodeEquiv (parkerStandardProjection α') d'.1 at ht
    rw [hproj] at ht
    exact (parkerCodeEquiv _).injective ht
  have ht (a : ParkerLoop) : α.val (parkerLoopMultiply a e) =
      α'.val (parkerLoopMultiply a e') := by
    let s : Equiv.Perm ParkerLoop := (loopLeft (loopInverse d)).trans (loopRight (loopInverse d))
    obtain ⟨b,hb⟩ := s.surjective a
    have hb' : parkerSign (golayQuarterWeight d.1 + golayHalfOverlap d.1 b.1) b = a := by
      simpa only [s, Equiv.trans_apply, loopLeft, loopRight, Equiv.coe_fn_mk, normalForm_sandwich] using hb
    have hh := h1 b
    rw [← hd, hb'] at hh
    exact hh
  have hee : e = e' := by
    let t := e'.2 + e.2
    have he' : e' = parkerSign t e := by
      apply Prod.ext
      · exact he.symm
      change e'.2 = e.2 + t
      change e'.2 = e.2 + (e'.2 + e.2)
      rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
    have hh := ht (loopInverse e)
    rw [he', parkerLoopMultiply_sign_right, loopInverse_mul,
      parkerStandard_preserves_sign, loopOne, α.prop.2.1, α'.prop.2.1] at hh
    have hz : t = 0 := by
      have hh' := congrArg Prod.snd hh
      simpa [loopOne, parkerSign] using hh'.symm
    simpa only [hz, parkerSign_zero] using he'.symm
  have haa : α = α' := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    obtain ⟨b,rfl⟩ := (loopRight e).surjective a
    simpa only [hee, loopRight, Equiv.coe_fn_mk] using ht b
  have hdd : d = d' := by
    subst e'
    subst α'
    have hh := h2 loopOne
    simp only [loopOne, parkerLoopMultiply_one_right] at hh
    have hh' := α.val.injective hh
    rw [← hd] at hh'
    have hsg : Function.Injective (parkerSign
        (golayQuarterWeight e.1 + golayHalfOverlap e.1 d.1)) := by
      intro a b hab
      apply Prod.ext
      · simpa only [parkerSign] using congrArg Prod.fst hab
      · exact add_right_cancel (congrArg Prod.snd hab)
    exact hsg hh'
  exact ⟨hdd,hee,haa⟩

private theorem normalForm_axis2_support (d e : ParkerLoop) (α : ParkerStandardGroup) :
    (((normalForm d e α).val.val (axis2 loopOne)).2.1).isSome =
      decide (α.val parkerOmega = parkerOmega) := by
  classical
  by_cases ha : α.val parkerOmega = parkerOmega <;>
    simp [normalForm, psiAut1N, psi1N, psi2N, psiAut1, ha, diagonal, flip1, axis2]

private theorem normalForm_straight_even (d e : ParkerLoop) (α : ParkerStandardGroup)
    (ha : α.val parkerOmega = parkerOmega) :
    (normalForm d e α).val.val = straightWord d e α := by
  simp [normalForm, psiAut1N, psi1N, psi2N, psiAut1, ha, straightWord]

private theorem normalForm_straight_odd (d e : ParkerLoop) (α : ParkerStandardGroup)
    (ha : α.val parkerOmega ≠ parkerOmega) :
    (normalForm d e α).val.val = flip1 * straightWord d e α := by
  have heq : (normalForm d e α).val.val =
      diagonal α.val * flip1 * psi2 e * psi1 d := by
    simp [normalForm, psiAut1N, psi1N, psi2N, psiAut1, ha, Equiv.Perm.mul_def]
  rw [heq, ← flip1_diagonal, mul_assoc, mul_assoc]
  rfl

theorem normalForm_injective : Function.Injective
    (fun x : ParkerLoop × ParkerLoop × ParkerStandardGroup => normalForm x.1 x.2.1 x.2.2) := by
  classical
  rintro ⟨d,e,α⟩ ⟨d',e',α'⟩ h
  have ht := congrArg (fun g : N1 => g.val.val) h
  have hp := congrArg (fun g : N1 => ((g.val.val (axis2 loopOne)).2.1).isSome) h
  simp only [normalForm_axis2_support, decide_eq_decide] at hp
  have hs : straightWord d e α = straightWord d' e' α' := by
    by_cases ha : α.val parkerOmega = parkerOmega
    · rw [normalForm_straight_even d e α ha,
        normalForm_straight_even d' e' α' (hp.mp ha)] at ht
      exact ht
    · rw [normalForm_straight_odd d e α ha,
        normalForm_straight_odd d' e' α' (fun he => ha (hp.mpr he))] at ht
      exact mul_left_cancel ht
  obtain ⟨rfl,rfl,rfl⟩ := straightWord_injective hs
  rfl

theorem NPlus_preserves_axis2_support {g : N} (hg : g ∈ NPlus) (x : Triple) :
    (g.val x).2.1.isSome = x.2.1.isSome := by
  induction hg using Subgroup.closure_induction generalizing x with
  | mem g hg =>
    rcases hg with ⟨d, hg | hg | hg⟩ | ⟨α, _, _, hg⟩
    · rw [hg]
      rcases x with ⟨a,b,c⟩
      cases b <;> simp
    · rw [hg]
      rcases x with ⟨a,b,c⟩
      cases b <;> simp
    · rw [hg]
      rcases x with ⟨a,b,c⟩
      cases b <;> simp
    · rw [hg]
      rcases x with ⟨a,b,c⟩
      cases b <;> rfl
  | one => rfl
  | mul g h _ _ ihg ihh =>
    exact (ihg (h.val x)).trans (ihh x)
  | inv g _ ih =>
    have ht := ih (g.val.symm x)
    simpa only [Subgroup.coe_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using ht.symm

theorem normalForm_mem_NPlus_iff (d e : ParkerLoop) (α : ParkerStandardGroup) :
    (normalForm d e α).val ∈ NPlus ↔ α.val parkerOmega = parkerOmega := by
  classical
  constructor
  · intro hg
    have ht := NPlus_preserves_axis2_support hg (axis2 loopOne)
    rw [normalForm_axis2_support] at ht
    exact of_decide_eq_true ht
  · intro ha
    apply NPlus.mul_mem
    · apply NPlus.mul_mem
      · apply Subgroup.subset_closure
        right
        refine ⟨α.val, α.prop, ha, ?_⟩
        simp [psiAut1N, psiAut1, ha]
      · apply Subgroup.subset_closure
        exact Or.inl ⟨e, Or.inr (Or.inl rfl)⟩
    · apply Subgroup.subset_closure
      exact Or.inl ⟨d, Or.inl rfl⟩

theorem q1Word_injective : Function.Injective
    (fun x : ParkerLoop × ParkerBit × Cocode => q1Word x.1 x.2.1 x.2.2) := by
  rintro ⟨d,t,c⟩ ⟨d',t',c'⟩ h
  have ht : (d, ((0 : golay),t), parkerCocodeStandard c) =
      (d', (0,t'), parkerCocodeStandard c') :=
    normalForm_injective (a₁ := (d,(0,t),parkerCocodeStandard c))
      (a₂ := (d',(0,t'),parkerCocodeStandard c')) (by
        simpa only [q1Word] using h)
  have hd : d = d' := congrArg Prod.fst ht
  have htt : t = t' := congrArg (fun x => x.2.1.2) ht
  have hc : c = c' := by
    apply Multiplicative.ofAdd.injective
    apply parkerCocodeEmbedding_injective
    exact congrArg (fun x => x.2.2) ht
  exact Prod.ext hd (Prod.ext htt hc)
end Sporadic.Monster.Construction.TrialitySpin

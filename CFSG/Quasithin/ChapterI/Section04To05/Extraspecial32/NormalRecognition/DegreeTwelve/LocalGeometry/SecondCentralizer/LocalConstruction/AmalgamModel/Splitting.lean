module
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.Inputs
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.AmalgamModel.Action
public import Theory.GroupTheory.ElementaryCoreSymmetricFour
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction

/-!
# Splitting the local elementary extension

Conjugation on the normal four-group V identifies C/E with Aut(V) = S₃.
A central element in V would force the action image to have order at most
two, contradicting its order six. Thus the ambient center meets V trivially,
has order at most two, and E is V joined with that center. The checked
central-extension splitting theorem applies to an involution outside E.
Its S₄ alternative is excluded by |C| = 48, leaving an actual C₂ × S₄
isomorphism. The marking is proved separately, without choosing a special
isomorphism in this step.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 4.1 and the opening of Lemma 4.2, pp.38–39.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer.Amalgam
open Subgroup
open scoped IsMulCommutative

private theorem model_of_elementary_extension
    {K : Type*} [Group K] [Finite K] (E V : Subgroup K)
    [E.Normal] [V.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (hV : Nat.card V = 4)
    (hcent : centralizer (E : Set K) ≤ E)
    (t : K) (htZ : t ∈ center K) (hsplit : E = V ⊔ zpowers t)
    (hK : Nat.card K = 48) (hout : ∃ r : K, r ∉ E ∧ r ^ 2 = 1) :
    Nonempty (K ≃* Model 4) := by
  have hVE : V ≤ E := hsplit ▸ le_sup_left
  let : IsElementaryAbelian 2 V := {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (congrArg (fun q : E => (q : K))
      (mul_comm (⟨x, hVE x.property⟩ : E) ⟨y, hVE y.property⟩))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := E) x (hVE x.property))) }
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour V := ⟨hV, IsElementaryAbelian.exponent_eq_prime⟩
  have hCV : centralizer (V : Set K) = E := by
    apply le_antisymm ?_ (E.le_centralizer.trans (centralizer_le (by exact hVE)))
    intro x hx
    apply hcent
    have hj : E ≤ centralizer ({x} : Set K) := by
      rw [hsplit]
      apply sup_le
      · intro v hv
        exact mem_centralizer_singleton_iff.mpr (hx v hv)
      · apply zpowers_le.mpr
        exact center_le_centralizer _ htZ
    intro e he
    exact (mem_centralizer_singleton_iff.mp (hj he))
  let f : K →* MulAut V := MulAut.conjNormal
  have hker : f.ker = E := by
    rw [← hCV]
    ext x
    constructor
    · intro hx v hv
      have he := congrArg (fun k : MulAut V => (k ⟨v, hv⟩ : K)) hx
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hx
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hx v v.property).symm
  have hR : Nat.card f.range = 6 := by
    have hc := f.ker.card_mul_index
    rw [hker, hE, hK, ← hker, index_ker] at hc
    omega
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply eq_of_le_of_card_ge le_top
    rw [card_top, IsKleinFour.card_mulAut, hR]
  have hVZ : V ⊓ center K = ⊥ := by
    apply le_antisymm ?_ bot_le
    rintro x ⟨hxV, hxZ⟩
    by_contra hx1
    have hxne : (⟨x, hxV⟩ : V) ≠ 1 := fun he => hx1 (congrArg Subtype.val he)
    have hb := card_mulAut_subgroup_le_two_of_fixed_point hV ⟨x, hxV⟩ hxne f.range (by
      rintro _ ⟨m, rfl⟩
      apply Subtype.ext
      change m * x * m⁻¹ = x
      rw [mem_center_iff.mp hxZ m, mul_inv_cancel_right])
    omega
  have hZE : center K ≤ E := (center_le_centralizer _).trans hcent
  have hZcard : Nat.card (center K) ≤ 2 := by
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes V (center K) (by
      rw [V.normalizer_eq_top]; exact le_top)
    rw [hVZ, card_bot, one_mul, hV] at hc
    have hb := Nat.card_le_card_of_injective _ (inclusion_injective (show V ⊔ center K ≤ E from sup_le hVE hZE))
    rw [hE, ← hc] at hb
    omega
  have hsplit' : E = V ⊔ center K := by
    apply le_antisymm ?_ (sup_le hVE hZE)
    rw [hsplit]
    exact sup_le_sup_left (zpowers_le.mpr htZ) V
  have hquot : Nonempty (K ⧸ E ≃* Equiv.Perm (Fin 3)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).trans
        (IsKleinFour.autEquivPermThree V)⟩
  rcases elementary_core_symmetric_four_or_c2_product E V hcent hsplit' hVZ hV hZcard hquot hout
      with he | he
  · obtain ⟨e⟩ := he
    have hc := Nat.card_congr e.toEquiv
    rw [hK, Nat.card_eq_fintype_card, Fintype.card_perm] at hc
    norm_num at hc
  · exact he

/-- The local eight-by-six extension splits once an involution outside E is given. -/
public theorem nonempty_unmarked_of_outside
    {G : Type*} [Group G] [Finite G] {z t : G} (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (r : localCentralizer z t a.g) (hr : orderOf r = 2) (hrE : r ∉ eight z t a.g) :
    Nonempty (localCentralizer z t a.g ≃* Model 4) := by
  let : (eight z t a.g).Normal := eight_normal h a t
  let : (four z t a.g).Normal := four_normal h d a t
  let : IsElementaryAbelian 2 (eight z t a.g) := eight_elementary h a htE
  exact model_of_elementary_extension (eight z t a.g) (four z t a.g)
    (eight_card h a htE) (four_card h d a htE) (eight_self_centralizing h a htE).le
    (centralElement h a htE) (centralElement_mem_center h a htE)
    (eight_eq_four_sup_central h d a htE ht hnt) (local_card h d a htE ht hnt)
    ⟨r, hrE, hr ▸ pow_orderOf_eq_one r⟩

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer.Amalgam

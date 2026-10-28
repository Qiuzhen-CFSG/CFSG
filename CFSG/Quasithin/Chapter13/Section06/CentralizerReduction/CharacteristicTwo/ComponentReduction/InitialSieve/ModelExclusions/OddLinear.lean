module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.QuotientAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.SmallModels
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.Alternating
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.OddCenters
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.Alternating.SmallInvolutionCentralizers
public import GorensteinWalter.LinearThreeEquiv
public import Theory.GroupTheory.PPerfectHom

/-!
# Excluding the odd-linear component alternative

The full odd-linear alternative of 1.1.5(3)(e) retains actual model
isomorphisms. PSL₃(3) is already excluded in SmallModels. For prime-field
PSL₂, every pointwise Sylow fixer is inner. At Fermat or Mersenne primes
at least seven, its order is bounded by the Sylow center of order two,
contradicting the faithful central four-group.

At five the Sylow subgroup itself is a four-group, so that bound is false.
Instead the actual marked element a induces a nontrivial inner involution
of A₅. Its centralizer in Aut(A₅), computed through the genuine S₅ action,
has order eight. Since a centralizes the two-perfect residual O²(C_L(v)),
the residual action is trivial, contradicting [K, O²(C_L(v))] = K.
The remaining prime three is excluded by perfectness and PSL₂(3) ≃ A₄.

All maps are the prescribed normalizer actions or transports of them.
The proof uses no normalization of K by Tᵥ, and requires no additional
innerness or odd-core premise beyond the supplied Setup and ActionData.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3)(e), printed pp.501–503; proof of 13.6.6, printed p.927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.OddLinear
open A5Module

private theorem fixer_card_le_center {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (A : Subgroup (MulAut H))
    (hfix : ∀ α ∈ A, ∀ x ∈ S, α x = x)
    (hinner : ∀ α ∈ A, ∃ g ∈ S, α = MulAut.conj g) :
    Nat.card A ≤ Nat.card (center S) := by
  classical
  choose g hg he using fun α : A => hinner α α.property
  have hc (α : A) : (⟨g α, hg α⟩ : S) ∈ center S := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have hx := hfix α α.property x x.property
    rw [he α] at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  let f : A → center S := fun α => ⟨⟨g α, hg α⟩, hc α⟩
  apply Nat.card_le_card_of_injective f
  intro α β h
  apply Subtype.ext
  have hg' : g α = g β := congrArg (fun x : center S => (x.val : H)) h
  exact (he α).trans ((congrArg MulAut.conj hg').trans (he β).symm)

private theorem centerless_equiv {H Q : Type*} [Group H] [Group Q]
    (e : H ≃* Q) (hq : center Q = ⊥) : center H = ⊥ := by
  apply card_eq_one.mp
  rw [Nat.card_congr (centerCongr e).toEquiv, hq, card_bot]

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

private noncomputable def centerlessModel {Q : Type*} [Group Q]
    (K : Subgroup (Gv (markedV s))) (e : K ≃* Q) (hc : center Q = ⊥) :
    NormalizerAction.componentImage K ≃* Q :=
  (NormalizerAction.componentCentralQuotientEquiv K).symm.trans
    (((QuotientGroup.quotientMulEquivOfEq (centerless_equiv e hc)).trans
      QuotientGroup.quotientBot).trans e)

private theorem not_large_prime (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (a : ActionData s (T : Subgroup G) K)
    {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    (hpk : ∃ k, p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k)
    (e : K ≃* PSL(2, ZMod p)) : False := by
  obtain ⟨S, A, hA, hfix⟩ := exists_fixed_four_of_equiv K hK a
    (centerlessModel K e (GorensteinWalter.psl2_center_eq_bot (ZMod p)))
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hbound := fixer_card_le_center S A hfix (fun α hα =>
    Theory.PSL2.primeField_sylow_fixed_inner hpodd (by omega) S α (hfix α hα))
  obtain ⟨k, hk⟩ := hpk
  have hcenter := Theory.PSL2.SylowFixedQuotients.sylow_center_card_le_two_of_adjacent_power
    hp7 hk S
  rw [hA.card_four] at hbound
  omega

/-- Keep the literal elements of E* when transporting the pointwise Sylow action. -/
private theorem exists_model_fixed_sylow {Q : Type*} [Group Q]
    (K : Subgroup (Gv (markedV s)))
    (a : ActionData s (T : Subgroup G) K)
    (e : NormalizerAction.componentImage K ≃* Q) :
    ∃ S : Sylow 2 Q, ∀ y ∈ EStar s K a.a_normalizes a.z_normalizes,
      ∀ x ∈ S, MulAut.congr e (quotientAction K y) x = x := by
  obtain ⟨P, hP⟩ := a.sylow
  let := componentImage_normal K
  obtain ⟨S, hS⟩ := P.exists_subgroupOf_eq_of_normal (NormalizerAction.componentImage K)
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro y hy _ ⟨x, hx, rfl⟩
  change e (quotientAction K y (e.symm (e x))) = e x
  rw [e.symm_apply_apply]
  congr 1
  apply Subtype.ext
  rw [quotientAction_apply]
  have hxP : (x : XStar K) ∈ (P : Subgroup (XStar K)) := by
    change x ∈ (S : Subgroup (NormalizerAction.componentImage K)) at hx
    rw [hS] at hx
    exact hx
  obtain ⟨c, hc, he⟩ := a.central hy
  have hxI : (x : XStar K) ∈ NormalizerAction.sylowImage K
      (localT (T : Subgroup G) (markedV s)) := hP ▸ hxP
  have hcomm := congrArg Subtype.val (mem_center_iff.mp hc ⟨x, hxI⟩)
  change (x : XStar K) * c.val = c.val * x at hcomm
  change c.val = y at he
  rw [he] at hcomm
  rw [← hcomm, mul_inv_cancel_right]

private theorem a5_twoPerfect_action_trivial {D : Type*} [Group D]
    (hD : IsPPerfect 2 D) (f : D →* MulAut (alternatingGroup (Fin 5)))
    (g : alternatingGroup (Fin 5)) (hg : orderOf g = 2)
    (hc : ∀ d, Commute (f d) (MulAut.conj g)) : f = 1 := by
  let e : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  have he : e (g : Equiv.Perm (Fin 5)) = MulAut.conj g := by
    ext x
    rfl
  let C := centralizer ({(g : Equiv.Perm (Fin 5))} : Set (Equiv.Perm (Fin 5)))
  have hC : IsPGroup 2 C := by
    apply IsPGroup.of_card (n := 3)
    rw [Equiv.Perm.nat_card_centralizer,
      alternatingGroup.involution_cycleType_of_degree_le_six (by decide) g hg]
    norm_num
  let r : D →* C := (e.symm.toMonoidHom.comp f).codRestrict C (by
    intro d
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.apply_symm_apply, he] using (hc d).eq)
  have hr := hD.hom_eq_one_of_isPGroup hC r
  apply MonoidHom.ext
  intro d
  have hd := congrArg (fun c : C => e c.val) (DFunLike.congr_fun hr d)
  simpa only [r, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, e.apply_symm_apply, MonoidHom.one_apply,
    coe_one, map_one] using hd

private theorem not_five {κ : CFSG.Quasithin.GroupClass}
    (d : Setup κ T s) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (a : ActionData s (T : Subgroup G) K)
    (eK : K ≃* alternatingGroup (Fin 5)) : False := by
  let e := centerlessModel K eK (alternatingGroup.center_eq_bot (by simp))
  let f : XStar K →* MulAut (alternatingGroup (Fin 5)) :=
    (MulAut.congr e).toMonoidHom.comp (quotientAction K)
  have hf : Function.Injective f := (MulAut.congr e).injective.comp
    (quotientAction_injective K hK)
  let aX : X K := ⟨aLocal s, a.a_normalizes⟩
  let aa := NormalizerAction.quotient K aX
  have haa : aa ∈ EStar s K a.a_normalizes a.z_normalizes :=
    subset_closure (Set.mem_insert _ _)
  have haa2 : aa ^ 2 = 1 := by
    rw [← a.four.exponent_two]
    exact Subgroup.pow_exponent_eq_one haa
  have hKne : K ≠ ⊥ := by
    let : Nontrivial K := eK.surjective.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance
  have haa1 : aa ≠ 1 := by
    intro h
    have hc := (NormalizerAction.quotient_eq_one_iff K aX).mp h
    have hz : zpowers (aLocal s) ≤ centralizer (K : Set (Gv (markedV s))) :=
      zpowers_le.mpr hc
    have hb : ⁅K, zpowers (aLocal s)⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hz)
    exact hKne (a.commutator_a.symm.trans hb)
  obtain ⟨S, hS⟩ := exists_model_fixed_sylow K a e
  obtain ⟨g, _, hg⟩ := Theory.PSL2.SylowFixedQuotients.alternating_sylow_fixed_inner
    S (f aa) (hS aa haa)
  have hconj : Function.Injective (MulAut.conj : alternatingGroup (Fin 5) →*
      MulAut (alternatingGroup (Fin 5))) := by
    intro x y hxy
    apply Subtype.ext
    apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 5 (by decide)
    exact hxy
  have hg2 : orderOf g = 2 := by
    apply (orderOf_eq_prime_iff (p := 2)).mpr
    constructor
    · apply hconj
      rw [map_pow, ← hg, ← map_pow, haa2, map_one, map_one]
    · intro hg1
      apply haa1
      apply hf
      rw [map_one, hg, hg1, map_one]
  let r : residual s →* MulAut (alternatingGroup (Fin 5)) :=
    f.comp ((NormalizerAction.quotient K).comp (inclusion a.residual_normalizes))
  have hr : r = 1 := a5_twoPerfect_action_trivial (residual_two_perfect s) r g hg2 (by
    intro x
    rw [← hg]
    have hx : Commute (inclusion a.residual_normalizes x) aX := by
      apply Subtype.ext
      apply Subtype.ext
      exact mem_centralizer_iff.mp d.a_centralizes x x.property
    exact (hx.map (NormalizerAction.quotient K)).map f)
  have hc : residual s ≤ centralizer (K : Set (Gv (markedV s))) := by
    intro x hx
    apply (NormalizerAction.quotient_eq_one_iff K ⟨x, a.residual_normalizes hx⟩).mp
    apply hf
    have hh := DFunLike.congr_fun hr ⟨x, hx⟩
    change f (NormalizerAction.quotient K (inclusion a.residual_normalizes ⟨x, hx⟩)) = 1 at hh
    have he : inclusion a.residual_normalizes (⟨x, hx⟩ : residual s) =
        (⟨x, a.residual_normalizes hx⟩ : X K) := rfl
    rw [he] at hh
    simpa only [map_one] using hh
  have hb : ⁅K, residual s⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
  exact hKne (a.commutator_residual.symm.trans hb)

omit [Finite G] in
private theorem not_three (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (e : K ≃* PSL(2, ZMod 3)) : False := by
  let : IsQuasisimple K := hK.2
  let eA := e.trans GorensteinWalter.psl2_three_equiv_alternatingGroup
  let : Nontrivial K := eA.surjective.nontrivial
  let : Group.IsSolvable (alternatingGroup (Fin 4)) :=
    ⟨⟨2, by
      change ⁅commutator (alternatingGroup (Fin 4)),
        commutator (alternatingGroup (Fin 4))⁆ = ⊥
      rw [← alternatingGroup.kleinFour_eq_commutator (by simp)]
      exact Subgroup.commutator_self_eq_bot_iff.mpr
        (alternatingGroup.kleinFour_isKleinFour (by simp)).isMulCommutative⟩⟩
  exact Group.IsPerfect.not_isSolvable K
    (Group.isSolvable_of_surjective (f := eA.symm.toMonoidHom) eA.symm.surjective)

private theorem fermatMersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  rintro rfl
  rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hlow : 2 ≤ 2 ^ (2 ^ a) := Nat.le_pow (by norm_num)
    omega
  · have hd : 2 ∣ 2 ^ a := dvd_pow_self _ (by rintro rfl; norm_num at ha)
    omega

/-- The prime-field PSL₂ part of source alternative (e), including p = 3, 5, 7. -/
theorem not_linear_two {κ : CFSG.Quasithin.GroupClass}
    (d : Setup κ T s) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (a : ActionData s (T : Subgroup G) K)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) : ¬ ClassicalGroup.IsPSL K 2 p := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let : Fact p.Prime := ⟨hp.1⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p :=
    (ZMod.ringEquivOfPrime F hp.1 (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let eP : K ≃* PSL(2, ZMod p) := e.trans (Atlas.fieldEquivPSL 2 eF)
  have hodd := fermatMersenne_odd hp
  by_cases h3 : p = 3
  · subst h3
    exact not_three K hK eP
  by_cases h5 : p = 5
  · subst h5
    obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
    exact not_five d K hK a (eP.trans eA)
  have hp7 : 7 ≤ p := by
    have := hp.1.two_le
    obtain ⟨m, hm⟩ := hodd
    omega
  apply not_large_prime K hK a hp7 _ eP
  rcases hp.2 with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨2 ^ m, Or.inl (by omega)⟩
  · exact ⟨m, Or.inr hm⟩

/-- Exclude the complete odd-linear source alternative 1.1.5(3)(e). -/
theorem not_odd_linear {κ : CFSG.Quasithin.GroupClass}
    (d : Setup κ T s) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (a : ActionData s (T : Subgroup G) K) :
    ¬ (ClassicalGroup.IsPSL K 3 3 ∨
      ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL K 2 p) := by
  rintro (h | ⟨p, hp, hm⟩)
  · exact not_linear_three_three K hK a h
  · exact not_linear_two d K hK a hp hm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.OddLinear

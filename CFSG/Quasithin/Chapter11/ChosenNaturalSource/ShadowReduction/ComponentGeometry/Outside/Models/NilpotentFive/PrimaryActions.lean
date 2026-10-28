module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.OmegaActions.Nilpotent
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.OddPrimeSectionCentralizers.Involution
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Theory.SpecificGroups.SL2.OddCoreAndRank
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.CharacteristicOuterRestriction

/-!
# Faithful restriction to the full nilpotent Fitting kernel

For the nilpotent A.3.6 alternative, the proved central-involution action
identifies every omega--Frattini kernel with F(B). Thus each involution outside
F(B) has cyclic fixed subgroup in every primary core, using the SQTK rank bound.
No core is replaced by its elementary quotient in the conclusion.

Choose an involution in B. Its image in the actual SL₂(5) Fitting quotient is
central. The fixed subgroup in C_B(F(B)) is normal in B; each of its primary
cores embeds in the corresponding cyclic fixed subgroup. Perfectness centralizes
these cyclic normal cores and hence the whole fixed subgroup. The odd-kernel
restriction theorem now proves that every automorphism fixing F(B) is inner.
Consequently Out(B) embeds in the normalizer quotient of its Fitting action.

The primary normalizer calculation remains separate. Both extraspecial kernels
and rank-two homocyclic kernels with every positive exponent are retained.
Source: Aschbacher--Smith, A.3.6(4) and its proof, printed pp.43--45;
11.4.3, printed p.778. No center--Frattini equality or splitting is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive
variable {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]

/-- The actual omega–Frattini action detects precisely the Fitting subgroup. -/
theorem omegaAction_kernel (h : A36Nilpotent B) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup B)) :
    (RadicalActions.omegaFrattiniAction p B).ker = fittingSubgroup B := by
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by
    intro he
    have hc := (h.2.2.2 p Fact.out (h.1.symm ▸ hd)).1
    norm_num [he] at hc)
  obtain ⟨e, hz⟩ := CenterFrattiniSource.nilpotent_exists_inverting_quotient h hp hd
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact RadicalActions.Nilpotent.action_ker_eq_fitting_of_inversion
    (K := B) (p := p) (F := ZMod 5) h hd
    (by simp : Nat.card (ZMod 5) = 5) e hz

/-- The whole primary core, including every homocyclic exponent, has cyclic
fixed subgroup under the original involution outside F(B). -/
theorem primary_fixed_cyclic {𝒦 : GroupClass} (hQ : IsSQTK 𝒦 B)
    (h : A36Nilpotent B) (t : B) (ht : t ^ 2 = 1)
    (hnt : t ∉ fittingSubgroup B) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup B)) :
    IsCyclic (MulAut.conjNormal t : MulAut (pCore p B)).fixedSubgroup := by
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by
    intro he
    have hc := (h.2.2.2 p Fact.out (h.1.symm ▸ hd)).1
    norm_num [he] at hc)
  let a : MulAut (pCore p B) := MulAut.conjNormal t
  have ha2 : a ^ 2 = 1 := by
    change MulAut.conjNormal t ^ 2 = 1
    rw [← map_pow, ht, map_one]
  apply cyclic_fixedSubgroup_of_involution_rank_le_two pCore_isPGroup hp
    ((primeRank_subgroup_le p _).trans (hQ.stronglyQuasithin p Fact.out hp))
    a (fun x => DFunLike.congr_fun ha2 x)
  intro ha
  apply hnt
  rw [← omegaAction_kernel h hd]
  change RadicalActions.omegaFrattiniAction p B t = 1
  have hw : RadicalActions.omegaCoreAction p B t = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    have hx := RadicalActions.Nilpotent.omega_le_core x.property
    have hh := congrArg (fun a : MulAut (pCore p B) => (a ⟨x, hx⟩ : B)) ha
    exact hh
  change quotientAut (frattini (RadicalActions.omegaCore p B))
    (RadicalActions.omegaCoreAction p B t) = 1
  rw [hw, map_one]

omit [Group.IsPerfect B] in
/-- Self-centralization uses the full generalized Fitting equality. -/
theorem fitting_selfCentralizing (h : A36Nilpotent B) :
    centralizer (fittingSubgroup B : Set B) ≤ fittingSubgroup B := by
  rw [← h.1]
  exact centralizer_generalizedFitting_le B

omit [Finite B] [Group.IsPerfect B] in
private theorem fixed_centralizer_normal (N : Subgroup B) [N.Normal]
    (t : B) (ht : QuotientGroup.mk' N t ∈ center (B ⧸ N)) :
    (centralizer (N : Set B) ⊓ centralizer ({t} : Set B)).Normal := by
  refine ⟨?_⟩
  intro x hx g
  refine ⟨(inferInstance : (centralizer (N : Set B)).Normal).conj_mem x hx.1 g, ?_⟩
  have hn : g⁻¹ * t * g * t⁻¹ ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (g⁻¹ * t * g * t⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      mem_center_iff.mp ht, inv_mul_cancel_right, mul_inv_cancel]
  have hc : Commute x (g⁻¹ * t * g) := by
    have hncomm : Commute x (g⁻¹ * t * g * t⁻¹) := (hx.1 _ hn).symm
    have htcomm : Commute x t := mem_centralizer_singleton_iff.mp hx.2
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hncomm.mul_right htcomm
  apply mem_centralizer_singleton_iff.mpr
  have he := (hc.map (MulAut.conj g).toMonoidHom).eq
  change (g * x * g⁻¹) * (g * (g⁻¹ * t * g) * g⁻¹) =
    (g * (g⁻¹ * t * g) * g⁻¹) * (g * x * g⁻¹) at he
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
    mul_inv_cancel_right, mul_inv_cancel, mul_one] using he

/-- Fixed points in C_B(F(B)) are central in B. The proof retains the specified
involution and treats the primary factors through their actual action. -/
theorem fitting_centralizer_fixed_le_center {𝒦 : GroupClass} (hQ : IsSQTK 𝒦 B)
    (h : A36Nilpotent B) (t : B) (ht : t ^ 2 = 1)
    (hnt : t ∉ fittingSubgroup B)
    (htcentral : QuotientGroup.mk' (fittingSubgroup B) t ∈
      center (B ⧸ fittingSubgroup B)) :
    centralizer (fittingSubgroup B : Set B) ⊓ centralizer ({t} : Set B) ≤ center B := by
  let F := fittingSubgroup B
  let D := centralizer (F : Set B) ⊓ centralizer ({t} : Set B)
  let : D.Normal := fixed_centralizer_normal F t htcentral
  have hDF : D ≤ F := inf_le_left.trans (fitting_selfCentralizing h)
  let : Group.IsNilpotent D :=
    Group.nilpotent_of_mulEquiv (subgroupOfEquivOfLe hDF)
  have hpcentral (p : ℕ) [Fact p.Prime] (hd : p ∣ Nat.card D) :
      (pCore p D).map D.subtype ≤ center B := by
    let P := (pCore p D).map D.subtype
    have hPD : P ≤ D := map_subtype_le _
    have hPC : P ≤ pCore p B := le_sSup ⟨inferInstance, pCore_isPGroup.map D.subtype⟩
    have hdiv : p ∣ Nat.card F := hd.trans (card_dvd_of_le hDF)
    let : IsCyclic (MulAut.conjNormal t : MulAut (pCore p B)).fixedSubgroup :=
      primary_fixed_cyclic hQ h t ht hnt hdiv
    let f : P →* (MulAut.conjNormal t : MulAut (pCore p B)).fixedSubgroup :=
      (inclusion hPC).codRestrict _ (by
        intro x
        apply (MulAut.mem_fixedSubgroup _ _).mpr
        apply Subtype.ext
        change t * (x : B) * t⁻¹ = x
        have hh := mem_centralizer_singleton_iff.mp (hPD x.property).2
        rw [← hh, mul_inv_cancel_right])
    let : IsCyclic P := isCyclic_of_injective f (fun x y hh =>
      (inclusion_injective hPC) (congrArg Subtype.val hh))
    have hc := commutator_le_centralizer_of_isCyclic_normal P
    rw [Group.IsPerfect.commutator_eq_top] at hc
    intro x hx
    apply mem_center_iff.mpr
    intro b
    exact (hc (mem_top b) x hx).symm
  have hall : (⊤ : Subgroup D) ≤ (center B).comap D.subtype := by
    rw [← fitting_eq_top_of_nilpotent D, fitting_eq_sup_pCore]
    apply iSup_le
    intro p
    let : Fact p.val.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.val.property⟩
    exact map_le_iff_le_comap.mp
      (hpcentral p.val.val (Nat.dvd_of_mem_primeFactors p.val.property))
  intro x hx
  exact hall (mem_top (⟨x, hx⟩ : D))

omit [Group.IsPerfect B] in
/-- The odd Fitting quotient has a central involution with an actual
involution representative in B. No complement to F(B) is assumed. -/
theorem exists_central_quotient_involution (h : A36Nilpotent B) (hc : A36Common B) :
    ∃ t : B, orderOf t = 2 ∧ t ∉ fittingSubgroup B ∧
      QuotientGroup.mk' (fittingSubgroup B) t ∈ center (B ⧸ fittingSubgroup B) := by
  have hodd : Odd (Nat.card (fittingSubgroup B)) := by
    rw [hc.1]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.2.2.1
  let eQ := (QuotientGroup.quotientMulEquivOfEq h.1.symm).trans e
  have hcard : Nat.card (B ⧸ fittingSubgroup B) = 120 := by
    rw [Nat.card_congr eQ.toEquiv, Atlas.card_sl_two, hF]
    rfl
  have hd : 2 ∣ Nat.card B :=
    (show 2 ∣ Nat.card (B ⧸ fittingSubgroup B) by rw [hcard]; decide).trans
      (card_quotient_dvd_card (fittingSubgroup B))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hd
  have hnt : t ∉ fittingSubgroup B := by
    intro hm
    exact hodd.not_two_dvd_nat (ht ▸ (fittingSubgroup B).orderOf_dvd_natCard hm)
  refine ⟨t, ht, hnt, ?_⟩
  have hFtwo : (2 : F) ≠ 0 := by
    let : Fintype F := Fintype.ofFinite F
    let r : ZMod 5 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    intro hh
    have hr : r (2 : ZMod 5) = r 0 := by simpa only [map_ofNat, map_zero] using hh
    exact (by decide : (2 : ZMod 5) ≠ 0) (r.injective hr)
  let x := eQ (QuotientGroup.mk' (fittingSubgroup B) t)
  have hx2 : x ^ 2 = 1 := by
    have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
    have hh := congrArg (fun b => eQ (QuotientGroup.mk' (fittingSubgroup B) b)) ht2
    simpa only [map_pow, map_one] using hh
  have hxdet : (Matrix.SpecialLinearGroup.toGL x).det = 1 := by
    apply Units.ext
    exact x.property
  have hxcentral : x ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rcases Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one
      hFtwo (Matrix.SpecialLinearGroup.toGL x)
      (by rw [← map_pow, hx2, map_one]) hxdet with hh | hh
    · have hx : x = 1 := Matrix.SpecialLinearGroup.toGL_injective (by simpa using hh)
      rw [hx]
      exact one_mem _
    · have hx : x = -1 := Subtype.ext (congrArg Units.val hh)
      rw [hx]
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      simp
  apply mem_center_iff.mpr
  intro g
  apply eQ.injective
  simp only [map_mul]
  exact mem_center_iff.mp hxcentral (eQ g)

/-- All automorphisms fixing F(B) pointwise are inner, from the original
nilpotent source data and the SQTK rank bound. -/
theorem fitting_restriction_kernel {𝒦 : GroupClass} (hQ : IsSQTK 𝒦 B)
    (h : A36Nilpotent B) (hc : A36Common B) :
    (MulAut.characteristic (fittingSubgroup B)).ker ≤ MulAut.innerSubgroup B := by
  obtain ⟨t, ht, hnt, htc⟩ := exists_central_quotient_involution h hc
  have hodd : Odd (Nat.card (fittingSubgroup B)) := by
    rw [hc.1]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact CharacteristicOuterRestriction.restriction_kernel_le_inner_of_involution
    (fittingSubgroup B) (fitting_selfCentralizing h) hodd t ht htc
    (fitting_centralizer_fixed_le_center hQ h t (ht ▸ pow_orderOf_eq_one t) hnt htc)

/-- The actual outer group embeds in the full normalizer quotient of its
Fitting action. The remaining source input is the primary normalizer calculation. -/
theorem outer_fitting_restriction_injective {𝒦 : GroupClass} (hQ : IsSQTK 𝒦 B)
    (h : A36Nilpotent B) (hc : A36Common B) :
    Function.Injective (CharacteristicOuterRestriction.outerRestriction (fittingSubgroup B)) :=
  CharacteristicOuterRestriction.outerRestriction_injective _ (fitting_restriction_kernel hQ h hc)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive

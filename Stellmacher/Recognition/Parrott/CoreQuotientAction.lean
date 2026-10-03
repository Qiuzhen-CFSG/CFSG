module

public import Stellmacher.Recognition.Parrott.CentralizerStructure
public import Theory.GroupTheory.SemidirectFaithfulInjection

/-!
# The action on Parrott's core abelianization

Put H = C_G(z), J = O₂(H), and D = J′. The literal quotient J/D is
an elementary abelian group of order sixteen. Conjugation by H descends
to a faithful action of H/J on this quotient, with an evaluation formula
on representatives. This is a different quotient from D/Z(J).

The supplied Sylow five-subgroup fixes only central elements of J, and
Z(J) is contained in D. Coprime fixed-point lifting therefore gives a
fixed-free action on J/D. The faithful C₅⋊C₄ model of H/J then implies
faithfulness of the entire quotient action.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed p.674, “The factor group H/E”, used in Lemma 4 on p.675.
-/

open Subgroup
open scoped commutatorElement

namespace Stellmacher.Recognition

/-- The actual core abelianization has the elementary structure and order
used in the five- and ten-coset orbit argument. -/
public theorem parrott_core_abelianization_structure
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    IsElementaryAbelian 2 (J ⧸ commutator J) ∧
      Nat.card (J ⧸ commutator J) = 16 := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 J) := ⟨pCore_isPGroup⟩
  obtain ⟨_, _, _, hPhi, _, _, hDcard, _⟩ := parrott_centralizer_structure z h
  change IsElementaryAbelian 2 (J ⧸ commutator J) ∧ Nat.card (J ⧸ commutator J) = 16
  change commutator J = frattini J at hPhi
  refine ⟨?_, ?_⟩
  · refine {
      toIsMulCommutative := (Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := commutator J)).mpr le_rfl
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (commutator J) x
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (N := commutator J) _).mpr
    rw [hPhi]
    exact pth_power_mem_frattini_of_isPGroup (p := 2) a
  · have hc := (commutator J).index_mul_card
    change Nat.card (J ⧸ commutator J) * Nat.card (commutator J) = Nat.card J at hc
    rw [hDcard, h.core_card] at hc
    omega

private theorem exists_five_mover
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let D := commutator J
    ∀ (P : Sylow 5 H), Nat.card P = 5 →
      (centralizer (P : Set H)).subgroupOf J ≤ center J →
      ∀ ρ : H →* MulAut (J ⧸ D),
        (∀ (a : H) (d d' : J), (d' : H) = a * (d : H) * a⁻¹ →
          ρ a (QuotientGroup.mk' D d) = QuotientGroup.mk' D d') →
        ∃ p : P, ρ (p : H) ≠ 1 := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  dsimp only
  intro P hPcard hPfixed ρ hρ
  let : MulDistribMulAction P J :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (P : Subgroup H) J
      (Subgroup.le_normalizer_of_normal (H := J))
  let hInv : IsInvariant P J D := isInvariant_of_characteristic D
  let : MulAction.QuotientAction P D := quotientAction_of_isInvariant D hInv
  let : MulDistribMulAction P (J ⧸ D) := quotientMulDistribMulAction D hInv
  have hfixed : FixedPoints.subgroup P J ≤ center J := by
    intro x hx
    apply hPfixed
    change (x : H) ∈ centralizer (P : Set H)
    intro a ha
    have hfix := congrArg (fun j : J => (j : H)) (hx ⟨a, ha⟩)
    change a * (x : H) * a⁻¹ = x at hfix
    exact mul_inv_eq_iff_eq_mul.mp hfix
  obtain ⟨_, _, _, _, hUpper, _, _, _⟩ := parrott_centralizer_structure z h
  change D = Subgroup.upperCentralSeries J 2 at hUpper
  have hZD : center J ≤ D := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      (Subgroup.upperCentralSeries_mono J (show 1 ≤ 2 by decide))
  have hcop : Nat.Coprime (Nat.card P) (Nat.card J) := by
    rw [hPcard, h.core_card]
    decide
  let : Group.IsNilpotent J := pCore_isPGroup.isNilpotent
  have hfree : FixedPoints.subgroup P (J ⧸ D) = ⊥ := by
    rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime
      (inferInstance : Group.IsSolvable J) hcop D hInv]
    exact (map_eq_bot_iff (FixedPoints.subgroup P J)).mpr (by
      simpa only [QuotientGroup.ker_mk'] using hfixed.trans hZD)
  have hVcard : Nat.card (J ⧸ D) = 16 :=
    (parrott_core_abelianization_structure z h).2
  let : Nontrivial (J ⧸ D) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  by_contra hnone
  have hrhoone : ∀ p : P, ρ (p : H) = 1 := by simpa only [not_exists, not_not] using hnone
  have htop : FixedPoints.subgroup P (J ⧸ D) = ⊤ := by
    apply top_unique
    intro x _ p
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective D x
    change p • QuotientGroup.mk' D d = QuotientGroup.mk' D d
    have hs : p • QuotientGroup.mk' D d = QuotientGroup.mk' D (p • d) :=
      MulAction.Quotient.smul_coe D p d
    rw [hs]
    have heq := congrArg (fun u : MulAut (J ⧸ D) => u (QuotientGroup.mk' D d)) (hrhoone p)
    change ρ (p : H) (QuotientGroup.mk' D d) = QuotientGroup.mk' D d at heq
    exact (hρ (p : H) d (p • d) rfl).symm.trans heq
  exact bot_ne_top (hfree.symm.trans htop)

/-- The literal quotient H/J acts faithfully on J/D, with conjugation evaluation. -/
public theorem parrott_core_quotient_action
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let D := commutator J
    ∃ f : (H ⧸ J) →* MulAut (J ⧸ D), Function.Injective f ∧
      ∀ (a : H) (d d' : J), (d' : H) = a * (d : H) * a⁻¹ →
        f (QuotientGroup.mk' J a) (QuotientGroup.mk' D d) = QuotientGroup.mk' D d' := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let ι : H →* normalizer (J : Set H) :=
    (MonoidHom.id H).codRestrict _ (by intro a; rw [normalizer_eq_top]; trivial)
  let jAct : H →* MulAut J := J.normalizerMonoidHom.comp ι
  let : MulDistribMulAction H J := MulDistribMulAction.compHom J jAct
  let hInv : IsInvariant H J D := isInvariant_of_characteristic D
  let : MulAction.QuotientAction H D := quotientAction_of_isInvariant D hInv
  let : MulDistribMulAction H (J ⧸ D) := quotientMulDistribMulAction D hInv
  let ρ : H →* MulAut (J ⧸ D) := MulDistribMulAction.toMulAut H (J ⧸ D)
  have hρ : ∀ (a : H) (d d' : J), (d' : H) = a * (d : H) * a⁻¹ →
      ρ a (QuotientGroup.mk' D d) = QuotientGroup.mk' D d' := by
    intro a d d' hd
    have heq : a • d = d' := Subtype.ext hd.symm
    change a • (QuotientGroup.mk' D d) = QuotientGroup.mk' D d'
    rw [← heq]
    exact MulAction.Quotient.smul_coe D a d
  have hkill : J ≤ ρ.ker := by
    intro a ha
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro x
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective D x
    change ρ a (QuotientGroup.mk' D d) = QuotientGroup.mk' D d
    rw [hρ a d (a • d) rfl]
    apply QuotientGroup.eq_iff_div_mem.mpr
    let aJ : J := ⟨a, ha⟩
    have hc : ⁅aJ, d⁆ ∈ D := commutator_mem_commutator (mem_top aJ) (mem_top d)
    change aJ * d * aJ⁻¹ / d ∈ D
    simpa only [commutatorElement_def, div_eq_mul_inv] using hc
  let f : (H ⧸ J) →* MulAut (J ⧸ D) := QuotientGroup.lift J ρ hkill
  obtain ⟨P, hPfixed⟩ := h.five_centralizer
  have hHcard : Nat.card H = 10240 := (h.card_and_solvable z).1
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hHcard]
    decide +kernel
  have hnontriv := exists_five_mover z h P hPcard hPfixed ρ hρ
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let C5 := Multiplicative (ZMod 5)
  let C4 := Multiplicative (ZMod 4)
  let modelMap : C5 ⋊[φ] C4 →* MulAut (J ⧸ D) := f.comp e.symm.toMonoidHom
  have hinl : Function.Injective (modelMap.comp SemidirectProduct.inl) := by
    let κ : C5 →* MulAut (J ⧸ D) := modelMap.comp SemidirectProduct.inl
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hC5 : Nat.card C5 = 5 := by change Nat.card (ZMod 5) = 5; simp
    let : IsSimpleGroup C5 := isSimpleGroup_of_prime_card hC5
    rcases (inferInstance : κ.ker.Normal).eq_bot_or_eq_top with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff κ).mp hk
    · obtain ⟨p, hp⟩ := hnontriv
      exfalso
      apply hp
      let y : C5 ⋊[φ] C4 := e (QuotientGroup.mk' J (p : H))
      have hp5 : (p : H) ^ 5 = 1 := by
        have hh : p ^ 5 = 1 := by
          have hh := pow_card_eq_one' (x := p)
          change p ^ Nat.card P = 1 at hh
          rw [hPcard] at hh
          exact hh
        exact congrArg Subtype.val hh
      have hy5 : y ^ 5 = 1 := by
        change (e (QuotientGroup.mk' J (p : H))) ^ 5 = 1
        rw [← map_pow, ← map_pow, hp5, map_one, map_one]
      have hry5 : y.right ^ 5 = 1 := by
        have hh := congrArg (SemidirectProduct.rightHom : C5 ⋊[φ] C4 →* C4) hy5
        simpa only [map_pow, map_one, SemidirectProduct.rightHom_eq_right] using hh
      have hry4 : y.right ^ 4 = 1 := by
        have hC4 : Nat.card C4 = 4 := by change Nat.card (ZMod 4) = 4; simp
        simpa only [hC4] using pow_card_eq_one' (x := y.right)
      have hry : y.right = 1 := orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 5 4)
          (orderOf_dvd_of_pow_eq_one hry5) (orderOf_dvd_of_pow_eq_one hry4))
      have hyinl : y = SemidirectProduct.inl y.left := by ext <;> simp [hry]
      have hκ : κ y.left = 1 := by
        have hm : y.left ∈ κ.ker := by rw [hk]; trivial
        exact hm
      have hρp : ρ (p : H) = modelMap y := by
        change ρ (p : H) = f (e.symm (e (QuotientGroup.mk' J (p : H))))
        rw [e.symm_apply_apply]
        rfl
      rw [hρp, hyinl]
      exact hκ
  have hmodelinj := SemidirectProduct.injective_of_left_injective hφ modelMap hinl
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    apply e.injective
    apply hmodelinj
    simpa only [modelMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply] using hxy
  · intro a d d' hd
    exact hρ a d d' hd

end Stellmacher.Recognition

module
public import Stellmacher.Recognition.Parrott.CentralizerStructure
public import Theory.GroupTheory.SemidirectFaithfulInjection
public import Theory.GroupAction.ParrottQuotientBounds

/-!
# The faithful quotient action on Parrott's derived central quotient

Under Parrott's original centralizer hypotheses, put H=C_G(z), J=O₂(H),
D=J', and Z=Z(J) intersected with D. The quotient H/J acts faithfully
on the literal group D/Z. The public theorem gives the automorphism
homomorphism together with its evaluation on any representatives related
by conjugation in H. Thus consumers can use the action without choosing
an equivalent action or invariance instance.

Conjugation by H on its normal two-core restricts to characteristic D
and descends through Z. The equality D=Z₂(J) gives [J,D] contained in
Z(J), so J is killed and the homomorphism descends to H/J.

The supplied Sylow five-action on J fixes only central elements. Coprime
fixed-point lifting therefore makes its action on D/Z fixed-point-free,
and the class bound makes D/Z nontrivial. This action supplies an element
that the descended homomorphism does not kill. A private helper checks
this with the native Sylow action and literal conjugation compatibility.

Transport along the supplied C5 semidirect C4 quotient model puts every
Sylow five-element in the model's C5 factor, since its right projection
has order dividing both five and four. The restriction to C5 is therefore
nontrivial and, by simplicity of C5, injective. The faithful abelian
semidirect-product injection theorem gives injectivity on the full model,
and hence on H/J.

Source: David Parrott, *A characterization of the Tits' simple group*
(1972), pp.674–675, the quotient action on E/<z> preceding Lemma 3.
All subgroup images, quotient maps, conjugation formulas and the supplied
quotient-model equivalence are the original constructions.
-/

open Subgroup
open scoped commutatorElement

namespace Stellmacher.Recognition

/-- Conjugation compatibility detects a nontrivial element of the actual Sylow five-action. -/
private theorem exists_five_mover
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let D := commutator J
    let Z := (center J).subgroupOf D
    ∀ (P : Sylow 5 H), Nat.card P = 5 →
      (centralizer (P : Set H)).subgroupOf J ≤ center J →
      ∀ ρ : H →* MulAut (D ⧸ Z),
        (∀ (a : H) (d d' : D), ((d' : J) : H) = a * ((d : J) : H) * a⁻¹ →
          ρ a (QuotientGroup.mk' Z d) = QuotientGroup.mk' Z d') →
        ∃ p : P, ρ (p : H) ≠ 1 := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let Z := (center J).subgroupOf D
  dsimp only
  intro P hPcard hPfixed ρ hρ
  let : MulDistribMulAction P J :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (P : Subgroup H) J
      (Subgroup.le_normalizer_of_normal (H := J))
  let : IsInvariant P J D := isInvariant_of_characteristic D
  let : IsInvariant P J (center J) := isInvariant_of_characteristic (center J)
  let hPInv : IsInvariant P D Z := isInvariant_subgroupOf (center J) D
  let : MulAction.QuotientAction P Z := quotientAction_of_isInvariant Z hPInv
  let : MulDistribMulAction P (D ⧸ Z) := quotientMulDistribMulAction Z hPInv
  have hfixed : FixedPoints.subgroup P J ≤ center J := by
    intro x hx
    apply hPfixed
    change (x : H) ∈ centralizer (P : Set H)
    intro a ha
    have heq := congrArg (fun j : J => (j : H)) (hx ⟨a, ha⟩)
    change a * (x : H) * a⁻¹ = x at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  have hbound := Theory.GroupAction.parrott_quotient_actions
    pCore_isPGroup h.core_class hPcard hfixed
  have hfree : FixedPoints.subgroup P (D ⧸ Z) = ⊥ := hbound.2.1
  let : Nontrivial (D ⧸ Z) := hbound.2.2
  by_contra hnone
  have hrhoone : ∀ p : P, ρ (p : H) = 1 := by simpa only [not_exists, not_not] using hnone
  have htop : FixedPoints.subgroup P (D ⧸ Z) = ⊤ := by
    apply top_unique
    intro x _ p
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective Z x
    change p • QuotientGroup.mk' Z d = QuotientGroup.mk' Z d
    have hs : p • QuotientGroup.mk' Z d = QuotientGroup.mk' Z (p • d) :=
      MulAction.Quotient.smul_coe Z p d
    rw [hs]
    have heq := congrArg (fun u : MulAut (D ⧸ Z) => u (QuotientGroup.mk' Z d)) (hrhoone p)
    change ρ (p : H) (QuotientGroup.mk' Z d) = QuotientGroup.mk' Z d at heq
    exact (hρ (p : H) d (p • d) rfl).symm.trans heq
  exact bot_ne_top (hfree.symm.trans htop)

/-- The actual quotient H/J acts faithfully on D/Z, with literal conjugation evaluation. -/
public theorem parrott_derived_quotient_action
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let D := commutator J
    let Z := (center J).subgroupOf D
    ∃ f : (H ⧸ J) →* MulAut (D ⧸ Z), Function.Injective f ∧
      ∀ (a : H) (d d' : D), ((d' : J) : H) = a * ((d : J) : H) * a⁻¹ →
        f (QuotientGroup.mk' J a) (QuotientGroup.mk' Z d) = QuotientGroup.mk' Z d' := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let Z := (center J).subgroupOf D
  let ι : H →* normalizer (J : Set H) :=
    (MonoidHom.id H).codRestrict _ (by intro a; rw [normalizer_eq_top]; trivial)
  let jAct : H →* MulAut J := J.normalizerMonoidHom.comp ι
  let : MulDistribMulAction H J := MulDistribMulAction.compHom J jAct
  let : IsInvariant H J D := isInvariant_of_characteristic D
  let : IsInvariant H J (center J) := isInvariant_of_characteristic (center J)
  let hInv : IsInvariant H D Z := isInvariant_subgroupOf (center J) D
  let : MulAction.QuotientAction H Z := quotientAction_of_isInvariant Z hInv
  let : MulDistribMulAction H (D ⧸ Z) := quotientMulDistribMulAction Z hInv
  let ρ : H →* MulAut (D ⧸ Z) := MulDistribMulAction.toMulAut H (D ⧸ Z)
  have hρ : ∀ (a : H) (d d' : D), ((d' : J) : H) = a * ((d : J) : H) * a⁻¹ →
      ρ a (QuotientGroup.mk' Z d) = QuotientGroup.mk' Z d' := by
    intro a d d' hd
    have heq : a • d = d' := by
      apply Subtype.ext
      apply Subtype.ext
      exact hd.symm
    change a • (QuotientGroup.mk' Z d) = QuotientGroup.mk' Z d'
    rw [← heq]
    exact MulAction.Quotient.smul_coe Z a d
  obtain ⟨_, _, _, _, hUpper, _, _, _⟩ := parrott_centralizer_structure z h
  change D = Subgroup.upperCentralSeries J 2 at hUpper
  have hcomm : ⁅(⊤ : Subgroup J), D⁆ ≤ center J := by
    rw [commutator_comm, hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using commutator_upperCentralSeries_top_le J 1
  have hkill : J ≤ ρ.ker := by
    intro a ha
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro x
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective Z x
    change ρ a (QuotientGroup.mk' Z d) = QuotientGroup.mk' Z d
    rw [hρ a d (a • d) rfl]
    apply QuotientGroup.eq_iff_div_mem.mpr
    let aJ : J := ⟨a, ha⟩
    have hc : ⁅aJ, (d : J)⁆ ∈ center J :=
      hcomm (commutator_mem_commutator (mem_top aJ) d.property)
    change aJ * (d : J) * aJ⁻¹ / (d : J) ∈ center J
    simpa only [commutatorElement_def, div_eq_mul_inv] using hc
  let f : (H ⧸ J) →* MulAut (D ⧸ Z) := QuotientGroup.lift J ρ hkill
  obtain ⟨P, hPfixed⟩ := h.five_centralizer
  have hHcard : Nat.card H = 10240 := (h.card_and_solvable z).1
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hHcard]
    decide +kernel
  have hnontriv := exists_five_mover z h P hPcard hPfixed ρ hρ
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let C5 := Multiplicative (ZMod 5)
  let C4 := Multiplicative (ZMod 4)
  let modelMap : C5 ⋊[φ] C4 →* MulAut (D ⧸ Z) := f.comp e.symm.toMonoidHom
  have hinl : Function.Injective (modelMap.comp SemidirectProduct.inl) := by
    let κ : C5 →* MulAut (D ⧸ Z) := modelMap.comp SemidirectProduct.inl
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

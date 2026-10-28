module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairCoordinates
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion.CocodeCommutant
-- Continue the existing cocode linearization internally, without exposing its body.
import all CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion.CocodeCommutant
public import Theory.Representation.ScalarMultiplicity
public import Theory.Representation.BinaryDoubledNaturalCentralizer
public import Theory.Representation.BinaryFourQuintic
public import Theory.Representation.BinaryIrreducibleCentralizer

/-!
# The joint cocode commutant excludes order five

The scalar commutant of one binary natural three-space constructs a
faithful action of the full four-copy commutant on a four-dimensional
multiplicity space. A nontrivial order-five operator there is irreducible,
so Schur's lemma excludes a commuting nontrivial involution. The even
image of the original I/P supplies that involution. This proves the
required joint centralizer bound without identifying its full scalar field.

The final section-action lemmas convert this bound to [P,X] <= U and
retain the literal quotient H/O2(H) and relative normality of I. The
same-witness application is NonFFSourceMathieuM24Five; no normality of I
in H is assumed. The private CocodeCommutant import continues the existing
linearization implementation without widening its public definition body.
Source: Aschbacher--Smith, 8.2.8(5), 8.2.9, printed pp.719--720,
refs/quasithin.pdf. Final Mathieu/J4 assembly: qt-d-1222-nonff-mathieu.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuMultiplicity
abbrev Natural := Fin 3 → ZMod 2
abbrev Copies := Fin 2 × Fin 2
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

/-- The full commutant acts faithfully on the actual four-dimensional
multiplicity space, without requiring invariant individual summands. -/
theorem commutant_multiplicity
    (α : D →* (W ≃ₗ[ZMod 2] W))
    (π : D →* (Natural ≃ₗ[ZMod 2] Natural)) (hπ : Function.Surjective π)
    (e : W ≃ₗ[ZMod 2] (Copies → Natural))
    (he : ∀ d w, e (α d w) = fun j => π d (e w j)) :
    ∃ μ : Representation (ZMod 2) (centralizer (α.range : Set (W ≃ₗ[ZMod 2] W)))
        (Copies → ZMod 2), Function.Injective μ := by
  let C := centralizer (α.range : Set (W ≃ₗ[ZMod 2] W))
  let σ : Representation (ZMod 2) (Natural ≃ₗ[ZMod 2] Natural) Natural :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  let ρ : Representation (ZMod 2) C (Copies → Natural) :=
    e.conjRingEquiv.toMonoidHom.comp
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp C.subtype)
  have hρ (c : C) (v : Copies → Natural) : ρ c v = e (c.val (e.symm v)) := rfl
  have hs (f : Natural →ₗ[ZMod 2] Natural)
      (hf : ∀ d v, f (σ d v) = σ d (f v)) :
      ∃ c : ZMod 2, ∀ v, f v = c • v := by
    apply Representation.BinaryDoubledNatural.natural_centralizer_scalar (by decide) f.toAddMonoidHom
    intro g v
    exact hf (Matrix.SpecialLinearGroup.toLin' g) v
  have hc (c : C) (d : Natural ≃ₗ[ZMod 2] Natural) (x : Copies → Natural) :
      ρ c (fun j => σ d (x j)) = fun j => σ d (ρ c x j) := by
    obtain ⟨a,rfl⟩ := hπ d
    obtain ⟨w,rfl⟩ := e.surjective x
    change ρ c (fun j => π a (e w j)) = fun j => π a (ρ c (e w) j)
    rw [←he,hρ,hρ,e.symm_apply_apply,e.symm_apply_apply,←he]
    exact congrArg e (LinearEquiv.congr_fun (c.property (α a) ⟨a,rfl⟩).symm w)
  obtain ⟨μ,hμ⟩ := Representation.ScalarMultiplicity.exists_multiplicity σ hs ρ hc
  refine ⟨μ,?_⟩
  intro a b hab
  have hr : ρ a = ρ b := by
    apply LinearMap.ext
    intro x
    have hx : x = ∑ j : Copies, Pi.single j (x j) := by
      apply funext
      intro j
      simp
    rw [hx,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hsing (v : Natural) :
        (fun k => (Pi.single j (1 : ZMod 2) : Copies → ZMod 2) k • v) = Pi.single j v := by
      ext k
      by_cases h : j = k
      · subst k; simp
      · simp [Ne.symm h]
    rw [←hsing (x j),hμ,hμ,hab]
  apply Subtype.ext
  ext w
  apply e.injective
  have hh := LinearMap.congr_fun hr (e w)
  simpa only [hρ,e.symm_apply_apply] using hh

/-- An involution in the residual commutant excludes every commuting
order-five operator. This is the joint, rather than residual-only, bound. -/
theorem four_copy_joint_no_five
    (α : D →* (W ≃ₗ[ZMod 2] W))
    (π : D →* (Natural ≃ₗ[ZMod 2] Natural)) (hπ : Function.Surjective π)
    (e : W ≃ₗ[ZMod 2] (Copies → Natural))
    (he : ∀ d w, e (α d w) = fun j => π d (e w j))
    (t : W ≃ₗ[ZMod 2] W) (ht : t ∈ centralizer (α.range : Set (W ≃ₗ[ZMod 2] W)))
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (z : W ≃ₗ[ZMod 2] W) (hz : z ∈ centralizer (α.range : Set (W ≃ₗ[ZMod 2] W)))
    (hzt : Commute z t) (hz5 : z ^ 5 = 1) : z = 1 := by
  obtain ⟨μ,hμ⟩ := commutant_multiplicity α π hπ e he
  let C := centralizer (α.range : Set (W ≃ₗ[ZMod 2] W))
  let t' : C := ⟨t,ht⟩
  let z' : C := ⟨z,hz⟩
  let : Finite W := Finite.of_equiv (Copies → Natural) e.toEquiv.symm
  let : Finite (W ≃ₗ[ZMod 2] W) := Finite.of_injective
    (fun a : W ≃ₗ[ZMod 2] W => (a : W → W)) DFunLike.coe_injective
  by_contra hz1
  have hzorder : orderOf z' = 5 := orderOf_eq_prime
    (show z' ^ 5 = 1 from Subtype.ext hz5) (fun h => hz1 (congrArg Subtype.val h))
  let A := zpowers z'
  have hA : 5 ∣ Nat.card A := by rw [Nat.card_zpowers,hzorder]
  let : Representation.IsIrreducible (μ.comp A.subtype) :=
    Representation.binary_four_irreducible_of_five_dvd (μ.comp A.subtype)
      (hμ.comp A.subtype_injective) (by simp [Copies]) hA
  have htc : t' ∈ centralizer (A : Set C) := by
    intro x hx
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hx
    exact (show Commute z' t' from Subtype.ext hzt.eq).zpow_left n |>.eq
  have htone := Representation.BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
    μ A hμ (show t' ^ 2 = 1 from Subtype.ext ht2) htc
  exact ht1 (congrArg Subtype.val htone)

open Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion
open scoped IsMulCommutative

/-- The two original section actions have no commuting operator of order
five once their first action has four natural copies and the second has
even image. The latter contributes the required nontrivial involution. -/
theorem section_joint_no_five_of_four_copies
    {Q J : Type*} [Group Q] [IsElementaryAbelian 2 Q] [Group J]
    (α : D →* MulAut Q) (β : J →* MulAut Q)
    (π : D →* (Natural ≃ₗ[ZMod 2] Natural)) (hπ : Function.Surjective π)
    (e : Additive Q ≃ₗ[ZMod 2] (Copies → Natural))
    (he : ∀ d v, e (Additive.ofMul (α d v)) = fun j => π d (e (Additive.ofMul v) j))
    (hβ : 2 ∣ Nat.card β.range) (hcomm : ∀ d j, Commute (α d) (β j))
    (z : MulAut Q) (hzα : ∀ d, Commute z (α d)) (hzβ : ∀ j, Commute z (β j))
    (hz5 : z ^ 5 = 1) : z = 1 := by
  let ell := cocodeMulAutLinear Q
  let a := ell.comp α
  let : Finite (Additive Q) := Finite.of_equiv (Copies → Natural) e.toEquiv.symm
  let : Finite Q := Finite.of_equiv (Additive Q) Additive.ofMul.symm
  let : Finite (MulAut Q) := Finite.of_injective
    (fun f : MulAut Q => (f : Q → Q)) DFunLike.coe_injective
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := β.range) 2 hβ
  obtain ⟨j,hj⟩ := t.property
  have htC : ell t.val ∈ centralizer (a.range : Set (Additive Q ≃ₗ[ZMod 2] Additive Q)) := by
    rintro _ ⟨d,rfl⟩
    rw [←hj]
    exact (hcomm d j).map ell |>.eq
  have ht2 : ell t.val ^ 2 = 1 := by
    rw [←map_pow]
    have hh : t.val ^ 2 = 1 := congrArg Subtype.val (ht ▸ pow_orderOf_eq_one t)
    rw [hh,map_one]
  have ht1 : ell t.val ≠ 1 := by
    intro hh
    have hh' : t.val = 1 := cocodeMulAutLinear_injective Q (hh.trans ell.map_one.symm)
    have hhone : t = 1 := Subtype.ext hh'
    rw [hhone,orderOf_one] at ht
    omega
  have hzC : ell z ∈ centralizer (a.range : Set (Additive Q ≃ₗ[ZMod 2] Additive Q)) := by
    rintro _ ⟨d,rfl⟩
    exact (hzα d).symm.map ell |>.eq
  have hzj : Commute (ell z) (ell t.val) := by rw [←hj]; exact (hzβ j).map ell
  have hl := four_copy_joint_no_five a π hπ e (fun d v => he d v.toMul)
    (ell t.val) htC ht2 ht1 (ell z) hzC hzj (by rw [←map_pow,hz5,map_one])
  exact cocodeMulAutLinear_injective Q (hl.trans ell.map_one.symm)

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuMultiplicity
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
open Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A fifth-order actor trivial on the faithful joint quotient centralizes
the section, by the proved joint commutant bound. All normality is relative. -/
theorem section_five_layer (Y X P U : Subgroup G) [(U.subgroupOf P).Normal]
    (hYP : Y ≤ normalizer (P : Set G)) (hYU : Y ≤ normalizer (U : Set G))
    (hXP : X ≤ normalizer (P : Set G)) (hXU : X ≤ normalizer (U : Set G))
    (hX : Nat.card X = 5)
    (hk : (sectionAction Y P U hYP hYU).ker = pCore 2 Y)
    (hc : ⁅Y,X⁆ ≤ Y.pCoreIn 2)
    (hfive : ∀ z : MulAut (P ⧸ U.subgroupOf P),
      (∀ y : Y, Commute z (sectionAction Y P U hYP hYU y)) → z ^ 5 = 1 → z = 1) :
    ⁅P,X⁆ ≤ U := by
  let N := normalizer (P : Set G) ⊓ normalizer (U : Set G)
  have hYN : Y ≤ N := le_inf hYP hYU
  have hXN : X ≤ N := le_inf hXP hXU
  let F := sectionAction N P U inf_le_left inf_le_right
  let f := sectionAction Y P U hYP hYU
  let a := sectionAction X P U hXP hXU
  have hFy (y : Y) : F (inclusion hYN y) = f y := rfl
  have hFx (x : X) : F (inclusion hXN x) = a x := rfl
  have hcomm (x : X) (y : Y) : Commute (a x) (f y) := by
    obtain ⟨c,hc,he⟩ := hc (commutator_mem_commutator y.property x.property)
    have hcy : inclusion hYN c = ⁅inclusion hYN y,inclusion hXN x⁆ := Subtype.ext he
    have hFc : F (inclusion hYN c) = 1 := hFy c ▸ (show c ∈ f.ker from hk.symm ▸ hc)
    rw [hcy,map_commutatorElement,hFy,hFx] at hFc
    exact (show Commute (f y) (a x) from commutatorElement_eq_one_iff_mul_comm.mp hFc).symm
  have ha (x : X) : a x = 1 := hfive (a x) (hcomm x) (by
    rw [←map_pow,show x ^ 5 = 1 from hX ▸ pow_card_eq_one' (x := x),map_one])
  rw [commutator_comm]
  apply commutator_le.mpr
  intro x hx p hp
  exact (mem_sectionAction_ker X P U hXP hXU ⟨x,hx⟩).mp (ha ⟨x,hx⟩) ⟨p,hp⟩

omit [Finite G] in
/-- The original quotient-centralization premise in H descends to the
intrinsic core of the normalized pair I, before any I-normality in H. -/
theorem relative_pair_commutator (H I X : Subgroup G) (hIH : I ≤ H) (hXH : X ≤ H)
    (hXI : X ≤ normalizer (I : Set G))
    (hq : (X.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≤
      centralizer ((I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H))) :
    ⁅I,X⁆ ≤ I.pCoreIn 2 := by
  have hXI' : X.subgroupOf H ≤ normalizer (I.subgroupOf H : Set H) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    exact mem_normalizer_iff.mp (hXI hx) y.val
  have hh := pair_commutator_le_core (I.subgroupOf H) (X.subgroupOf H) hXI' hq
  have hb := map_mono (f := H.subtype) hh
  rw [map_commutator,map_subgroupOf_eq_of_le hIH,map_subgroupOf_eq_of_le hXH,
    pCoreIn_subgroupOf 2 I H hIH,map_subgroupOf_eq_of_le ((pCoreIn_le 2 I).trans hIH)] at hb
  exact hb

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair

module
public import Theory.SpecificGroups.MinusExtraspecial.FourActionConjugacy
public import Theory.SpecificGroups.AlternatingFiveBorelProjection
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Complement

/-!
# Retaining the actual point section in an alternating complement

An order-twelve subgroup disjoint from the kernel of the actual A₅ quotient
is a section over a point stabilizer. Sylow conjugacy aligns its quotient
image with the standard four-point stabilizer. The two sections induce the
same marked A₄ action on the minus core, so inner action conjugacy places the
original section in a conjugate of the given complement.

All homomorphisms and the complete inner-action kernel are retained. This
is the point-marking correction in Baumeister Lemma 2.6, p.496.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace MinusExtraspecial.PointComplementRetention
open FixedFourCalculation.Outside
open BinaryPermutation.AlternatingFiveBorel
local notation "A5" => alternatingGroup (Fin 5)
local notation "A4" => alternatingGroup (Fin 4)

/-- Every actual order-twelve subgroup of A₅ is conjugate to the marked point stabilizer. -/
theorem twelve_conjugate_borel (D : Subgroup A5) (hD : Nat.card D = 12) :
    ∃ g : A5, D.map (MulAut.conj g).toMonoidHom = B := by
  let S : Sylow 2 D := Classical.choice inferInstance
  have hS : Nat.card S = 4 := by
    rw [S.card_eq_multiplicity,hD]
    decide +kernel
  let R := (S : Subgroup D).map D.subtype
  have hR : Nat.card R = 4 := by rw [card_map_of_injective D.subtype_injective,hS]
  let T : Sylow 2 A5 := Sylow.ofCard R (by
    rw [hR,nat_card_alternatingGroup]
    simp only [Nat.card_fin]
    decide +kernel)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A5 T AlternatingFiveProjection.sylow
  let e := MulAut.conj g
  have hP : R.map e.toMonoidHom = AlternatingFiveProjection.P := by
    have he := congrArg (fun S : Sylow 2 A5 => (S : Subgroup A5)) hg
    rw [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def] at he
    exact he
  have hproper : D.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    have hh := card_map_of_injective (K := D) (f := e.toMonoidHom) e.injective
    rw [ht,Nat.card_congr (topEquiv (G := A5)).toEquiv,nat_card_alternatingGroup,hD] at hh
    norm_num [Nat.factorial] at hh
  have hle : D.map e.toMonoidHom ≤ B := by
    rw [←AlternatingFiveProjection.normalizer_P]
    apply alternatingGroup.proper_sylow_overgroup_le_normalizer
      AlternatingFiveProjection.sylow _ hproper
    change AlternatingFiveProjection.P ≤ D.map e.toMonoidHom
    rw [←hP]
    exact map_mono (map_subtype_le _)
  refine ⟨g,eq_of_le_of_card_ge hle ?_⟩
  rw [card_map_of_injective e.injective,hD,
    Nat.card_congr marking.symm.toEquiv,alternatingGroup.card_of_card_eq_four (by simp)]

variable {W : Type*} [Group W] [Finite W]

private theorem conjugate_complement (p : W →* A5) (K : Subgroup W)
    (hK : p.ker.IsComplement' K) (a : W) :
    p.ker.IsComplement' (K.map (MulAut.conj a).toMonoidHom) := by
  apply isComplement'_of_card_mul_and_disjoint
  · rw [card_map_of_injective (MulAut.conj a).injective]
    exact hK.card_mul_card
  · have hh := disjoint_map (f := (MulAut.conj a).toMonoidHom)
      (MulAut.conj a).injective hK.disjoint
    have hn : p.ker.map (MulAut.conj a).toMonoidHom = p.ker :=
      Subgroup.Normal.map_conj_eq p.ker a
    rwa [hn] at hh

set_option maxHeartbeats 800000 in
private theorem retain_standard
    (p : W →* A5) (hp : Function.Surjective p)
    (ρ : W →* MulAut Model) (hρ : Function.Injective ρ)
    (hmark : ∀ w, fivePointAction (ρ w) = (p w).val)
    (hinner : ∀ n : Model, ∃ w ∈ p.ker, ρ w = MulAut.conj n)
    (K U : Subgroup W) (hK : p.ker.IsComplement' K)
    (hd : Disjoint p.ker U) (hU : U.map p = B) :
    ∃ L : Subgroup W, p.ker.IsComplement' L ∧ U ≤ L := by
  let u : U →* B := (p.comp U.subtype).codRestrict B (fun x =>
    hU ▸ mem_map_of_mem p x.property)
  have hui : Function.Injective u := by
    apply (injective_iff_map_eq_one u).mpr
    intro x hx
    apply Subtype.ext
    exact disjoint_def.mp hd (congrArg Subtype.val hx) x.property
  have hus : Function.Surjective u := by
    intro b
    have hb : (b : A5) ∈ U.map p := hU.symm ▸ b.property
    obtain ⟨x,hx,he⟩ := hb
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let eU := MulEquiv.ofBijective u ⟨hui,hus⟩
  let eA := QuotientGroup.quotientKerEquivOfSurjective p hp
  let eK : K ≃* A5 := hK.symm.QuotientMulEquiv.symm.trans eA
  have heK (k : K) : eK k = p k := by
    have hk : hK.symm.QuotientMulEquiv.symm k = QuotientGroup.mk' p.ker k := by
      apply hK.symm.QuotientMulEquiv.injective
      rw [MulEquiv.apply_symm_apply,quotientMulEquiv_mk_apply_of_isComplement']
    change eA (hK.symm.QuotientMulEquiv.symm k) = p k
    rw [hk]
    rfl
  let u₀ : A4 →* W := U.subtype.comp (eU.symm.toMonoidHom.comp marking.toMonoidHom)
  let k₀ : A4 →* W := K.subtype.comp
    (eK.symm.toMonoidHom.comp (B.subtype.comp marking.toMonoidHom))
  have hu₀ (g : A4) : p (u₀ g) = (marking g).val := by
    exact congrArg Subtype.val (eU.apply_symm_apply (marking g))
  have hk₀ (g : A4) : p (k₀ g) = (marking g).val := by
    exact (heK (eK.symm (marking g).val)).symm.trans (eK.apply_symm_apply _)
  obtain ⟨n,hn⟩ := FourActionConjugacy.exists_inner_conjugacy (ρ.comp u₀) (ρ.comp k₀)
    (fun g => (hmark _).trans (congrArg Subtype.val (hu₀ g)))
    (fun g => (hmark _).trans (congrArg Subtype.val (hk₀ g)))
  obtain ⟨w,_hw,hwρ⟩ := hinner n
  refine ⟨K.map (MulAut.conj w⁻¹).toMonoidHom,conjugate_complement p K hK w⁻¹,?_⟩
  intro x hx
  let g := marking.symm (eU (⟨x,hx⟩ : U))
  have hug : u₀ g = x := by
    change (eU.symm (marking (marking.symm (eU (⟨x,hx⟩ : U)))) : W) = x
    rw [marking.apply_symm_apply,eU.symm_apply_apply]
  have he : w * u₀ g = k₀ g * w := by
    apply hρ
    rw [map_mul,map_mul,hwρ]
    exact hn g
  refine ⟨k₀ g,(eK.symm (marking g).val).property,?_⟩
  change w⁻¹ * k₀ g * (w⁻¹)⁻¹ = x
  rw [inv_inv,mul_assoc,←he,inv_mul_cancel_left,hug]

set_option maxHeartbeats 800000 in
/-- A genuine order-twelve section lies in a conjugate complement when the
full inner action is present and the original action on the minus core is faithful. -/
theorem exists_complement_containing_twelve
    (p : W →* A5) (hp : Function.Surjective p)
    (ρ : W →* MulAut Model) (hρ : Function.Injective ρ)
    (hmark : ∀ w, fivePointAction (ρ w) = (p w).val)
    (hinner : ∀ n : Model, ∃ w ∈ p.ker, ρ w = MulAut.conj n)
    (K U : Subgroup W) (hK : p.ker.IsComplement' K)
    (hd : Disjoint p.ker U) (hU : Nat.card U = 12) :
    ∃ L : Subgroup W, p.ker.IsComplement' L ∧ U ≤ L := by
  have hi : Function.Injective (p.subgroupMap U) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    exact Subtype.ext (disjoint_def.mp hd (congrArg Subtype.val hx) x.property)
  have hD : Nat.card (U.map p) = 12 :=
    (Nat.card_congr (MulEquiv.ofBijective (p.subgroupMap U)
      ⟨hi,p.subgroupMap_surjective U⟩).toEquiv).symm.trans hU
  obtain ⟨g,hg⟩ := twelve_conjugate_borel (U.map p) hD
  obtain ⟨a,ha⟩ := hp g
  let c := MulAut.conj a
  let U' := U.map c.toMonoidHom
  have hU' : U'.map p = B := by
    change (U.map c.toMonoidHom).map p = _
    rw [map_map]
    have hm : p.comp c.toMonoidHom = (MulAut.conj g).toMonoidHom.comp p := by
      apply MonoidHom.ext
      intro x
      change p (a*x*a⁻¹) = g*p x*g⁻¹
      rw [map_mul,map_mul,map_inv,ha]
    rw [hm,←map_map,hg]
  have hd' : Disjoint p.ker U' := by
    have hh := disjoint_map (f := c.toMonoidHom) c.injective hd
    have hn : p.ker.map c.toMonoidHom = p.ker := Subgroup.Normal.map_conj_eq p.ker a
    rwa [hn] at hh
  obtain ⟨L,hL,hUL⟩ := retain_standard p hp ρ hρ hmark hinner K U' hK hd' hU'
  refine ⟨L.map (MulAut.conj a⁻¹).toMonoidHom,conjugate_complement p L hL a⁻¹,?_⟩
  intro x hx
  refine ⟨c x,hUL (mem_map_of_mem c.toMonoidHom hx),?_⟩
  change a⁻¹ * (a*x*a⁻¹) * (a⁻¹)⁻¹ = x
  group

end MinusExtraspecial.PointComplementRetention

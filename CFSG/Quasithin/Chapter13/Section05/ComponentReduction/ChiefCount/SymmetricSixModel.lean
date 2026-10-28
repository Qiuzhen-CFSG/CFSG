module

public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals
public import Theory.SpecificGroups.SymmetricTwoResidual
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.CubicActions
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations.MarkedModules

/-!
# The concrete syntheme residual actor for the S₆ chief count

The two-residual of the syntheme parabolic is the tetrahedral A₄. Every
order-three actor in this residual is conjugate to the marked pair cycle, and
the checked natural-module polynomial for that pair cycle forces the fixed
index of any injective cubic actor to be sixteen. The same argument transports
through any conjugate residual supplied by the source residual marking.

Source: Aschbacher–Smith 13.5.24 and 13.8.33. The natural action is the
literal alternating permutation action on the four-dimensional quotient of the
six-letter augmentation module; no outer-twisted marking is used here.
-/

@[expose] public section

open Subgroup BinaryPermutation Representation.BinaryFixedPoints
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixModel
/-- The literal embedded two-residual of the even syntheme parabolic. -/
abbrev residual := (pResidual 2 AlternatingAction.parabolic).map AlternatingAction.parabolic.subtype
/-- The source residual is the actual tetrahedral A₄. -/
noncomputable def residualEquiv : residual ≃* alternatingGroup (Fin 4) := by
  let e : AlternatingAction.parabolic ≃* Equiv.Perm (Fin 4) := edgeEquiv.symm
  exact ((pResidual 2 AlternatingAction.parabolic).equivMapOfInjective
    AlternatingAction.parabolic.subtype AlternatingAction.parabolic.subtype_injective).symm.trans
    (((e.subgroupMap (pResidual 2 AlternatingAction.parabolic)).trans
      (MulEquiv.subgroupCongr (map_pResidual 2 e))).trans
      (MulEquiv.subgroupCongr (Equiv.Perm.twoResidual_eq_alternating (Fin 4))))
/-- The A₄ equivalence for the conjugate supplied by the source marking. -/
noncomputable def conjugateResidualEquiv (g : alternatingGroup (Fin 6)) :
    residual.map (MulAut.conj g).toMonoidHom ≃* alternatingGroup (Fin 4) :=
  ((MulAut.conj g).subgroupMap residual).symm.trans residualEquiv

/-- The syntheme residual has order twelve. -/
theorem residual_card : Nat.card residual = 12 := by
  rw [Nat.card_congr residualEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide

private theorem conjugate_cubic_mem {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 12) (x : H) (hx : orderOf x = 3)
    (B : Subgroup H) (hB : Nat.card B = 3) :
    ∃ g : H, g * x * g⁻¹ ∈ B := by
  have hi (C : Subgroup H) (hC : Nat.card C = 3) : ¬ 3 ∣ C.index := by
    have hm := C.card_mul_index
    rw [hH,hC] at hm
    have : C.index = 4 := by omega
    rw [this]; decide
  have hxcard : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers,hx]
  let P : Sylow 3 H := (IsPGroup.of_card (p := 3) (n := 1) hxcard).toSylow
    (hi (zpowers x) hxcard)
  let Q : Sylow 3 H := (IsPGroup.of_card (p := 3) (n := 1) hB).toSylow (hi B hB)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P Q
  refine ⟨g, ?_⟩
  have hm : g * x * g⁻¹ ∈ (g • P : Sylow 3 H) := by
    change g * x * g⁻¹ ∈ (P : Subgroup H).map (MulAut.conj g).toMonoidHom
    apply mem_map_of_mem
    change x ∈ zpowers x
    exact mem_zpowers x
  rw [hg] at hm
  exact hm

private theorem cubic_order : orderOf AlternatingAction.actor = 3 := by
  apply orderOf_eq_prime
  · exact Subtype.ext AlternatingAction.cubic_cube
  · decide

/-- Every cubic subgroup of the residual acts without nonzero fixed vectors. -/
theorem natural_fixed_eq_zero {A : Type*} [Group A] [Finite A]
    (f : A →* alternatingGroup (Fin 6)) (hf : Function.Injective f)
    (hA : Nat.card A = 3) (hJ : f.range ≤ residual)
    (v : natural (Fin 6))
    (hv : ∀ a, alternatingNaturalRepresentation (Fin 6) (f a) v = v) : v = 0 := by
  let fJ : A →* residual := f.codRestrict residual (fun a => hJ ⟨a,rfl⟩)
  have hi : Function.Injective fJ := fun a b h => hf (congrArg Subtype.val h)
  have hb : Nat.card fJ.range = 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans hA
  let x : residual := ⟨AlternatingAction.actor,AlternatingAction.actor_mem_residual⟩
  have hx : orderOf x = 3 := (residual.orderOf_coe x).symm.trans cubic_order
  obtain ⟨g,hg⟩ := conjugate_cubic_mem residual_card x hx fJ.range hb
  obtain ⟨a,ha⟩ := hg
  have he : f a = g.val * AlternatingAction.actor * g.val⁻¹ := congrArg Subtype.val ha
  let ρ := alternatingNaturalRepresentation (Fin 6)
  have hv' : ρ (g.val * AlternatingAction.actor * g.val⁻¹) v = v := by
    rw [←he]; exact hv a
  have hc := congrArg (ρ g.val⁻¹) hv'
  simp only [map_mul, Module.End.mul_apply] at hc
  rw [ρ.inv_self_apply] at hc
  have hz := AlternatingAction.cubic_fixed_eq_zero (ρ g.val⁻¹ v) hc
  have hz' := congrArg (ρ g.val) hz
  simpa only [ρ.self_inv_apply,map_zero] using hz'

/-- The fixed index on the literal natural module is sixteen. -/
theorem natural_fixedIndex {A : Type*} [Group A] [Finite A]
    (f : A →* alternatingGroup (Fin 6)) (hf : Function.Injective f)
    (hA : Nat.card A = 3) (hJ : f.range ≤ residual) :
    fixedIndex ((alternatingNaturalRepresentation (Fin 6)).comp f) = 16 := by
  have hz : Representation.invariants ((alternatingNaturalRepresentation (Fin 6)).comp f) = ⊥ := by
    ext v
    constructor
    · intro hv
      exact natural_fixed_eq_zero f hf hA hJ v hv
    · intro hv
      have : v = 0 := hv
      subst v
      exact Submodule.zero_mem _
  have hc := fixedIndex_mul_card ((alternatingNaturalRepresentation (Fin 6)).comp f)
  rw [hz] at hc
  simp only [Nat.card_unique, mul_one] at hc
  have hnat : Nat.card (natural (Fin 6)) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
      CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.natural_finrank]
    norm_num
  simpa only [mul_one,hnat] using hc

/-- The cubic length contributed by the literal natural module is two. -/
theorem natural_cubicLength {A : Type*} [Group A] [Finite A]
    (f : A →* alternatingGroup (Fin 6)) (hf : Function.Injective f)
    (hA : Nat.card A = 3) (hJ : f.range ≤ residual) :
    letI := action ((alternatingNaturalRepresentation (Fin 6)).comp f)
    FixedPoints.cubicLength A (Multiplicative (natural (Fin 6))) = 2 := by
  change Nat.log 4 (fixedIndex ((alternatingNaturalRepresentation (Fin 6)).comp f)) = 2
  rw [natural_fixedIndex f hf hA hJ]
  decide

/-- Fixed-point freeness respects the actual conjugate residual marking. -/
theorem conjugate_fixed_eq_zero {A : Type*} [Group A] [Finite A]
    (f : A →* alternatingGroup (Fin 6)) (hf : Function.Injective f)
    (hA : Nat.card A = 3) (g : alternatingGroup (Fin 6))
    (hJ : f.range ≤ residual.map (MulAut.conj g).toMonoidHom)
    (v : natural (Fin 6)) (hv : ∀ a, alternatingNaturalRepresentation (Fin 6) (f a) v = v) :
    v = 0 := by
  let f₀ : A →* alternatingGroup (Fin 6) := (MulAut.conj g⁻¹).toMonoidHom.comp f
  have hf₀ : Function.Injective f₀ := (MulAut.conj g⁻¹).injective.comp hf
  have hr : f₀.range ≤ residual := by
    rintro _ ⟨a,rfl⟩
    obtain ⟨x,hx,he⟩ := hJ ⟨a,rfl⟩
    have he' : f₀ a = x := by
      change (MulAut.conj g⁻¹) (f a) = x
      rw [←he]
      change g⁻¹ * (g * x * g⁻¹) * g = x
      group
    rw [he']
    exact hx
  let ρ := alternatingNaturalRepresentation (Fin 6)
  have hz : ρ g⁻¹ v = 0 := by
    apply natural_fixed_eq_zero f₀ hf₀ hA hr
    intro a
    change ρ (g⁻¹ * f a * g) (ρ g⁻¹ v) = ρ g⁻¹ v
    simp only [map_mul, Module.End.mul_apply, ρ.self_inv_apply]
    rw [show ρ (f a) v = v from hv a]
  have hz' := congrArg (ρ g) hz
  simpa only [ρ.self_inv_apply,map_zero] using hz'

/-- The fixed-index input for the original source marked cubic actor. -/
theorem conjugate_fixedIndex {A : Type*} [Group A] [Finite A]
    (f : A →* alternatingGroup (Fin 6)) (hf : Function.Injective f)
    (hA : Nat.card A = 3) (g : alternatingGroup (Fin 6))
    (hJ : f.range ≤ residual.map (MulAut.conj g).toMonoidHom) :
    fixedIndex ((alternatingNaturalRepresentation (Fin 6)).comp f) = 16 := by
  have hz : Representation.invariants ((alternatingNaturalRepresentation (Fin 6)).comp f) = ⊥ := by
    ext v
    constructor
    · exact conjugate_fixed_eq_zero f hf hA g hJ v
    · intro hv
      have : v = 0 := hv
      subst v
      exact Submodule.zero_mem _
  have hc := fixedIndex_mul_card ((alternatingNaturalRepresentation (Fin 6)).comp f)
  rw [hz] at hc
  simp only [Nat.card_unique,mul_one] at hc
  have hnat : Nat.card (natural (Fin 6)) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
      CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.natural_finrank]
    norm_num
  exact hc.trans hnat

/-- The natural-module contribution to the literal source chief count. -/
theorem conjugate_cubicLength {A : Type*} [Group A] [Finite A]
    (f : A →* alternatingGroup (Fin 6)) (hf : Function.Injective f)
    (hA : Nat.card A = 3) (g : alternatingGroup (Fin 6))
    (hJ : f.range ≤ residual.map (MulAut.conj g).toMonoidHom) :
    letI := action ((alternatingNaturalRepresentation (Fin 6)).comp f)
    FixedPoints.cubicLength A (Multiplicative (natural (Fin 6))) = 2 := by
  change Nat.log 4 (fixedIndex ((alternatingNaturalRepresentation (Fin 6)).comp f)) = 2
  rw [conjugate_fixedIndex f hf hA g hJ]
  decide
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixModel

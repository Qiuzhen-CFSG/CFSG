module
public import Theory.Representation.PSL3Two.DoubledCubic
public import Theory.Representation.PSL3Two.FanoNonFF
public import Theory.Representation.FrattiniAction
public import Theory.Representation.ElementaryPerfectSplit

/-!
# Cubic movement in the three binary linear six-space models

A faithful cubic has fixed codimension two on the natural three-space
and its dual. The point and line Fano cores have these as their actual
submodule and quotient; the fixed-codimension inequality supplies at least
four on each core. The natural–dual sum has exactly four.

Transport through an actual representation equivalence and cubic image
therefore gives conjugation cubic length at least two on all three models.
This supplies the omega-module contribution in the block exclusion of
Aschbacher–Smith 13.4.7(4), printed p.903. Neither a splitting of a Fano
core nor a new finite certificate is used.
-/

public noncomputable section
open scoped IsMulCommutative
open Representation Representation.BinaryOffender Subgroup
namespace BinaryLinearThree.SixCubic
open FanoDecomposition FanoCoreStructure
local instance : Finite (Module.Dual (ZMod 2) Vector) :=
  Finite.of_injective (fun f : Module.Dual (ZMod 2) Vector => (f : Vector → ZMod 2))
    DFunLike.coe_injective

private theorem natural_codim (A : Subgroup Group) (hA : Nat.card A = 3) :
    fixedCodim W A = 2 := by
  have hh := natural_cubic_fixedIndex hA A.subtype A.subtype_injective
  rw [FrattiniAction.fixedIndex_eq_two_pow_fixedCodim] at hh
  exact (Nat.pow_right_injective (by decide : 1 < 2)) hh

private theorem dual_codim (A : Subgroup Group) (hA : Nat.card A = 3) :
    fixedCodim W.dual A = 2 := by
  let : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨a,ha⟩ := IsCyclic.exists_generator (α := A)
  have hh := BinaryFixedPoints.fixedIndex_dual (W.comp A.subtype) a ha
  change BinaryFixedPoints.fixedIndex (W.dual.comp A.subtype) = _ at hh
  rw [FrattiniAction.fixedIndex_eq_two_pow_fixedCodim,
    natural_cubic_fixedIndex hA A.subtype A.subtype_injective] at hh
  exact (Nat.pow_right_injective (by decide : 1 < 2)) hh

private theorem codim_equiv {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N]
    {ρ : Representation (ZMod 2) Group M} {σ : Representation (ZMod 2) Group N}
    (e : ρ.Equiv σ) (A : Subgroup Group) : fixedCodim ρ A = fixedCodim σ A := by
  simpa only [Subgroup.map_id] using fixedCodim_map_equivariant ρ σ (MonoidHom.id Group)
    e.toLinearEquiv (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A

/-- Each actual Fano core has at least two cubic movement contributions. -/
theorem fano_codim (A : Subgroup Group) (hA : Nat.card A = 3) :
    4 ≤ fixedCodim U₂ A ∧ 4 ≤ fixedCodim lineCoreRepresentation A := by
  have hp := fixedCodim_quotient_add_subrepresentation_le U₂ pointKernel A
  have hl := fixedCodim_quotient_add_subrepresentation_le lineCoreRepresentation lineKernel A
  rw [codim_equiv pointQuotientEquiv,←codim_equiv pointKernelEquiv,
    natural_codim A hA,dual_codim A hA] at hp
  rw [codim_equiv lineQuotientEquiv,←codim_equiv lineKernelEquiv,
    natural_codim A hA,dual_codim A hA] at hl
  exact ⟨hp,hl⟩

/-- Oppositely marked natural summands have the same two contributions. -/
theorem sum_codim (A : Subgroup Group) (hA : Nat.card A = 3) :
    fixedCodim (W.prod W.dual) A = 4 := by
  have hp := BinaryFixedPoints.fixedIndex_prod (W.comp A.subtype) (W.dual.comp A.subtype)
  change BinaryFixedPoints.fixedIndex ((W.prod W.dual).comp A.subtype) = _ at hp
  rw [FrattiniAction.fixedIndex_eq_two_pow_fixedCodim,
    FrattiniAction.fixedIndex_eq_two_pow_fixedCodim,
    FrattiniAction.fixedIndex_eq_two_pow_fixedCodim,natural_codim A hA,dual_codim A hA] at hp
  exact (Nat.pow_right_injective (by decide : 1 < 2)) hp

/-- The lower bound transports to the literal conjugation action, using the
actual cubic image and any of the three six-dimensional source models. -/
theorem conjugation_length_ge_two
    {G : Type*} [_root_.Group G] [Finite G]
    (E U : Subgroup G) [IsElementaryAbelian 2 U]
    (hEU : E ≤ normalizer (U : Set G)) (q : E →* Group)
    (hq : Nat.card q.range = 3)
    (hmodel :
      Nonempty (Representation.Equiv ((W.prod W.dual).comp q)
        (Representation.elementaryRepresentation (U.normalizerMonoidHom.comp (inclusion hEU)))) ∨
      Nonempty (Representation.Equiv (U₂.comp q)
        (Representation.elementaryRepresentation (U.normalizerMonoidHom.comp (inclusion hEU)))) ∨
      Nonempty (Representation.Equiv (lineCoreRepresentation.comp q)
        (Representation.elementaryRepresentation (U.normalizerMonoidHom.comp (inclusion hEU))))) :
    2 ≤ conjugationCubicLength E U := by
  let := conjMulDistribMulActionOfLeNormalizer E U hEU
  have step {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
      (σ : Representation (ZMod 2) Group M)
      (e : Representation.Equiv (σ.comp q)
        (Representation.elementaryRepresentation (U.normalizerMonoidHom.comp (inclusion hEU))))
      (hcodim : 4 ≤ fixedCodim σ q.range) : 2 ≤ conjugationCubicLength E U := by
    let em : U ≃* Multiplicative M := e.toLinearEquiv.symm.toAddEquiv.toMultiplicative
    have hh := BinaryFixedPoints.cubicLength_eq_of_equivariant
      (σ.comp q.range.subtype) q.rangeRestrict q.rangeRestrict_surjective em (by
        intro a v
        apply Multiplicative.toAdd.injective
        have he := LinearMap.congr_fun (e.isIntertwining' a) (e.toLinearEquiv.symm (Additive.ofMul v))
        change e.toLinearEquiv.symm (Additive.ofMul (a • v)) =
          σ (q a) (e.toLinearEquiv.symm (Additive.ofMul v))
        apply e.toLinearEquiv.injective
        rw [e.toLinearEquiv.apply_symm_apply]
        change e.toLinearEquiv (σ (q a) (e.toLinearEquiv.symm (Additive.ofMul v))) =
          Additive.ofMul (a • (e.toLinearEquiv (e.toLinearEquiv.symm (Additive.ofMul v))).toMul) at he
        rw [e.toLinearEquiv.apply_symm_apply] at he
        exact he.symm)
    rw [FrattiniAction.fixedIndex_eq_two_pow_fixedCodim] at hh
    rw [conjugationCubicLength_eq E U hEU,hh]
    have hb : 16 ≤ 2 ^ fixedCodim σ q.range :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) hcodim
    exact (show 2 = Nat.log 4 16 from rfl).trans_le (Nat.log_mono_right hb)
  rcases hmodel with hm | hm | hm
  · obtain ⟨e⟩ := hm
    exact step _ e (by rw [sum_codim q.range hq])
  · obtain ⟨e⟩ := hm
    exact step _ e (fano_codim q.range hq).1
  · obtain ⟨e⟩ := hm
    exact step _ e (fano_codim q.range hq).2
end BinaryLinearThree.SixCubic

module
public import Theory.Representation.PSL3Two.DoubledCubic
public import Theory.Representation.PSL3Two.FanoNonFF
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex

/-!
# Cubic movement in the six-dimensional binary linear modules

A faithful cubic has fixed codimension two on each natural three-space
and its dual. The literal submodule and quotient of each Fano core
therefore give codimension at least four, as does the direct sum.
Transport through conjugation coordinates gives cubic length at least two.

This supplies the chief-factor premise for the weight-two parabolic in
Aschbacher–Smith 13.4.12, printed pp.910–911, using the six-dimensional
module already recognized in 13.4.7. No enumeration is needed.
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup
namespace BinaryLinearThree.CubicSixSpace
open FanoDecomposition FanoCoreStructure

private theorem codim_equiv {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) Group M) (σ : Representation (ZMod 2) Group N)
    (e : ρ.Equiv σ) (A : Subgroup Group) : fixedCodim ρ A = fixedCodim σ A := by
  simpa only [Subgroup.map_id] using fixedCodim_map_equivariant ρ σ
    (MonoidHom.id Group) e.toLinearEquiv
    (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A

private theorem codim_of_index {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Finite M] (ρ : Representation (ZMod 2) Group M) (A : Subgroup Group)
    (hi : BinaryFixedPoints.fixedIndex (ρ.comp A.subtype) = 4) : fixedCodim ρ A = 2 := by
  have hc := BinaryFixedPoints.fixedIndex_mul_card (ρ.comp A.subtype)
  have hd := fixedCodim_add_finrank ρ A
  have hv := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M)
  have hf := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A)
  rw [hi] at hc
  change 4 * Nat.card (fixedSpace ρ A) = Nat.card M at hc
  rw [hv,hf,show Nat.card (ZMod 2) = 2 by simp] at hc
  have he : 2 ^ (2 + Module.finrank (ZMod 2) (fixedSpace ρ A)) =
      2 ^ Module.finrank (ZMod 2) M := by simpa only [pow_add,show (2 : ℕ)^2 = 4 from rfl] using hc
  have hh := (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))) he
  omega

theorem natural_dual_codim (A : Subgroup Group) (hA : Nat.card A = 3) :
    fixedCodim W A = 2 ∧ fixedCodim W.dual A = 2 := by
  let : Finite (Module.Dual (ZMod 2) Vector) :=
    Finite.of_injective (fun f => (f : Vector → ZMod 2)) DFunLike.coe_injective
  have hn := natural_cubic_fixedIndex hA A.subtype A.subtype_injective
  have ha : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨a,ha⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := A)).mp ha
  have hdual := BinaryFixedPoints.fixedIndex_dual (W.comp A.subtype) a
    (fun x => ha ▸ mem_top x)
  exact ⟨codim_of_index W A hn,codim_of_index W.dual A (hdual.trans hn)⟩

theorem sum_codim (A : Subgroup Group) (hA : Nat.card A = 3) :
    4 ≤ fixedCodim (W.prod W.dual) A := by
  rw [fixedCodim_prod,(natural_dual_codim A hA).1,(natural_dual_codim A hA).2]

theorem point_codim (A : Subgroup Group) (hA : Nat.card A = 3) :
    4 ≤ fixedCodim U₂ A := by
  have hb := fixedCodim_quotient_add_subrepresentation_le U₂ pointKernel A
  have hk := codim_equiv W.dual pointKernel.toRepresentation pointKernelEquiv A
  have hq := codim_equiv pointKernel.quotientRepresentation W pointQuotientEquiv A
  obtain ⟨hn,hd⟩ := natural_dual_codim A hA
  omega

theorem line_codim (A : Subgroup Group) (hA : Nat.card A = 3) :
    4 ≤ fixedCodim lineCoreRepresentation A := by
  have hb := fixedCodim_quotient_add_subrepresentation_le lineCoreRepresentation lineKernel A
  have hk := codim_equiv W lineKernel.toRepresentation lineKernelEquiv A
  have hq := codim_equiv lineKernel.quotientRepresentation W.dual lineQuotientEquiv A
  obtain ⟨hn,hd⟩ := natural_dual_codim A hA
  omega
/-- Transfer a cubic codimension bound through the actual conjugation coordinates. -/
theorem length_ge_two {G M : Type*} [_root_.Group G] [Finite G]
    [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) Group M)
    (hc : ∀ J : Subgroup Group, Nat.card J = 3 → 4 ≤ fixedCodim σ J)
    (A U : Subgroup G) (hA : Nat.card A = 3)
    (hAU : A ≤ normalizer (U : Set G))
    (q : A →* Group) (hq : Function.Injective q)
    (e : U ≃* Multiplicative M)
    (he : ∀ (a : A) (v : U),
      (e (U.normalizerMonoidHom ⟨a.val,hAU a.property⟩ v)).toAdd =
        σ (q a) (e v).toAdd) : 2 ≤ conjugationCubicLength A U := by
  let : Finite M := Finite.of_equiv U e.toEquiv
  let j := U.subtype.comp e.symm.toMonoidHom
  have hj : j.range = U := by
    ext u
    constructor
    · rintro ⟨v,rfl⟩
      exact (e.symm v).property
    · intro hu
      exact ⟨e ⟨u,hu⟩,congrArg Subtype.val (e.symm_apply_apply _)⟩
  have hact (a : A) (v : M) : j (Multiplicative.ofAdd (σ (q a) v)) =
      a.val * j (Multiplicative.ofAdd v) * a.val⁻¹ := by
    have hh := congrArg (fun w : M => (e.symm (Multiplicative.ofAdd w)).val)
      (he a (e.symm (Multiplicative.ofAdd v)))
    change (e.symm (e (U.normalizerMonoidHom ⟨a.val,hAU a.property⟩
      (e.symm (Multiplicative.ofAdd v))))).val =
      (e.symm (Multiplicative.ofAdd (σ (q a) (e (e.symm (Multiplicative.ofAdd v))).toAdd))).val at hh
    rw [e.symm_apply_apply,e.apply_symm_apply] at hh
    exact hh.symm
  have hi := embedded_centralizer_index σ U A j
    (U.subtype_injective.comp e.symm.injective) hj q hact
  have hr : Nat.card q.range = 3 := (Nat.card_congr (MonoidHom.ofInjective hq).toEquiv).symm.trans hA
  have hb := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) (hc q.range hr)
  have hh := Nat.log_mono_right (b := 4) hb
  rw [←hi] at hh
  exact hh
end BinaryLinearThree.CubicSixSpace

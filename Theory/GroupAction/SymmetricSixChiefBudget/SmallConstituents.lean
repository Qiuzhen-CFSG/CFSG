module
public import Theory.GroupAction.SymmetricSixChiefBudget
public import Theory.GroupTheory.NoncentralChiefRefinement.BinarySections
public import Theory.Representation.BinaryAlternatingSixModels.InvolutionRanks

/-!
# Small chief constituents above S₆

Linearize each literal chief quotient separately. Its irreducible binary
action kills the normal two-kernel, so it descends along the prescribed
map onto S₆. Fixed-index monotonicity bounds the displacement on that
quotient by two. The actual model catalogue excludes the tensor model
and identifies a natural four-space, of order sixteen.

Source application: Aschbacher--Smith, Lemma 13.8.33, printed p.967,
the constituent of V_H/U_H. No abelianness of the numerator, splitting
of the chief series, or choice of natural marking is required.
-/

public section
open Representation Subgroup
open scoped IsMulCommutative
open Theory.SpecificGroups.SymmetricSix BinaryDuadModule
namespace NoncentralChiefRefinement.SymmetricSixBudget
open Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
variable {H W : Type*} [Group H] [Finite H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- A small even-involution displacement on an irreducible action above S₆
forces dimension four after descending through the actual two-kernel. -/
theorem simple_finrank_four_of_small_index
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ] (hne : ρ ≠ 1)
    (A : Subgroup H) (y : H) (hy : y ∈ A)
    (ha : orderOf (q y) = 2) (heven : q y ∈ alternatingGroup (Fin 6))
    (hsmall : fixedCodim ρ A ≤ 2) : Module.finrank (ZMod 2) W = 4 := by
  have hk : q.ker ≤ ρ.ker := normal_p_subgroup_le_ker ρ q.ker hp
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  let σ := (quotientOfLEKer ρ q.ker hk).comp e.symm.toMonoidHom
  have he (h : H) : σ (q h) = ρ h := by
    change quotientOfLEKer ρ q.ker hk (e.symm (q h)) = _
    have hh : e.symm (q h) = QuotientGroup.mk' q.ker h := e.symm_apply_eq.mpr rfl
    rw [hh]
    rfl
  have hcomp : σ.comp q = ρ := MonoidHom.ext he
  let : IsIrreducible σ := (irreducible_comp_surjective_iff q hq σ).mp
    (hcomp ▸ (inferInstance : IsIrreducible ρ))
  have hnσ : σ ≠ 1 := by
    intro hs
    apply hne
    rw [← hcomp, hs]
    rfl
  have hb : operatorFixedCodim (σ (q y)) ≤ 2 := by
    rw [he]
    exact (operatorFixedCodim_le_fixedCodim ρ A hy).trans hsmall
  rcases BinaryAlternatingSix.natural_of_small_even_displacement σ hnσ
    (q y) ha heven hb with hm | hm
  all_goals
    obtain ⟨en⟩ := hm
    exact en.toLinearEquiv.finrank_eq.trans naturalModule_finrank

/-- Every noncentral chief factor in a normal subgroup with fixed index at
most four has order sixteen. The original numerator need not be abelian. -/
theorem noncentral_factor_card_sixteen
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (U : Subgroup H) [U.Normal] (hU : U ≤ q.ker)
    (A : Subgroup H) (y : H) (hy : y ∈ A)
    (ha : orderOf (q y) = 2) (heven : q y ∈ alternatingGroup (Fin 6))
    (hindex : (centralizer (A : Set H)).relIndex U ≤ 4)
    (s : SeriesOn U) (i : Fin s.series.length) (hi : ¬ s.Central i) :
    Nat.card (s.Factor i) = 16 := by
  have hU2 := hp.to_le hU
  let := s.factor_elementary hU2 i
  let ρ : Representation (ZMod 2) H (Additive (s.Factor i)) :=
    binarySectionRepresentation (s.lower i) (s.upper i)
  let : IsIrreducible ρ := by
    exact binarySection_irreducible (s.lower i) (s.upper i) (s.series.step i)
  have hnρ : ρ ≠ 1 := fun he => hi ((binarySection_trivial_iff _ _).mp he)
  have hidx : sectionIndex A (s.lower i) (s.upper i) ≤ 4 := by
    have hm := sectionIndex_mul_lower_le A (s.lower i) (s.upper i) (s.series.isChief i).lt.le
    have hpidx : 1 ≤ (centralizer (A : Set H)).relIndex (s.lower i).val :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hu := (centralizer (A : Set H)).relIndex_le_of_le_right (s.upper_le i)
      index_ne_zero_of_finite
    nlinarith
  have hf : fixedSpace (ρ.comp A.subtype) ⊤ = fixedSpace ρ A := by
    ext v
    constructor
    · intro hv g
      exact hv ⟨g, mem_top g⟩
    · intro hv g
      exact hv g.val
  have hc := fixed_subgroup_index (ρ.comp A.subtype)
  rw [fixedCodim, hf] at hc
  change (AddSubgroup.toSubgroup' (fixedSpace ρ A).toAddSubgroup).index = 2 ^ fixedCodim ρ A at hc
  have hpow : 2 ^ fixedCodim ρ A ≤ 4 := by
    rw [← hc]
    exact hidx
  have hsmall : fixedCodim ρ A ≤ 2 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 3 ≤ fixedCodim ρ A by omega)
    norm_num at hh
    omega
  have hd := simple_finrank_four_of_small_index q hq hp ρ hnρ A y hy ha heven hsmall
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (s.Factor i))
  rw [hd, Nat.card_zmod] at he
  exact he
end NoncentralChiefRefinement.SymmetricSixBudget

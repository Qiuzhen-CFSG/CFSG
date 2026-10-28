module
public import Theory.AtlasPort.ExceptionalIsomorphisms.NineCoordinates
public import GorensteinWalter.PGL2DerivedSubgroup
public import GorensteinWalter.PGL2InnerAction
public import GorensteinWalter.CyclicOrderThreeAutomorphism
public import Mathlib.GroupTheory.SemidirectProduct
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The canonical cubic normalizer 3 : PGL₂(9)

The derived subgroup of PGL₂(9) has index two. Its quotient supplies the
unique nontrivial action on a cyclic group of order three: the derived
subgroup fixes the group and the other coset inverts it. A split extension
with noncentral cubic kernel therefore has this canonical model.

The recognition equivalence retains arbitrary supplied coordinates on the
kernel and complement, including the literal quotient projection. Its core
requires no finiteness hypothesis on the ambient group.
-/

noncomputable section
open Subgroup
open scoped Classical
namespace Sporadic.Janko3.SourceRecognition.CubicNormalizerModel

/-- The fixed projective linear complement. -/
public abbrev P := GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F
/-- The fixed cubic normal subgroup. -/
public abbrev Z := Multiplicative (ZMod 3)
/-- The canonical index-two subgroup of the complement. -/
public abbrev derived : Subgroup P := commutator P

private theorem field_odd_prime_power :
    GorensteinWalter.IsOddPrimePower (Nat.card Atlas.Comparisons.Exceptional.Nine.F) := by
  rw [Atlas.Comparisons.Exceptional.Nine.card]
  exact ⟨3, 2, by decide, by decide, by decide, by decide⟩

/-- The complement acts through its quotient of order two. -/
public theorem derived_index : derived.index = 2 := by
  rw [derived, GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three
    _ field_odd_prime_power (by rw [Atlas.Comparisons.Exceptional.Nine.card]; decide)]
  exact GorensteinWalter.pgl2_psl2Range_index_eq_two _ field_odd_prime_power

/-- The nonidentity automorphism of the cubic kernel. -/
@[expose] public def inversion : MulAut Z where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' := by intro x y; simp [mul_comm]

private theorem inversion_mul_self : inversion * inversion = 1 := by
  apply MulEquiv.ext
  intro x
  exact inv_inv x

private theorem inversion_ne_one : inversion ≠ 1 := by
  intro he
  have hx := congrArg (fun f : MulAut Z => f (Multiplicative.ofAdd 1)) he
  exact (by decide +kernel :
    (Multiplicative.ofAdd 1 : Z)⁻¹ ≠ Multiplicative.ofAdd 1) hx

/-- The derived subgroup fixes the cubic kernel and its other coset inverts it. -/
public def action : P →* MulAut Z := by
  classical
  exact {
    toFun := fun g => if g ∈ derived then 1 else inversion
    map_one' := by simp
    map_mul' := by
      intro g h
      have hm := derived.mul_mem_iff_of_index_two derived_index (a := g) (b := h)
      by_cases hg : g ∈ derived <;> by_cases hh : h ∈ derived <;>
        simp_all [inversion_mul_self] }

public theorem action_apply (g : P) :
    action g = if g ∈ derived then 1 else inversion := by rfl

public theorem action_ker : action.ker = derived := by
  classical
  ext g
  simp only [MonoidHom.mem_ker, action_apply]
  by_cases hg : g ∈ derived <;> simp [hg, inversion_ne_one]

private theorem z_card : Nat.card Z = 3 := by
  simp [Z, Nat.card_eq_fintype_card, Fintype.card_multiplicative]

private theorem aut_eq_one_or_inversion (a : MulAut Z) : a = 1 ∨ a = inversion := by
  rcases GorensteinWalter.mulAut_eq_one_or_apply_eq_inv_of_card_eq_three z_card a with ha | ha
  · exact Or.inl ha
  · exact Or.inr (MulEquiv.ext ha)

/-- Every nontrivial action on the cubic kernel is the canonical action. -/
public theorem action_unique (ρ : P →* MulAut Z) (hρ : ρ ≠ 1) : ρ = action := by
  classical
  let : CommGroup (MulAut Z) := (IsCyclic.mulAutMulEquiv Z).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv Z).injective
  have hd : derived ≤ ρ.ker := Abelianization.commutator_subset_ker ρ
  have hnot (x : P) (hx : x ∉ derived) : ρ x ≠ 1 := by
    intro hx1
    apply hρ
    apply MonoidHom.ext
    intro y
    change ρ y = 1
    by_cases hy : y ∈ derived
    · exact hd hy
    · have hyx : y * x⁻¹ ∈ derived :=
        (derived.mul_mem_iff_of_index_two derived_index).mpr
          (iff_of_false hy (by simpa using hx))
      have hh : ρ (y * x⁻¹) = 1 := hd hyx
      simpa [map_mul, map_inv, hx1] using hh
  apply MonoidHom.ext
  intro x
  rw [action_apply]
  by_cases hx : x ∈ derived
  · simpa [hx] using (show ρ x = 1 from hd hx)
  · simpa [hx] using (aut_eq_one_or_inversion (ρ x)).resolve_left (hnot x hx)

/-- The canonical cubic normalizer. -/
public abbrev Model := Z ⋊[action] P

/-- The retained quotient projection to the projective linear complement. -/
@[expose] public def projection : Model →* P := SemidirectProduct.rightHom

public theorem projection_ker : projection.ker = (SemidirectProduct.inl : Z →* Model).range :=
  SemidirectProduct.range_inl_eq_ker_rightHom.symm

public theorem p_card : Nat.card P = 720 := by
  rw [GorensteinWalter.pgl2_card_formula, Atlas.Comparisons.Exceptional.Nine.card]
  decide

public instance p_finite : Finite P := Nat.finite_of_card_ne_zero (by rw [p_card]; decide)

public instance model_finite : Finite Model :=
  Finite.of_equiv (Z × P) SemidirectProduct.equivProd.symm

public theorem model_card : Nat.card Model = 2160 := by
  rw [SemidirectProduct.card, z_card, p_card]

variable {E : Type*} [Group E] (V K : Subgroup E) [V.Normal]

private def complementAction : K →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion (V.normalizer_eq_top ▸ le_top))

private def transportedAction (eV : V ≃* Z) (eK : K ≃* P) : P →* MulAut Z :=
  (MulAut.congr eV).toMonoidHom.comp ((complementAction V K).comp eK.symm.toMonoidHom)

private theorem transportedAction_ne_one (hcomp : V.IsComplement' K)
    (eV : V ≃* Z) (eK : K ≃* P) (hnc : ¬ V ≤ center E) :
    transportedAction V K eV eK ≠ 1 := by
  intro he
  apply hnc
  intro v hv
  apply mem_center_iff.mpr
  intro g
  obtain ⟨⟨w, k⟩, rfl⟩ := hcomp.2 g
  have hfix : complementAction V K k ⟨v, hv⟩ = ⟨v, hv⟩ := by
    apply eV.injective
    have hh := congrArg (fun ρ : P →* MulAut Z => ρ (eK k) (eV ⟨v, hv⟩)) he
    simpa [transportedAction, MulAut.congr] using hh
  have hkv : (k : E) * v = v * k := by
    have hh := congrArg Subtype.val hfix
    change (k : E) * v * (k : E)⁻¹ = v at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hwv : (w : E) * v = v * w := by
    exact congrArg Subtype.val (eV.injective (show eV (w * ⟨v, hv⟩) = eV (⟨v, hv⟩ * w) by
      rw [map_mul, map_mul, mul_comm]))
  rw [mul_assoc, hkv, ← mul_assoc, hwv, mul_assoc]

private theorem action_compat (hcomp : V.IsComplement' K)
    (eV : V ≃* Z) (eK : K ≃* P) (hnc : ¬ V ≤ center E) (k : K) :
    (complementAction V K k).trans eV = eV.trans (action (eK k)) := by
  have he := action_unique (transportedAction V K eV eK)
    (transportedAction_ne_one V K hcomp eV eK hnc)
  apply MulEquiv.ext
  intro v
  have hh := congrArg (fun ρ : P →* MulAut Z => ρ (eK k) (eV v)) he
  simpa [transportedAction, MulAut.congr] using hh

/-- Recognition retaining the prescribed coordinates on both complementary subgroups. -/
public def splitEquiv (hcomp : V.IsComplement' K)
    (eV : V ≃* Z) (eK : K ≃* P) (hnc : ¬ V ≤ center E) : E ≃* Model :=
  (SemidirectProduct.mulEquivSubgroup hcomp).symm.trans
    (SemidirectProduct.congr eV eK (action_compat V K hcomp eV eK hnc))

public theorem splitEquiv_apply_mul (hcomp : V.IsComplement' K)
    (eV : V ≃* Z) (eK : K ≃* P) (hnc : ¬ V ≤ center E) (v : V) (k : K) :
    splitEquiv V K hcomp eV eK hnc ((v : E) * k) = ⟨eV v, eK k⟩ := by
  change SemidirectProduct.congr eV eK (action_compat V K hcomp eV eK hnc)
    ((SemidirectProduct.mulEquivSubgroup hcomp).symm ((v : E) * k)) = _
  have hi : (SemidirectProduct.mulEquivSubgroup hcomp).symm ((v : E) * k) = ⟨v, k⟩ :=
    (SemidirectProduct.mulEquivSubgroup hcomp).symm_apply_apply ⟨v, k⟩
  rw [hi]
  rfl

public theorem splitEquiv_apply_V (hcomp : V.IsComplement' K)
    (eV : V ≃* Z) (eK : K ≃* P) (hnc : ¬ V ≤ center E) (v : V) :
    splitEquiv V K hcomp eV eK hnc v = SemidirectProduct.inl (eV v) := by
  simpa using splitEquiv_apply_mul V K hcomp eV eK hnc v (1 : K)

public theorem splitEquiv_apply_K (hcomp : V.IsComplement' K)
    (eV : V ≃* Z) (eK : K ≃* P) (hnc : ¬ V ≤ center E) (k : K) :
    splitEquiv V K hcomp eV eK hnc k = SemidirectProduct.inr (eK k) := by
  simpa using splitEquiv_apply_mul V K hcomp eV eK hnc (1 : V) k

public theorem splitEquiv_projection (hcomp : V.IsComplement' K)
    (eV : V ≃* Z) (eK : K ≃* P) (hnc : ¬ V ≤ center E) :
    projection.comp (splitEquiv V K hcomp eV eK hnc).toMonoidHom =
      (eK.toMonoidHom.comp hcomp.symm.QuotientMulEquiv.toMonoidHom).comp
        (QuotientGroup.mk' V) := by
  apply MonoidHom.ext
  intro g
  obtain ⟨⟨v, k⟩, rfl⟩ := hcomp.2 g
  have hv : QuotientGroup.mk' V (v : E) = 1 := by
    exact (QuotientGroup.eq_one_iff (v : E)).mpr v.property
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul,
    splitEquiv_apply_V, splitEquiv_apply_K, projection,
    SemidirectProduct.rightHom_inl, SemidirectProduct.rightHom_inr,
    hv, map_one, one_mul, quotientMulEquiv_mk_apply_of_isComplement']

/-- The order-three kernel supplies its own coordinates; the given complement marking is retained. -/
public theorem exists_splitEquiv (hcomp : V.IsComplement' K) (eK : K ≃* P)
    (hV : Nat.card V = 3) (hnc : ¬ V ≤ center E) :
    ∃ (eV : V ≃* Z) (e : E ≃* Model),
      (∀ v : V, e v = SemidirectProduct.inl (eV v)) ∧
      (∀ k : K, e k = SemidirectProduct.inr (eK k)) ∧
      (∀ (v : V) (k : K), e ((v : E) * k) = ⟨eV v, eK k⟩) ∧
      projection.comp e.toMonoidHom =
        (eK.toMonoidHom.comp hcomp.symm.QuotientMulEquiv.toMonoidHom).comp
          (QuotientGroup.mk' V) := by
  let eV : V ≃* Z := mulEquivOfPrimeCardEq hV z_card
  exact ⟨eV, splitEquiv V K hcomp eV eK hnc,
    splitEquiv_apply_V V K hcomp eV eK hnc,
    splitEquiv_apply_K V K hcomp eV eK hnc,
    splitEquiv_apply_mul V K hcomp eV eK hnc,
    splitEquiv_projection V K hcomp eV eK hnc⟩

end Sporadic.Janko3.SourceRecognition.CubicNormalizerModel

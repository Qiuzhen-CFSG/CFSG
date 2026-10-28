module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LocalActions
public import Theory.GroupAction.OddInvolutionFrattini
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.RepresentationTheory.Basic

/-!
# Literal invariant root sections and their effective quotients

A section X/Y of a canonical radical carries the actual rank-one
conjugation action. Its normality is relative to X. In the split setting,
H ∩ U = 1, so H ∩ X = 1; we identify the literal ordered product
Φ(X)Y(H ∩ X) with the normal subgroup used for the quotient. The quotient
is elementary abelian and carries the induced binary representation.

An odd-order actor trivial on this quotient is trivial on X/Y: the image
of Φ(X)Y in X/Y lies in Φ(X/Y), and coprime Frattini faithfulness applies.
The companion EffectiveSections module applies this to the actual radical.

Source: Fong--Seitz, Groups with a (B,N)-pair of rank 2, I (1973),
(5D)--(5F), printed pp.26--28.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates

def sectionQuotientAction {R A : Type*} [Group R] [Group A]
    (ρ : R →* MulAut A) (B : Subgroup A) [B.Normal]
    (hB : ∀ r, B.map (ρ r).toMonoidHom = B) : R →* MulAut (A ⧸ B) where
  toFun r := QuotientGroup.congr B B (ρ r) (hB r)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp only [QuotientGroup.congr_mk, map_one]; rfl
  map_mul' r s := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      change QuotientGroup.mk (ρ (r*s) x) = QuotientGroup.mk (ρ r (ρ s x))
      rw [map_mul]; rfl

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- An actual invariant section of the canonical radical. Normality is relative
    to the numerator, rather than to the entire finite quotient. -/
structure RootSection (i : Fin 2) where
  numerator : Subgroup (X ⧸ Q.D)
  le_radical : numerator ≤ simpleRemainder Q split i
  normalized : rankOne Q split i ≤ normalizer (numerator : Set (X ⧸ Q.D))
  denominator : Subgroup numerator
  [normal : denominator.Normal]
  invariant : ∀ r : rankOne Q split i,
    denominator.map (numerator.normalizerMonoidHom (inclusion normalized r)).toMonoidHom = denominator

attribute [instance] RootSection.normal
namespace RootSection
variable {Q split} {i : Fin 2} (d : RootSection Q split i)

def numeratorAction : rankOne Q split i →* MulAut d.numerator :=
  d.numerator.normalizerMonoidHom.comp (inclusion d.normalized)

@[simp] theorem numeratorAction_apply (r : rankOne Q split i) (x : d.numerator) :
    (d.numeratorAction r x : X ⧸ Q.D) = (r : X ⧸ Q.D)*x*(r : X ⧸ Q.D)⁻¹ := rfl

/-- The source's H ∩ X is trivial for this literal section. -/
theorem cartan_intersection : (Q.tits.B ⊓ Q.tits.N).subgroupOf d.numerator = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply Subtype.ext
  have h : (x : X ⧸ Q.D) ∈ split.U ⊓ Q.tits.N :=
    ⟨(d.le_radical x.property).1, hx.2⟩
  exact mem_bot.mp (split.unipotent_inf_N ▸ h)

/-- The literal denominator Φ(X) Y (H ∩ X) in (5D). -/
def effectiveDenominator : Subgroup d.numerator :=
  frattini d.numerator ⊔ d.denominator ⊔ (Q.tits.B ⊓ Q.tits.N).subgroupOf d.numerator

theorem effectiveDenominator_eq :
    d.effectiveDenominator = frattini d.numerator ⊔ d.denominator := by
  rw [effectiveDenominator, d.cartan_intersection, sup_bot_eq]

instance effectiveDenominator_normal : d.effectiveDenominator.Normal := by
  rw [d.effectiveDenominator_eq]
  infer_instance

/-- The joins above are the source's ordered product, not a replacement denominator. -/
theorem effectiveDenominator_product :
    (d.effectiveDenominator : Set d.numerator) =
      (frattini d.numerator : Set d.numerator) * (d.denominator : Set d.numerator) *
        ((Q.tits.B ⊓ Q.tits.N).subgroupOf d.numerator : Set d.numerator) := by
  rw [d.cartan_intersection]
  change (d.effectiveDenominator : Set d.numerator) =
    (frattini d.numerator : Set d.numerator) * (d.denominator : Set d.numerator) * 1
  rw [mul_one, d.effectiveDenominator_eq, Subgroup.mul_normal]

theorem effectiveDenominator_invariant (r : rankOne Q split i) :
    d.effectiveDenominator.map (d.numeratorAction r).toMonoidHom = d.effectiveDenominator := by
  rw [d.effectiveDenominator_eq, Subgroup.map_sup]
  change (frattini d.numerator).map (d.numeratorAction r).toMonoidHom ⊔
    d.denominator.map (d.numeratorAction r).toMonoidHom = _
  rw [show d.denominator.map (d.numeratorAction r).toMonoidHom = d.denominator from d.invariant r]
  rw [characteristic_iff_map_eq.mp (inferInstance : (frattini d.numerator).Characteristic)]

abbrev Carrier := d.numerator ⧸ d.denominator
abbrev EffectiveCarrier := d.numerator ⧸ d.effectiveDenominator

def action : rankOne Q split i →* MulAut d.Carrier :=
  sectionQuotientAction d.numeratorAction d.denominator d.invariant

def effectiveAction : rankOne Q split i →* MulAut d.EffectiveCarrier :=
  sectionQuotientAction d.numeratorAction d.effectiveDenominator d.effectiveDenominator_invariant

@[simp] theorem action_mk (r : rankOne Q split i) (x : d.numerator) :
    d.action r (QuotientGroup.mk x) = QuotientGroup.mk (d.numeratorAction r x) := rfl

@[simp] theorem effectiveAction_mk (r : rankOne Q split i) (x : d.numerator) :
    d.effectiveAction r (QuotientGroup.mk x) = QuotientGroup.mk (d.numeratorAction r x) := rfl

theorem isTwo : IsPGroup 2 d.numerator :=
  split.isTwo.of_injective (inclusion (d.le_radical.trans inf_le_left)) (inclusion_injective _)

/-- The exact effective quotient has its canonical binary vector-space structure. -/
instance effective_elementary : IsElementaryAbelian 2 d.EffectiveCarrier := by
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  have hphi : frattini d.numerator ≤ d.effectiveDenominator := by
    rw [d.effectiveDenominator_eq]
    exact le_sup_left
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      ((commutator_le_frattini_of_isPGroup (p := 2)).trans hphi)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro z
    induction z using QuotientGroup.induction_on with
    | H x =>
      change (QuotientGroup.mk' d.effectiveDenominator x)^2 = 1
      rw [←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr
        (hphi (pth_power_mem_frattini_of_isPGroup (p := 2) x))

/-- The actual binary representation on X/Φ(X)Y(H ∩ X). -/
def effectiveRepresentation : Representation (ZMod 2) (rankOne Q split i)
    (Additive d.EffectiveCarrier) where
  toFun r := (d.effectiveAction r).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by ext v; simp only [map_one]; rfl
  map_mul' r s := by ext v; simp only [map_mul]; rfl

@[simp] theorem effectiveRepresentation_mk (r : rankOne Q split i) (x : d.numerator) :
    d.effectiveRepresentation r (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk (d.numeratorAction r x)) := by rfl

theorem effectiveRepresentation_injective (hf : Function.Injective d.effectiveAction) :
    Function.Injective d.effectiveRepresentation := by
  intro r s he
  apply hf
  ext v
  exact Additive.ofMul.injective (congrArg
    (fun f : Module.End (ZMod 2) (Additive d.EffectiveCarrier) => f (Additive.ofMul v)) he)

/-- Coprime Frattini faithfulness on the actual source section. -/
theorem action_eq_one_of_odd (r : rankOne Q split i) (ho : Nat.Coprime (orderOf r) 2)
    (hr : d.effectiveAction r = 1) : d.action r = 1 := by
  apply OddInvolutionFrattini.automorphism_eq_one_of_quotient_eq_one
    (d.isTwo.to_quotient d.denominator) _ (ho.of_dvd_left (orderOf_map_dvd d.action r))
  ext z
  induction z using QuotientGroup.induction_on with
  | H z =>
    induction z using QuotientGroup.induction_on with
    | H x =>
      change quotientAut (frattini d.Carrier) (d.action r)
        (QuotientGroup.mk' (frattini d.Carrier) (QuotientGroup.mk' d.denominator x)) =
        QuotientGroup.mk' (frattini d.Carrier) (QuotientGroup.mk' d.denominator x)
      rw [quotientAut_apply_mk]
      change QuotientGroup.mk (d.action r (QuotientGroup.mk x)) = QuotientGroup.mk (QuotientGroup.mk x)
      rw [d.action_mk]
      change QuotientGroup.mk' (frattini d.Carrier) (QuotientGroup.mk' d.denominator (d.numeratorAction r x)) =
        QuotientGroup.mk' (frattini d.Carrier) (QuotientGroup.mk' d.denominator x)
      apply QuotientGroup.eq_iff_div_mem.mpr
      rw [← map_div]
      have hx : d.numeratorAction r x / x ∈ d.effectiveDenominator := by
        apply QuotientGroup.eq_iff_div_mem.mp
        change d.effectiveAction r (QuotientGroup.mk x) = QuotientGroup.mk x
        rw [hr]; rfl
      have hle : d.effectiveDenominator ≤ (frattini d.Carrier).comap (QuotientGroup.mk' d.denominator) := by
        rw [d.effectiveDenominator_eq]
        apply sup_le (frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective _))
        intro y hy
        change QuotientGroup.mk' d.denominator y ∈ frattini d.Carrier
        have he : QuotientGroup.mk' d.denominator y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
        rw [he]
        exact one_mem _
      exact hle hx

/-- Effectiveness means containment in the literal panel kernel. -/
def IsEffective : Prop := d.effectiveAction.ker ≤ (localKernel Q i).subgroupOf (rankOne Q split i)
end RootSection
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

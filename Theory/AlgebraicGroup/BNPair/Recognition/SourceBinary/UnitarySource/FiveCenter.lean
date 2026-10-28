module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FiveCoefficients

/-!
# Central Hermitian corrections, including the exceptional U₅ branch

A homomorphism of the full Hermitian root group with first coordinate
x ↦ a*x has second coordinate z ↦ a*conj(a)*z on its center. Every central
element is exhibited as a commutator using a trace-one scalar, and the
existing exact Hermitian commutator formula proves the assertion.

Apply this to the correction homomorphism obtained by associativity in
FiveCoefficients. This recovers the central-parameter step used in
Fong--Seitz II (8.30), p.207, directly in the presentation convention. It
works at q=2 and q=4 and requires no ordinary-branch Cartan scalar. The original root charts and preceding crossing laws remain source inputs.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open scoped commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.FiveCenter
variable {E : Type*} [Field E] [CharP E 2]
variable (J : HermitianForm 5 E)

/-- Construct a full Hermitian parameter with prescribed first coordinate. -/
theorem exists_parameter_first (κ : E) (hκ : κ+J.conj κ=1) (x : E) :
    ∃ p : FivePositive.Parameter J, p.val.1=x := by
  refine ⟨⟨(x,κ*x*J.conj x),?_⟩,rfl⟩
  change κ*x*J.conj x+J.conj (κ*x*J.conj x)+x*J.conj x=0
  simp only [map_mul, J.conj_involutive x]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) x*J.conj x*hκ

/-- The commutator law forces the norm action on every central parameter. -/
theorem hom_on_center (κ : E) (hκ : κ+J.conj κ=1)
    (F : FivePositive.Parameter J →* FivePositive.Parameter J) (a : E)
    (hfirst : ∀ p, (F p).val.1=a*p.val.1)
    (p : FivePositive.Parameter J) (hp : p.val.1=0) :
    F p = FivePositive.normParameter J a p := by
  have hpfix : J.conj p.val.2=p.val.2 := by
    have h := FivePositive.parameter_relation J p
    rw [hp, zero_mul] at h
    exact (eq_neg_of_add_eq_zero_right h).trans (CharTwo.neg_eq _)
  obtain ⟨u,hu⟩ := exists_parameter_first J κ hκ 1
  obtain ⟨v,hv⟩ := exists_parameter_first J κ hκ (κ*p.val.2)
  have hcomm : ⁅u,v⁆=p := by
    rw [hermitianUnipotent_commutator]
    apply Subtype.ext
    apply Prod.ext hp.symm
    change v.val.1*J.conj u.val.1-u.val.1*J.conj v.val.1=p.val.2
    rw [hu,hv,map_one,mul_one,one_mul,CharTwo.sub_eq_add,map_mul,hpfix]
    linear_combination p.val.2*hκ
  have hmap : F p=⁅F u,F v⁆ := by rw [← map_commutatorElement, hcomm]
  rw [hmap, hermitianUnipotent_commutator]
  apply Subtype.ext
  apply Prod.ext
  · change 0=a*p.val.1
    rw [hp,mul_zero]
  · change (F v).val.1*J.conj (F u).val.1-(F u).val.1*J.conj (F v).val.1 =
      a*J.conj a*p.val.2
    simp only [hfirst, hu, hv, mul_one, map_mul, hpfix, CharTwo.sub_eq_add]
    linear_combination a*J.conj a*p.val.2*hκ

variable {Y : Type*} [Group Y]
variable (r : PositiveMaps Y (Multiplicative E) (FivePositive.Parameter J)
  (Multiplicative E) (FivePositive.Parameter J))
variable (T : FivePositive.Parameter J → E → FivePositive.Parameter J)

/-- Recover the actual central mixed correction from the source multiplication identities, with no torus-action premise. -/
theorem correction_on_center (κ : E) (hκ : κ+J.conj κ=1)
    (hD : Function.Injective r.D)
    (hfst : ∀ (p : FivePositive.Parameter J) (a : E), (T p a).val.1=a*p.val.1)
    (hCD : ∀ c d, Commute (r.C c) (r.D d))
    (hBC : ∀ p c, Commute (r.B p) (r.C c))
    (hBD : ∀ p q, r.B p*r.D q = r.D q*
      r.C (Multiplicative.ofAdd (q.val.1*J.conj p.val.1))*r.B p)
    (hBA : ∀ a p, r.B p*r.A (Multiplicative.ofAdd a) =
      r.A (Multiplicative.ofAdd a)*r.D (T p a)*
        r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*r.B p)
    (p : FivePositive.Parameter J) (hp : p.val.1=0) (a : E) :
    T p a=FivePositive.normParameter J a p := by
  let F : FivePositive.Parameter J →* FivePositive.Parameter J := MonoidHom.mk'
    (fun q => T q a) (fun u v => FiveCoefficients.correction_mul J r T hCD hBA hD hfst hBC hBD u v a)
  exact hom_on_center J κ hκ F a (fun q => hfst q a) p hp

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.FiveCenter

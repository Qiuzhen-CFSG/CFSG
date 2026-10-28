module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.Initial
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Defs
public import Theory.Quasithin.Rank
public import CFSG.Quasithin.ChapterA.Section01.PStructure
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ExtraspecialExtensions
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# The natural action of the defining-prime Fitting core

Let L be a C-component of a finite strongly quasithin group, with noncentral
Fitting subgroup F = Oₚ(L), p > 3, and an actual quotient L/F ≃ SL₂(p).
Assume the independently supplied extraspecial or homocyclic core shape.
The exponent-p extraspecial group is identified with the Heisenberg model;
A.1.33(2) then contradicts the ambient rank bound.

For the homocyclic shape, F* = F makes the core self-centralizing. First omega
detects its centralizer, so the literal quotient action is faithful on Ω₂.
The actual homocyclic coordinates identify Ω₂ with C(p²) × C(p²) whenever
the exponent exceeds one, contradicting A.1.30. This restriction uses the
same defining prime in both the core and SL₂ quotient.

Finally the core coordinates turn conjugation into a faithful matrix action.
Perfectness forces determinant one, and the given quotient order makes the
matrix homomorphism onto SL₂(p). The resulting quotient equivalence satisfies
the literal conjugation equation in `NaturalSL2Action`. The export `hnatural`
discharges exactly that premise of `CoreShapes.structure_of_prime_core_data`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6, printed p.44, using A.1.30 (p.27) and A.1.33(2) (p.29).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02 LocalModels
open CFSG.Quasithin.ChapterA.RankActions
open CFSG.Quasithin CFSG.Quasithin.ChapterA
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.DefiningPrime

universe u
variable {G : Type u} [Group G] [Finite G] {L : Subgroup G}
variable {p : ℕ} [Fact p.Prime]

/-- A.1.33(2) excludes the extraspecial core using the actual Fitting quotient. -/
theorem not_extraspecial {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hp : 3 < p)
    (e : (L ⧸ fittingSubgroup L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hF : fittingSubgroup L = pCore p L) :
    ¬ OddExtraspecialThree p (pCore p L) := by
  intro hs
  let P := pCore p L
  let : IsExtraspecial p P := hs.1.1
  have hc : Nat.card P = p ^ 3 := hs.1.2
  have hclass : _root_.commutator P ≤ center P :=
    (IsExtraspecial.commutator_eq_center (p := p) (P := P)).le
  have hna : ¬ IsMulCommutative P := by
    intro ha
    let := ha
    have hz : center P = ⊤ := center_eq_top
    have he := IsExtraspecial.center_order_p p P
    rw [hz, Nat.card_congr (topEquiv (G := P)).toEquiv, hc] at he
    have hlt : p < p ^ 3 := by
      have hh := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by decide : 1 < 3)
      simpa only [pow_one] using hh
    omega
  obtain ⟨f⟩ := HeisenbergPrime.nonempty_mulEquiv_of_card_prime_cube hc hs.2 hclass hna
  have hr := primeRank_gt_two_of_extraspecial_sl2 P f hp
    ((QuotientGroup.quotientMulEquivOfEq hF.symm).trans e)
  have hb := (primeRank_subgroup_le p L).trans
    (hG.stronglyQuasithin p Fact.out ((Fact.out : p.Prime).odd_of_ne_two (by omega)))
  omega

variable {A : Type*} [Group A] [Finite A]

omit [Finite A] in
private theorem abelian_le_conj_ker (N : Subgroup A) [N.Normal] [IsMulCommutative N] :
    N ≤ (MulAut.conjNormal : A →* MulAut N).ker := by
  intro x hx
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  change x * y * x⁻¹ = y
  have he := congrArg (fun z : N => (z : A)) (mul_comm (⟨x, hx⟩ : N) y)
  change x * y = y * x at he
  rw [he, mul_inv_cancel_right]

private noncomputable def quotientAction (N : Subgroup A) [N.Normal] [IsMulCommutative N] :
    (A ⧸ N) →* MulAut N :=
  QuotientGroup.lift N MulAut.conjNormal (abelian_le_conj_ker N)

omit [Finite A] in
private theorem quotientAction_injective (N : Subgroup A) [N.Normal] [IsMulCommutative N]
    (hC : centralizer (N : Set A) ≤ N) : Function.Injective (quotientAction N) := by
  apply (QuotientGroup.injective_lift_iff N MulAut.conjNormal (abelian_le_conj_ker N)).mpr
  apply le_antisymm (abelian_le_conj_ker N)
  intro x hx
  apply hC
  intro y hy
  have he := congrArg (fun a : MulAut N => (a ⟨y, hy⟩ : A)) hx
  change x * y * x⁻¹ = y at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem omega_quotientAction_injective [IsMulCommutative (pCore p A)]
    (hC : centralizer (pCore p A : Set A) ≤ pCore p A) {k : ℕ} (hk : 1 ≤ k) :
    Function.Injective ((OmegaAction.omegaRestriction (pCore p A) p k).comp
      (quotientAction (pCore p A))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore p A) q
  apply (QuotientGroup.eq_one_iff _).mpr
  apply OmegaAction.centralizer_omegaOne_pCore_le hC
  rintro y ⟨z, hz, rfl⟩
  have hzk : z ∈ omega (pCore p A) (p := p) k := by
    have hz1 : z ^ (p ^ 1) = 1 := by
      rw [OmegaAction.omega_eq_pow_ker] at hz
      exact hz
    obtain ⟨m, hm⟩ := pow_dvd_pow p hk
    apply Subgroup.subset_closure
    change z ^ (p ^ k) = 1
    rw [hm, pow_mul, hz1, one_pow]
  have he := congrArg (fun a : MulAut (omega (pCore p A) (p := p) k) =>
    ((a ⟨z, hzk⟩ : pCore p A) : A)) hq
  change x * z * x⁻¹ = z at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private noncomputable def twoCoordinatesEquiv (n : ℕ) :
    Multiplicative (Fin 2 → ZMod n) ≃*
      (Multiplicative (ZMod n) × Multiplicative (ZMod n)) :=
  (AddEquiv.toMultiplicative (LinearEquiv.finTwoArrow (ZMod n) (ZMod n)).toAddEquiv).trans
    (MulEquiv.prodMultiplicative _ _)

private noncomputable def cyclicOmegaEquiv (p a k : ℕ) [Fact p.Prime] (hk : k ≤ a) :
    omega (Multiplicative (ZMod (p ^ a))) (p := p) k ≃*
      Multiplicative (ZMod (p ^ k)) := by
  rw [OmegaAction.omega_eq_pow_ker]
  apply mulEquivOfCyclicCardEq
  rw [IsCyclic.card_powMonoidHom_ker]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact Nat.gcd_eq_right (pow_dvd_pow p hk)

private noncomputable def productOmegaEquiv (p a k : ℕ) [Fact p.Prime] (hk : k ≤ a) :
    omega (Multiplicative (ZMod (p ^ a)) × Multiplicative (ZMod (p ^ a))) (p := p) k ≃*
      (Multiplicative (ZMod (p ^ k)) × Multiplicative (ZMod (p ^ k))) := by
  have he : omega (Multiplicative (ZMod (p ^ a)) × Multiplicative (ZMod (p ^ a))) (p := p) k =
      (omega (Multiplicative (ZMod (p ^ a))) (p := p) k).prod
        (omega (Multiplicative (ZMod (p ^ a))) (p := p) k) := by
    simp only [OmegaAction.omega_eq_pow_ker]
    ext x
    change x ^ (p ^ k) = 1 ↔ x.1 ^ (p ^ k) = 1 ∧ x.2 ^ (p ^ k) = 1
    exact Prod.ext_iff
  exact (MulEquiv.subgroupCongr he).trans ((prodEquiv _ _).trans
    ((cyclicOmegaEquiv p a k hk).prodCongr (cyclicOmegaEquiv p a k hk)))

private theorem homocyclic_exponent_one (hp : 3 < p)
    (hC : centralizer (pCore p A : Set A) ≤ pCore p A)
    (eQ : (A ⧸ pCore p A) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    {a : ℕ} (ha : 1 ≤ a)
    (e : pCore p A ≃* Multiplicative (Fin 2 → ZMod (p ^ a))) : a = 1 := by
  by_contra hn
  have ha2 : 2 ≤ a := by omega
  let : IsMulCommutative (pCore p A) :=
    ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  let eO := ((e.trans (twoCoordinatesEquiv (p ^ a))).omega p 2).trans
    (productOmegaEquiv p a 2 ha2)
  let f := ((OmegaAction.omegaRestriction (pCore p A) p 2).comp
    (quotientAction (pCore p A))).comp eQ.symm.toMonoidHom
  exact (lemma_A_1_30 hp eO).2 f
    ((omega_quotientAction_injective hC (by decide : 1 ≤ 2)).comp eQ.symm.injective)

private def vectorAutAdd (a : MulAut (Multiplicative (Fin 2 → ZMod p))) :
    (Fin 2 → ZMod p) ≃+ (Fin 2 → ZMod p) where
  toFun v := (a (Multiplicative.ofAdd v)).toAdd
  invFun v := (a.symm (Multiplicative.ofAdd v)).toAdd
  left_inv v := a.left_inv v
  right_inv v := a.right_inv v
  map_add' v w := a.map_mul v w

private def vectorAutLinear : MulAut (Multiplicative (Fin 2 → ZMod p)) ≃*
    ((Fin 2 → ZMod p) ≃ₗ[ZMod p] (Fin 2 → ZMod p)) where
  toFun a := { vectorAutAdd a with map_smul' := ZMod.map_smul (vectorAutAdd a) }
  invFun a := a.toAddEquiv.toMultiplicative
  left_inv a := by ext; rfl
  right_inv a := by ext; rfl
  map_mul' a b := by ext; rfl

private def matrixAutEquiv : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) ≃*
    MulAut (Multiplicative (Fin 2 → ZMod p)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin 2 → ZMod p)).trans
      vectorAutLinear.symm)

private theorem matrixAutEquiv_apply (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
    (v : Multiplicative (Fin 2 → ZMod p)) :
    matrixAutEquiv g v = Multiplicative.ofAdd (Matrix.mulVec g.val v.toAdd) := rfl

omit [Finite A] in
private theorem natural_of_coordinates [Group.IsPerfect A]
    (N : Subgroup A) [N.Normal] (hC : centralizer (N : Set A) ≤ N)
    (v : N ≃* Multiplicative (Fin 2 → ZMod p))
    (eQ : (A ⧸ N) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
    NaturalSL2Action A N p := by
  let : IsMulCommutative N :=
    ⟨⟨fun x y => v.injective (by simp only [map_mul, mul_comm])⟩⟩
  let j := (MulAut.congr v).trans matrixAutEquiv.symm
  let f := j.toMonoidHom.comp (quotientAction N)
  have hf : Function.Injective f := j.injective.comp (quotientAction_injective N hC)
  have hd (x : A ⧸ N) : (f x).det = 1 :=
    Abelianization.commutator_subset_ker (Matrix.GeneralLinearGroup.det.comp f)
      Group.IsPerfect.mem_commutator
  let s : (A ⧸ N) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    { toFun := fun x => ⟨(f x : Matrix (Fin 2) (Fin 2) (ZMod p)), congrArg Units.val (hd x)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; exact congrArg Units.val (f.map_mul x y) }
  have hs : Function.Injective s := by
    intro x y hxy
    apply hf
    exact Units.ext (congrArg Subtype.val hxy)
  let ρ := MulEquiv.ofBijective s
    (hs.bijective_of_nat_card_le (Nat.card_congr eQ.toEquiv).ge)
  refine ⟨ZMod p, inferInstance, inferInstance, Nat.card_zmod p, v, ρ, ?_⟩
  intro g x
  have he := congrArg (fun a : MulAut (Multiplicative (Fin 2 → ZMod p)) => a (v x))
    (matrixAutEquiv.apply_symm_apply (MulAut.congr v (quotientAction N (QuotientGroup.mk' N g))))
  change matrixAutEquiv (f (QuotientGroup.mk' N g)) (v x) =
    v (MulAut.conjNormal g (v.symm (v x))) at he
  rw [v.symm_apply_apply, matrixAutEquiv_apply] at he
  exact he.symm

/-- In the defining-prime case, the supplied core shapes force the actual
natural action on F*(L). The extraspecial branch contradicts A.1.33(2),
and A.1.30 on Ω₂ forces the homocyclic exponent to be one. -/
theorem natural_action_of_shape {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G)
    (hL : L.IsCComponent) (hn : ¬ fittingSubgroup L ≤ center L)
    (hp : 3 < p)
    (eQ : (L ⧸ fittingSubgroup L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hF : fittingSubgroup L = pCore p L)
    (hs : OddExtraspecialThree p (pCore p L) ∨ HomocyclicTwo p (pCore p L)) :
    NaturalSL2Action L (generalizedFitting L) p := by
  have hgen := generalizedFitting_eq_fitting hL hn
  have hC : centralizer (pCore p L : Set L) ≤ pCore p L := by
    simpa only [hgen, hF] using centralizer_generalizedFitting_le L
  obtain ⟨a, ha, ⟨e⟩⟩ := hs.resolve_left (not_extraspecial hG hp eQ hF)
  have ha1 := homocyclic_exponent_one hp hC
    ((QuotientGroup.quotientMulEquivOfEq hF.symm).trans eQ) ha e
  subst a
  have he : Nonempty (pCore p L ≃* Multiplicative (Fin 2 → ZMod p)) := by
    rw [Nat.pow_one] at e
    exact ⟨e⟩
  let : Group.IsPerfect L := hL.perfect
  exact natural_of_coordinates (generalizedFitting L)
    (centralizer_generalizedFitting_le L)
    ((MulEquiv.subgroupCongr (hgen.trans hF)).trans he.some)
    ((QuotientGroup.quotientMulEquivOfEq hgen).trans eQ)

/-- Discharges precisely the `hnatural` argument of
`CoreShapes.structure_of_prime_core_data`. Support and core shape remain
independent inputs of that consumer; no new premise is added here. -/
theorem hnatural {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G)
    (hL : L.IsCComponent) (hn : ¬ fittingSubgroup L ≤ center L) :
    ∀ (r : ℕ) [Fact r.Prime], 3 < r →
      Nonempty ((L ⧸ fittingSubgroup L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) →
      fittingSubgroup L = pCore r L →
      (OddExtraspecialThree r (pCore r L) ∨ HomocyclicTwo r (pCore r L)) →
      NaturalSL2Action L (generalizedFitting L) r := by
  intro r hr hr3 he hF hs
  exact natural_action_of_shape hG hL hn hr3 he.some hF hs

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.DefiningPrime

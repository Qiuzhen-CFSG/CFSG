module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterInvolution
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootFrame
public import Theory.SpecificGroups.Triality.StandardTwoRank.FourSemilinear.HighestRoot
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.UnipotentCocycle.Descent
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterTorus

/-!
# Fixed positive roots of a triality torus--coefficient action

The genuine positive subgroup has three parameters over GF(q³) and three
in the q-Frobenius fixed field. An involution of GF(q³) restricts nontrivially
to GF(q), since the intervening extension has odd degree three. Each scalar
fixed-point equation has at most the corresponding fixed-field order of
solutions. Uniqueness of the twelve descended root coordinates therefore
gives at most q^6 fixed elements, for every actual torus element.

The original right-parabolic map transports this estimate to C_S(t) when
its local action agrees with that torus--coefficient action. The existing
whole-overlap splitting then gives |C_T(t)| < q^7, using [T:S] < q and the
proved equality of the model and source field exponents. The Chapter 12
companion applies this estimate with the literal chosen-module hypotheses.

The local action identity remains an explicit premise: two compatible
parabolic automorphisms have not yet been extended or identified with this
model action. Its construction and the ambient Sylow placement in F.4.37
remain necessary for S=T. Exhaustive comparison, original uniqueness and
ambient recognition remain obligations of the generic-global assembly.

Source: Aschbacher--Smith F.4.37--38, pp.293--294, and 5.3.3, p.659
(`refs/quasithin.pdf`); GLS3 §§2.4--2.6 for the actual folded-root coordinates.
The internal import reuses this source family's torus-weight calculation
without changing its public boundary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat Triality.Standard.PositiveCoordinates
open Triality.Standard.OuterOdd Triality.Standard.OuterOdd.Coverage
open Triality.Standard.CentralCovers.TwoPrimary
open Triality.Standard.EvenField.NormalForm.UnipotentCocycle
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityOuterFixed

private theorem fixed_base_card (P : Parameters) (σ : CoefficientAut P)
    (hσ : orderOf σ = 2) :
    Nat.card (FixedBy.subfield (fixedField P) (coefficientFixedField P σ))^2 = P.q := by
  have hs : Function.Involutive σ := fun x =>
    DFunLike.congr_fun (show σ^2=1 from (orderOf_eq_prime_iff.mp hσ).1) x
  have hb : Function.Involutive (coefficientFixedField P σ) := fun x => Subtype.ext (hs x.val)
  have hn : coefficientFixedField P σ ≠ RingEquiv.refl (fixedField P) := by
    intro he
    apply TwoRank.FourSemilinear.coefficient_not_fixed_base_of_parameters P σ (by rw [hσ])
    intro x
    exact congrArg Subtype.val (DFunLike.congr_fun he x)
  exact (FiniteField.card_involution_fixed_sq _ hb hn).trans (card_fixedField P)

private theorem scalar_base_fixed_le (P : Parameters) (σ : CoefficientAut P)
    (c : ExtensionField P) :
    Nat.card {x : fixedField P // c * σ x.val = x.val} ≤
      Nat.card (FixedBy.subfield (fixedField P) (coefficientFixedField P σ)) := by
  classical
  by_cases h : ∃ w : fixedField P, c * σ w.val = w.val ∧ w ≠ 0
  · obtain ⟨w,hw,hw0⟩ := h
    have hwv : w.val ≠ 0 := fun he => hw0 (Subtype.ext he)
    have hc : c ≠ 0 := by intro he; exact hwv (by simpa [he] using hw.symm)
    let f : {x : fixedField P // c * σ x.val = x.val} →
        FixedBy.subfield (fixedField P) (coefficientFixedField P σ) := fun x =>
      ⟨x.val / w, by
        apply Subtype.ext
        change σ (x.val.val / w.val) = x.val.val / w.val
        rw [map_div₀]
        calc
          σ x.val.val / σ w.val = (c * σ x.val.val) / (c * σ w.val) :=
            (mul_div_mul_left _ _ hc).symm
          _ = x.val.val / w.val := by rw [x.property,hw]⟩
    apply Nat.card_le_card_of_injective f
    intro x y he
    apply Subtype.ext
    exact (div_left_inj' hw0).mp (congrArg Subtype.val he)
  · push Not at h
    apply Nat.card_le_card_of_injective (fun _ : {x : fixedField P // c * σ x.val = x.val} =>
      (0 : FixedBy.subfield (fixedField P) (coefficientFixedField P σ)))
    intro x y _
    exact Subtype.ext ((h x x.property).trans (h y y.property).symm)

private theorem mixed_fixed_card (P : Parameters) (σ : CoefficientAut P)
    (hσ : orderOf σ = 2) (c d : Fin 3 → ExtensionField P) :
    Nat.card (((i : Fin 3) → {x : ExtensionField P // c i * σ x = x}) ×
      ((i : Fin 3) → {x : fixedField P // d i * σ x.val = x.val})) ≤ P.q^6 := by
  let a := Nat.card (FixedBy.subfield (ExtensionField P) σ)
  let b := Nat.card (FixedBy.subfield (fixedField P) (coefficientFixedField P σ))
  have ha : a^2=P.q^3 := (FiniteField.card_involution_fixed_sq σ
    (fun x => DFunLike.congr_fun (show σ^2=1 from (orderOf_eq_prime_iff.mp hσ).1) x)
    (orderOf_eq_prime_iff.mp hσ).2).trans (card_extensionField P)
  have hb : b^2=P.q := fixed_base_card P σ hσ
  have hab : a^3*b^3=P.q^6 := by
    have he : (a^3*b^3)^2=(P.q^6)^2 := by
      calc
        (a^3*b^3)^2 = (a^2)^3*(b^2)^3 := by ring
        _ = (P.q^3)^3*P.q^3 := by rw [ha,hb]
        _ = (P.q^6)^2 := by ring
    exact Nat.pow_left_injective (by decide : (2:ℕ) ≠ 0) he
  rw [Nat.card_prod,Nat.card_pi,Nat.card_pi]
  calc
    _ ≤ (∏ _i : Fin 3, a) * (∏ _i : Fin 3, b) := Nat.mul_le_mul
      (Finset.prod_le_prod' (fun i _ => FiniteField.card_scalar_fixed_le σ (c i)))
      (Finset.prod_le_prod' (fun i _ => scalar_base_fixed_le P σ (d i)))
    _ = P.q^6 := by simpa using hab

private theorem map_conjugate {G K : Type*} [Group G] [Group K]
    (f : G →* K) (g x : G) : f (g*x*g⁻¹)=f g*f x*(f g)⁻¹ := by
  rw [map_mul,map_mul,map_inv]

private theorem conjugation_congr {G : Type*} [Group G]
    {g h x y : G} (hg : g=h) (hx : x=y) : g*x*g⁻¹=h*y*h⁻¹ := by
  rw [hg,hx]

private theorem torus_coefficient_coordinates (P : Parameters) (hp : P.prime=2)
    (a : TorusCoordinates.OrbitParameters P) (σ : CoefficientAut P)
    (x : Carrier P) (v : OrbitParameters P)
    (hv : FixedDescent.carrierToSplit P hp x = orderedProduct P (expand P v))
    (hx : (TorusCoordinates.torusMulEquiv P hp a).val * coefficientAction P σ x *
      (TorusCoordinates.torusMulEquiv P hp a).val⁻¹ = x) :
    ∀ i : Fin 12, TrialityOuterTorus.rootWeight P (TorusCoordinates.expand P a) i *
      σ (expand P v i) = expand P v i := by
  have hg : FixedDescent.carrierToSplit P hp (TorusCoordinates.torusMulEquiv P hp a).val =
      TorusCoordinates.product P (TorusCoordinates.expand P a) := by
    rw [TorusCoordinates.torusMulEquiv_val,FixedDescent.carrierToSplit_toCarrier]
    exact TorusCoordinates.inclusion_orbitElementary P hp a
  have hcx := (carrierToSplit_coefficient P hp σ x).trans
    ((congrArg (coefficientSplit P σ) hv).trans (coefficientSplit_orderedProduct P σ (expand P v)))
  have hc := (map_conjugate (FixedDescent.carrierToSplit P hp)
    (TorusCoordinates.torusMulEquiv P hp a).val (coefficientAction P σ x)).trans
      (conjugation_congr hg hcx)
  have he := (TrialityOuterTorus.product_orderedProduct P hp (TorusCoordinates.expand P a)
    (fun i => σ (expand P v i))).symm.trans
      (hc.symm.trans ((congrArg (FixedDescent.carrierToSplit P hp) hx).trans hv))
  intro i
  exact congrFun (orderedProduct_injective P he) i

/-- A torus twist of a nontrivial cubic-field involution fixes at most q^6
points of the genuine positive subgroup, with all six folded roots retained. -/
theorem torus_coefficient_fixed_card (m : ℕ) (hm : 0<m)
    (g : torus (binaryParameters m hm))
    (σ : CoefficientAut (binaryParameters m hm)) (hσ : orderOf σ=2) :
    Nat.card (unipotent (binaryParameters m hm) ⊓
      (MulAut.conj g.val * coefficientAction (binaryParameters m hm) σ).fixedSubgroup :
        Subgroup (Carrier (binaryParameters m hm))) ≤ (binaryParameters m hm).q^6 := by
  let P := binaryParameters m hm
  have hp : P.prime=2 := rfl
  obtain ⟨a,rfl⟩ := (TorusCoordinates.torusMulEquiv P hp).surjective g
  let w := TrialityOuterTorus.rootWeight P (TorusCoordinates.expand P a)
  let Q := unipotent P ⊓
    (MulAut.conj (TorusCoordinates.torusMulEquiv P hp a).val * coefficientAction P σ).fixedSubgroup
  let v (x : Q) := (positiveEquiv m hm).symm ⟨x.val,x.property.1⟩
  have hv (x : Q) : FixedDescent.carrierToSplit P hp x.val = orderedProduct P (expand P (v x)) := by
    rw [←baseProduct_toSplit]
    apply congrArg (FixedDescent.carrierToSplit P hp)
    exact (congrArg Subtype.val ((positiveEquiv m hm).apply_symm_apply
      ⟨x.val,x.property.1⟩)).symm.trans (positiveEquiv_val m hm (v x))
  have hcoord (x : Q) := torus_coefficient_coordinates P hp a σ x.val (v x) (hv x)
    ((MulAut.mem_fixedSubgroup _ x.val).mp x.property.2)
  let s : Fin 3 → Fin 12 := ![0,4,7]
  let l : Fin 3 → Fin 12 := ![3,10,11]
  let f : Q → (((i : Fin 3) → {x : ExtensionField P // w (s i) * σ x=x}) ×
      ((i : Fin 3) → {x : fixedField P // w (l i) * σ x.val=x.val})) := fun x =>
    (fun i => ⟨(v x).1 i,by have hh := hcoord x (s i); fin_cases i <;> exact hh⟩,
     fun i => ⟨(v x).2 i,by have hh := hcoord x (l i); fin_cases i <;> exact hh⟩)
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    have he' : v x=v y := by
      apply Prod.ext
      · funext i; exact congrArg Subtype.val (congrFun (congrArg Prod.fst he) i)
      · funext i; exact congrArg Subtype.val (congrFun (congrArg Prod.snd he) i)
    exact congrArg (fun z : unipotent P => z.val) ((positiveEquiv m hm).symm.injective he')
  exact (Nat.card_le_card_of_injective f hf).trans (mixed_fixed_card P σ hσ (w ∘ s) (w ∘ l))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityOuterFixed


namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityOuterFixed
variable {G : Type*} [Group G]

private theorem centralizer_bound_transport
    (m : ℕ) (hm : 0<m)
    (f : parabolic (binaryParameters m hm) .arms →* G) (hf : Function.Injective f)
    (S : Subgroup G)
    (hS : ((unipotent (binaryParameters m hm)).subgroupOf
      (parabolic (binaryParameters m hm) .arms)).map f=S)
    (t : G) (g : torus (binaryParameters m hm))
    (σ : CoefficientAut (binaryParameters m hm)) (hσ : orderOf σ=2)
    (hact : let P := binaryParameters m hm
      let gP : parabolic P .arms := inclusion ((torus_le_borel P).trans (borel_le_parabolic P .arms)) g
      ∀ x : parabolic P .arms, x.val ∈ unipotent P →
        t * f x * t⁻¹ = f (gP * coefficientParabolic P σ .arms x * gP⁻¹)) :
    Nat.card (S ⊓ centralizer ({t} : Set G) : Subgroup G) ≤ (binaryParameters m hm).q^6 := by
  let P := binaryParameters m hm
  have hUP : unipotent P ≤ parabolic P .arms := (unipotent_le_borel P).trans (borel_le_parabolic P .arms)
  let eU : unipotent P ≃* S := ((subgroupOfEquivOfLe hUP).symm.trans
    (equivMapOfInjective ((unipotent P).subgroupOf (parabolic P .arms)) f hf)).trans
      (MulEquiv.subgroupCongr hS)
  let a := MulAut.conj g.val * coefficientAction P σ
  let j : (S ⊓ centralizer ({t} : Set G) : Subgroup G) →
      (unipotent P ⊓ a.fixedSubgroup : Subgroup (Carrier P)) := fun x =>
    let y := eU.symm ⟨x.val,x.property.1⟩
    ⟨y.val,y.property,by
      apply (MulAut.mem_fixedSubgroup a y.val).mpr
      have hy : f ⟨y.val,hUP y.property⟩=x.val := congrArg Subtype.val
        (eU.apply_symm_apply ⟨x.val,x.property.1⟩)
      have hh := hact ⟨y.val,hUP y.property⟩ y.property
      rw [hy,←mem_centralizer_singleton_iff.mp x.property.2,mul_inv_cancel_right] at hh
      rw [←hy] at hh
      exact (congrArg Subtype.val (hf hh)).symm⟩
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    have he' : eU.symm ⟨x.val,x.property.1⟩ = eU.symm ⟨y.val,y.property.1⟩ :=
      Subtype.ext (congrArg (fun z : (unipotent P ⊓ a.fixedSubgroup : Subgroup (Carrier P)) => z.val) he)
    exact congrArg (fun z : S => z.val) (eU.symm.injective he')
  exact (Nat.card_le_card_of_injective j hj).trans (torus_coefficient_fixed_card m hm g σ hσ)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityOuterFixed

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The genuine torus--coefficient root action gives the source q^6 bound and
a strict q^7 bound after restoring the original Sylow extension factor.
The displayed identity is on the same right parabolic map; its construction
from the compatible local automorphisms remains a source obligation. -/
theorem Preparation.triality_outer_centralizer_lt_of_torus_coefficient_action
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ torus (binaryParameters m hm))
    (t : T) (htD : t.val ∈ normalizer (D : Set G))
    (g : torus (binaryParameters m hm))
    (σ : CoefficientAut (binaryParameters m hm)) (hσ : orderOf σ=2)
    (hact : let P := binaryParameters m hm
      let gP : parabolic P .arms := inclusion ((torus_le_borel P).trans (borel_le_parabolic P .arms)) g
      ∀ x : parabolic P .arms, x.val ∈ unipotent P →
        t.val * (e.right.symm x).val * t.val⁻¹ =
          (e.right.symm (gP * coefficientParabolic P σ .arms x * gP⁻¹)).val) :
    Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤ (binaryParameters m hm).q^6 ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) < (binaryParameters m hm).q^7 := by
  let P := binaryParameters m hm
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := Y.subtype_injective.comp e.right.symm.injective
  have hS := d.triality_right_unipotent_image h hTH P rfl e
  have hb := TrialityOuterFixed.centralizer_bound_transport m hm f hf _ hS t.val g σ hσ hact
  have hc := d.triality_outer_torus_centralizer h hTH hp m hm e hD hmark t htD
  have hi : (sourceS L H).relIndex (T : Subgroup G) < P.q := by
    rw [←hc.2.2.1]
    change _ < 2^m
    rw [d.triality_parameter_eq h hTH hp m hm e]
    exact hc.2.2.2.2.1
  refine ⟨hb,?_⟩
  calc
    _ = Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) *
        (sourceS L H).relIndex (T : Subgroup G) := hc.2.2.2.2.2
    _ ≤ P.q^6 * (sourceS L H).relIndex (T : Subgroup G) := Nat.mul_le_mul_right _ hb
    _ < P.q^6 * P.q := Nat.mul_lt_mul_of_pos_left hi (pow_pos (by have := P.q_ge_two; omega) _)
    _ = P.q^7 := (pow_succ _ 6).symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

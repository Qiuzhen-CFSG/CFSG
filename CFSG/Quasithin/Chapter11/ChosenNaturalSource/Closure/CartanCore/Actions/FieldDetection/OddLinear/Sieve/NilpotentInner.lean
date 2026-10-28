module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.NilpotentFive
public import Theory.SpecificGroups.Alternating.FiveCoverInnerActors
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv

/-!
# All induced actors on the remaining Fitting quotient are inner

The actual primary Frattini action has exactly the Fitting subgroup as
kernel. It therefore embeds the Fitting quotient in the automorphism
group of the primary plane and supplies an element of order five there.
The two-dimensional trace restriction rules out squaring this element
under every automorphism of the original component image.

The Fitting quotient is a perfect double cover of A₅. The inner-actor
criterion then shows that every induced automorphism of this quotient
is inner, including induced two-group actors. The final theorem applies
this to the original moved-component sieve, with no additional action
premise. Both extraspecial factors and every homocyclic exponent remain.

The ambient Sylow-normalizer lift and scalar exclusion are still required
for 11.5.6(3), owned by qt-d-1222-natural-closure-cartan. The parent
qt-d-1222-natural-closure retains the preceding geometry.
Source: Aschbacher--Smith A.3.6 and 11.5.6(3), pp.43--45,780--781.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

/-- A primary plane of characteristic greater than five forces innerness on the Fitting quotient. -/
theorem nilpotent_primary_quotient_actors_inner {B : Type*} [Group B] [Finite B]
    [Group.IsPerfect B] (hn : A36Nilpotent B) (hc : A36Common B)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hpF : p ∣ Nat.card (fittingSubgroup B)) :
    ∀ a : MulAut B, quotientAut (fittingSubgroup B) a ∈
      MulAut.innerSubgroup (B ⧸ fittingSubgroup B) := by
  let R := B ⧸ fittingSubgroup B
  let : IsQuasisimple R := hc.2.1
  let q := QuotientGroup.mk' (fittingSubgroup B)
  let r := FittingActions.coreFrattiniAction p B
  have hk : r.ker = fittingSubgroup B :=
    ((FittingActions.nilpotent_frattini_actions hn hc).2.2 p hpF).2.1
  let rQ := QuotientGroup.lift (fittingSubgroup B) r hk.ge
  have hrQ : Function.Injective rQ :=
    (QuotientGroup.injective_lift_iff _ r hk.ge).mpr hk.symm
  obtain ⟨g,hg,hng⟩ := nilpotent_primary_exists_five_not_squared hn hc hp5 hpF
  have hu : orderOf (q g) = 5 := (orderOf_injective rQ hrQ _).symm.trans hg
  obtain ⟨F,_,_,hF,⟨e₀⟩⟩ := hn.2.2.1
  let e : R ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hn.1).symm.trans e₀
  let eZ : (R ⧸ center R) ≃* Theory.PSL2.Group F :=
    QuotientGroup.congr _ _ e (by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact (centerCongr e ⟨w,hw⟩).property
      · intro hz
        exact ⟨e.symm z,(centerCongr e.symm ⟨z,hz⟩).property,e.apply_symm_apply z⟩)
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 5 := (ZMod.ringEquivOfPrime F (by decide : Nat.Prime 5)
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let eA := eZ.trans ((Atlas.fieldEquivPSL 2 eF).trans
    Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some)
  have hR : Nat.card R = 120 := by
    rw [Nat.card_congr e.toEquiv,Atlas.card_sl_two,hF]
    norm_num
  have hA : Nat.card (R ⧸ center R) = 60 := by
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hZ : Nat.card (center R) = 2 := by
    have hh := (center R).card_mul_index
    rw [Subgroup.index,hA,hR] at hh
    omega
  let H := (quotientAut (fittingSubgroup B)).range
  have hH : MulAut.innerSubgroup R ≤ H := by
    rintro a ⟨u,rfl⟩
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (fittingSubgroup B) u
    refine ⟨MulAut.conj x,?_⟩
    ext z
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (fittingSubgroup B) z
    rw [quotientAut_apply_mk]
    simp only [MulAut.conj_apply,map_mul,map_inv]
  have hno : ∀ a ∈ H, a (q g) ≠ (q g) ^ 2 := by
    rintro a ⟨b,rfl⟩ he
    apply hng b
    have he' := congrArg rQ he
    rw [quotientAut_apply_mk] at he'
    change r (b g) = rQ ((q g)^2) at he'
    rw [map_pow] at he'
    have hqeval : rQ (q g) = r g := QuotientGroup.lift_mk _ hk.ge g
    rw [hqeval] at he'
    exact he'
  have hinner := Theory.SpecificGroups.Alternating.FiveCoverInnerActors.inner_of_no_five_squaring
    eA hZ H hH (q g) hu hno
  exact fun a => hinner ⟨a,rfl⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.OddLinear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- Every actor induced on the original remaining Fitting quotient is inner. -/
theorem moved_component_fitting_quotient_actors_inner (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hthree : 1 ≤ primeRank 3 E.L₁)
    (hexception : E.L₁ < E.K → Even E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) :
    let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
    A36Nilpotent B ∧ A36Common B ∧ primeRank 3 B ≤ 1 ∧
      ∀ a : MulAut B, quotientAut (fittingSubgroup B) a ∈
        MulAut.innerSubgroup (B ⧸ fittingSubgroup B) := by
  obtain ⟨hn,hcommon,hrB,p,hpp,hp5,hpF,_⟩ :=
    E.moved_component_primary_five_not_squared hp hT hX c hcart hXR hCX hz hNG hthree hexception hI hmoved
  let : Fact p.Prime := ⟨hpp⟩
  let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
  let := pCore_isNilpotent (p := 2) (G := E.G₁)
  let : Group.IsPerfect B := ((E.component_in_point_normalizer hI).map_quotient _).perfect
  exact ⟨hn,hcommon,hrB,nilpotent_primary_quotient_actors_inner hn hcommon hp5 hpF⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry

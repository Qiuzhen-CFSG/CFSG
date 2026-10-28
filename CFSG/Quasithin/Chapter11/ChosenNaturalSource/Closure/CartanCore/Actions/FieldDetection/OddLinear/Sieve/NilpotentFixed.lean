module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.NilpotentSylow
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The fixed Sylow image in the remaining nilpotent component

The actual Cartan fixes the Sylow intersection modulo the component's
intrinsic two-core. Coprime decomposition of that intersection shows that
its pointwise Cartan centralizer has the same quotient image. The primary
Frattini action has odd Fitting kernel, so its restriction to a Sylow
two-subgroup is injective. Transport the quaternion subgroup of its action
image back through this restriction and the literal component quotient.

Thus every remaining moved component has a noncommutative fixed Sylow
image containing Q₈. The final application starts with the original
Geometry and the complete moved-component sieve; no Sylow alignment,
fixed-image or quaternion premise is added. Both extraspecial factors and
arbitrary homocyclic exponents remain available.

This is a necessary consequence of the surviving row, not an exclusion:
odd scalar automorphisms can fix a quaternion complement. The ambient
Cartan exclusion and source 11.5.6(3) assembly remain with
qt-d-1222-natural-closure-cartan. The parent qt-d-1222-natural-closure
retains discharge of the preceding marked geometry.
Source: Aschbacher--Smith A.3.6, pp.43--45, and 11.5.6(3), pp.780--781.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
open CFSG.Quasithin.Chapter1.Section02

/-- The primary action detects a quaternion subgroup of every actual Sylow two-subgroup. -/
theorem nilpotent_sylow_quaternion {Q : Type*} [Group Q] [Finite Q]
    [Group.IsPerfect Q] (hn : A36Nilpotent Q) (hc : A36Common Q)
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card (fittingSubgroup Q))
    (S : Sylow 2 Q) : ∃ f : QuaternionGroup 2 →* S, Function.Injective f := by
  let r := FittingActions.coreFrattiniAction p Q
  have hk : Nat.Coprime 2 (Nat.card r.ker) := by
    rw [((FittingActions.nilpotent_frattini_actions hn hc).2.2 p hd).2.1,hc.1]
    exact pPrimeCore_coprime_card
  let rS := r.comp (S : Subgroup Q).subtype
  have hi : Function.Injective rS :=
    injective_comp_subtype_of_coprime_ker r hk (S : Subgroup Q) S.isPGroup'
  let e : S ≃* rS.range := MulEquiv.ofBijective rS.rangeRestrict
    ⟨fun _ _ he => hi (congrArg Subtype.val he),rS.rangeRestrict_surjective⟩
  obtain ⟨j,hj⟩ := (((FittingActions.nilpotent_frattini_actions hn hc).2.2 p hd).2.2.2 S).2
  exact ⟨e.symm.toMonoidHom.comp j,e.symm.injective.comp hj⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.OddLinear
open CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- Coprime fixed-point lifting preserves the full image of the literal Sylow intersection. -/
theorem nilpotent_component_fixed_sylow_image (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hodd : Odd (Nat.card E.X)) (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hcop : Nat.Coprime (Nat.card E.X) (Nat.card E.Y))
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hn : A36Nilpotent
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))))
    (hc : A36Common
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁)))) :
    (((T : Subgroup G) ⊓ I ⊓ centralizer (E.X : Set G)).subgroupOf I).map
        (QuotientGroup.mk' (pCore 2 I)) =
      ((T : Subgroup G).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) := by
  let S := (T : Subgroup G) ⊓ I
  let q := QuotientGroup.mk' (pCore 2 I)
  have hS : IsPGroup 2 S := T.isPGroup'.to_le inf_le_left
  have hsolv : Group.IsSolvable S := by
    let := hS.isNilpotent
    infer_instance
  have hcopS : Nat.Coprime (Nat.card E.X) (Nat.card S) := by
    obtain ⟨n,hn⟩ := hS.exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr hodd).pow_right n
  have hcomm : ⁅S,E.X⁆ ≤ I.pCoreIn 2 :=
    E.nilpotent_component_sylow_commutator hp hT hX hodd hXR hcop hI hn hc
  have hdec := eq_commutator_sup_centralizer_of_solvable_coprime S E.X
    (E.cartan_normalizes_component_sylow hp hT hX hodd hXR hI) hsolv hcopS
  have hk : (⁅S,E.X⁆.subgroupOf I).map q = ⊥ := by
    apply bot_unique
    rintro _ ⟨i,hi,rfl⟩
    apply mem_bot.mpr
    obtain ⟨j,hj,he⟩ := hcomm hi
    have he' : j = i := Subtype.ext he
    subst j
    exact (QuotientGroup.eq_one_iff i).mpr hj
  have he := congrArg (fun A : Subgroup G => (A.subgroupOf I).map q) hdec
  rw [subgroupOf_sup (hcomm.trans (pCoreIn_le 2 I))
    (inf_le_left.trans inf_le_right),Subgroup.map_sup,hk,bot_sup_eq] at he
  have hSI : S.subgroupOf I = (T : Subgroup G).subgroupOf I := by
    ext i
    exact ⟨fun hi => hi.1,fun hi => ⟨hi,i.property⟩⟩
  simpa only [hSI] using he.symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.OddLinear
open CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- The Cartan-fixed Sylow image contains a quaternion subgroup on the original quotient. -/
theorem nilpotent_component_fixed_sylow_quaternion (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hodd : Odd (Nat.card E.X)) (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hcop : Nat.Coprime (Nat.card E.X) (Nat.card E.Y))
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hn : A36Nilpotent
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))))
    (hc : A36Common
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))))
    {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))))) :
    ∃ f : QuaternionGroup 2 →*
      ((((T : Subgroup G) ⊓ I ⊓ centralizer (E.X : Set G)).subgroupOf I).map
        (QuotientGroup.mk' (pCore 2 I))), Function.Injective f := by
  let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
  let e := E.componentImageQuotientEquiv hI
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  let C := (((T : Subgroup G) ⊓ I ⊓ centralizer (E.X : Set G)).subgroupOf I).map
    (QuotientGroup.mk' (pCore 2 I))
  let := pCore_isNilpotent (p := 2) (G := E.G₁)
  let : Group.IsPerfect B := ((E.component_in_point_normalizer hI).map_quotient _).perfect
  obtain ⟨S,hS⟩ := E.exists_component_sylow_intersection hT hI
  let P : Sylow 2 B := S.mapSurjective
    (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 I)))
  have he : C.map e.toMonoidHom = (P : Subgroup B) := by
    change C.map e.toMonoidHom = (S : Subgroup I).map f
    rw [hS]
    dsimp only [C]
    rw [E.nilpotent_component_fixed_sylow_image hp hT hX hodd hXR hcop hI hn hc,
      map_map]
  let eC : C ≃* P := (C.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr he)
  obtain ⟨j,hj⟩ := nilpotent_sylow_quaternion hn hc hd P
  exact ⟨eC.symm.toMonoidHom.comp j,eC.symm.injective.comp hj⟩

/-- Apply the full component sieve: a moved component has a noncommutative fixed Sylow image. -/
theorem moved_component_fixed_sylow_obstruction (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hr : primeRank 3 E.Y ≤ 1) (hodd : Odd E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) :
    let C := (((T : Subgroup G) ⊓ I ⊓ centralizer (E.X : Set G)).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I))
    C = ((T : Subgroup G).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ∧
      ∃ f : QuaternionGroup 2 →* C, Function.Injective f ∧ ¬ IsMulCommutative C := by
  obtain ⟨hn,hc,_,_,_,_,_,p,hprime,_,hd,_⟩ :=
    E.moved_component_primary_scalar_case hp hT hX c hcart hXR hCX hz hNG hr hodd hI hmoved
  let : Fact p.Prime := ⟨hprime⟩
  have hcop := E.cartan_coprime_of_local_action hp hX hcart.odd
    (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
  have hXY := E.cartan_coprime_Y_of_split_marking (c.cartanTorusEquiv hcart) hcop
  obtain ⟨f,hf⟩ := E.nilpotent_component_fixed_sylow_quaternion hp hT hX hcart.odd
    hXR hXY hI hn hc hd
  refine ⟨E.nilpotent_component_fixed_sylow_image hp hT hX hcart.odd hXR hXY hI hn hc,
    f,hf,?_⟩
  intro hC
  have h := hf (show
    f ((QuaternionGroup.a 1 : QuaternionGroup 2) * .xa 0) =
      f ((QuaternionGroup.xa 0 : QuaternionGroup 2) * .a 1) by
    rw [map_mul,map_mul]
    exact hC.is_comm.comm _ _)
  exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) * .xa 0 ≠ .xa 0 * .a 1) h

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry

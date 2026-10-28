module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction.Coordinates

/-!
# The complete image of a marked original action

The component supplies one whole base factor. Conjugating by the specified
exchanger supplies the other. Its base coordinates need not vanish: conjugation
on the second factor is corrected by the corresponding inner automorphism.
Thus the orbit image is the entire base and the Sylow join image is the entire
wreath product. No order-two lift of the exchange is assumed.

Source: Aschbacher--Smith 10.1.1(3) and 10.2.4, pp.741,747.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction
open Chapter3.Section02 Geometry.Escape

def other : Bit := Multiplicative.ofAdd 1

theorem bit_cases (i : Bit) : i = 1 ∨ i = other := by
  revert i
  decide

@[simp] theorem other_ne_one : other ≠ 1 := by decide
@[simp] theorem other_inv : other⁻¹ = other := by decide
@[simp] theorem other_mul_self : other * other = 1 := by decide

def secondBase : Matrix.PSL3Two.SL →* Actor where
  toFun a := ⟨fun i => if i = 1 then 1 else a, 1⟩
  map_one' := by ext i <;> simp
  map_mul' a b := by
    ext i
    · by_cases hi : i = 1 <;> simp [hi]
    · simp

def base : (Bit → Matrix.PSL3Two.SL) →* Actor where
  toFun a := ⟨a,1⟩
  map_one' := rfl
  map_mul' a b := by ext i <;> simp

theorem base_injective : Function.Injective base :=
  fun _ _ h => congrArg RegularWreathProduct.left h

theorem base_eq_first_mul_second (a : Bit → Matrix.PSL3Two.SL) :
    base a = firstBase (a 1) * secondBase (a other) := by
  ext i
  · rcases bit_cases i with rfl | rfl <;> simp [base,firstBase,secondBase]
  · rfl

theorem conjugate_first (x : Actor) (hx : x.right = other) (a : Matrix.PSL3Two.SL) :
    x * firstBase a * x⁻¹ = secondBase (x.left other * a * (x.left other)⁻¹) := by
  ext i
  · rcases bit_cases i with rfl | rfl <;>
      simp [RegularWreathProduct.mul_left, RegularWreathProduct.inv_left,
        firstBase, secondBase, hx]
  · simp [firstBase, secondBase]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}
  {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

def exchanger (s : SourceLinearThreeSurvivor T D) : localJoin T L :=
  ⟨s.exchange, (show (T : Subgroup G) ≤ localJoin T L from le_sup_right) s.exchange_mem⟩

/-- The exchanger has nontrivial permutation coordinate in every marked lift. -/
theorem LiftData.exchanger_right (f : LiftData s hz) :
    (f.hom (exchanger s)).right = other := by
  rcases bit_cases (f.hom (exchanger s)).right with h | h
  · exfalso
    obtain ⟨w,hw⟩ := exists_ne (1 : Eight)
    obtain ⟨a,ha⟩ := s.natural.onto w
    let b : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) :=
      (MulAut.conj s.exchange).subgroupMap ⁅D.fullModule,L⁆ a
    let v := factorProduct s hz (a,1)
    have he : joinAction D (exchanger s) v = factorProduct s hz (1,b) := by
      apply Subtype.ext
      rw [joinAction_apply]
      change s.exchange * (factorProduct s hz (a,1) : G) * s.exchange⁻¹ =
        (factorProduct s hz (1,b) : G)
      rw [factorProduct_apply s hz a 1, factorProduct_apply s hz 1 b]
      change s.exchange * ((a : G) * 1) * s.exchange⁻¹ =
        1 * (s.exchange * (a : G) * s.exchange⁻¹)
      simp only [mul_one,one_mul]
    have hc (x : (⁅D.fullModule,L⁆ : Subgroup G))
        (y : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)) :
        fullCoordinates s hz (factorProduct s hz (x,y)) other = partnerCoordinates s hz y := by
      have hh := fullCoordinates_mul s hz x y other
      have hv : (⟨(x : G) * y, D.fullModule.mul_mem (survivor_moved_le s x.property)
          (survivor_partner_le s y.property)⟩ : D.fullModule) = factorProduct s hz (x,y) :=
        Subtype.ext (factorProduct_apply s hz x y).symm
      simpa only [hv,other_ne_one,if_false] using hh
    have eqn := congrFun (f.equivariant (exchanger s) v) other
    rw [he, hc, show partnerCoordinates s hz b = s.natural.coordinates a from
      partnerCoordinates_conj s hz a, ha, action_apply, h] at eqn
    simp only [inv_one, one_mul] at eqn
    change w = Multiplicative.ofAdd
      (Matrix.mulVec ((f.hom (exchanger s)).left other).val
        (fullCoordinates s hz (factorProduct s hz (a,1)) other).toAdd) at eqn
    rw [hc, map_one] at eqn
    change w = Multiplicative.ofAdd (Matrix.mulVec ((f.hom (exchanger s)).left other).val 0) at eqn
    rw [Matrix.mulVec_zero] at eqn
    exact hw eqn
  · exact h

theorem LiftData.first_mem_orbit_image (f : LiftData s hz) (a : Matrix.PSL3Two.SL) :
    firstBase a ∈ ((localOrbit T L).subgroupOf (localJoin T L)).map f.hom := by
  obtain ⟨l,rfl⟩ := componentHom_surjective s a
  exact ⟨componentInclusion l,le_componentOrbit L T l.property,LiftData.component s hz f l⟩

theorem LiftData.second_mem_orbit_image (f : LiftData s hz) (a : Matrix.PSL3Two.SL) :
    secondBase a ∈ ((localOrbit T L).subgroupOf (localJoin T L)).map f.hom := by
  let x := f.hom (exchanger s)
  obtain ⟨l,hl⟩ := componentHom_surjective s ((x.left other)⁻¹ * a * x.left other)
  refine ⟨exchanger s * componentInclusion l * (exchanger s)⁻¹,?_,?_⟩
  · exact (mem_normalizer_iff.mp (le_normalizer_componentOrbit L T s.exchange_mem)
      l).mp (le_componentOrbit L T l.property)
  · rw [map_mul, map_mul, map_inv, f.component, hl,
      conjugate_first _ f.exchanger_right]
    congr 1
    dsimp only [x]
    group

/-- The image of the literal component orbit is exactly the complete base. -/
theorem LiftData.orbit_image (f : LiftData s hz) :
    ((localOrbit T L).subgroupOf (localJoin T L)).map f.hom = base.range := by
  apply le_antisymm
  · have hR : localOrbit T L = L ⊔ L.map (MulAut.conj s.exchange).toMonoidHom :=
      orbit_eq_pair s
    have hL : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
    have hB : L.map (MulAut.conj s.exchange).toMonoidHom ≤ localJoin T L :=
      (le_sup_right.trans_eq hR.symm).trans le_sup_left
    rw [hR, subgroupOf_sup hL hB, Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨l,hl,rfl⟩
      have he : l = componentInclusion (⟨l,hl⟩ : L) := rfl
      rw [he,f.component]
      exact ⟨_,rfl⟩
    · rintro _ ⟨b,⟨l,hl,he⟩,rfl⟩
      have hb : b = exchanger s * componentInclusion (⟨l,hl⟩ : L) * (exchanger s)⁻¹ :=
        Subtype.ext he.symm
      rw [hb,map_mul,map_mul,map_inv,f.component,conjugate_first _ f.exchanger_right]
      exact ⟨_,rfl⟩
  · rintro _ ⟨a,rfl⟩
    rw [base_eq_first_mul_second]
    exact mul_mem (f.first_mem_orbit_image _) (f.second_mem_orbit_image _)

/-- The base and the nontrivial permutation coset give the whole wreath image. -/
theorem LiftData.surjective (f : LiftData s hz) : Function.Surjective f.hom := by
  have hb : ∀ a, base a ∈ f.hom.range := by
    intro a
    have ha : base a ∈ ((localOrbit T L).subgroupOf (localJoin T L)).map f.hom := by
      rw [f.orbit_image]
      exact ⟨a,rfl⟩
    exact map_le_range _ _ ha
  intro y
  change y ∈ f.hom.range
  rcases bit_cases y.right with hy | hy
  · have he : y = base y.left := RegularWreathProduct.ext rfl hy
    rw [he]
    exact hb _
  · let x := f.hom (exchanger s)
    have hr : (y * x⁻¹).right = 1 := by
      simp [x, hy, f.exchanger_right]
    have he : y * x⁻¹ = base (y * x⁻¹).left := RegularWreathProduct.ext rfl hr
    have hh := f.hom.range.mul_mem (he.symm ▸ hb (y * x⁻¹).left)
      (show x ∈ f.hom.range from ⟨exchanger s,rfl⟩)
    simpa only [inv_mul_cancel_right] using hh

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction

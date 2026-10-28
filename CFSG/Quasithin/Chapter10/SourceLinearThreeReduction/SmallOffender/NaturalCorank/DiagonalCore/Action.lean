module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.DiagonalCore.Coordinates
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag.Model
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.LinearThree.Placement
public import Theory.GroupTheory.PCoreActionCardKernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.PointModel.Geometry
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.SpecificGroups.SymmetricFourWreath.ResidualQuotient
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Preparation

/-!
# The full natural action before the numerical conclusions

The two component factors give the whole base of the natural wreath action;
the Sylow exchanger supplies the remaining coset. Comparing the base order
with the original orbit quotient proves that the action kernel is a two-group.
Equivariance identifies the diagonal centralizer with the preimage of the
actual point stabilizer, giving its intrinsic S3-wreath two-core quotient.

The proofs adapt the indicated original-action modules under
`SourceLinearThreeReplacement/`, using only the earlier natural pair.
Source: Aschbacher--Smith 10.1.1(3), 10.2.4 and 10.2.11, pp.741,747,753.
-/

public noncomputable section
-- Adapted from Overgroups/Closure/Parabolic/Natural/OriginalAction/Image.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural.OriginalAction
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
open Chapter3.Section02 Geometry.Escape

@[expose] def other : Bit := Multiplicative.ofAdd 1

theorem bit_cases (i : Bit) : i = 1 ∨ i = other := by
  revert i
  decide

@[simp] theorem other_ne_one : other ≠ 1 := by decide
@[simp] theorem other_inv : other⁻¹ = other := by decide
@[simp] theorem other_mul_self : other * other = 1 := by decide

@[expose] def secondBase : Matrix.PSL3Two.SL →* Actor where
  toFun a := ⟨fun i => if i = 1 then 1 else a, 1⟩
  map_one' := by ext i <;> simp
  map_mul' a b := by
    ext i
    · by_cases hi : i = 1 <;> simp [hi]
    · simp

@[expose] def base : (Bit → Matrix.PSL3Two.SL) →* Actor where
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
  {s : SourceLinearThreePair T D}
  {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

@[expose] def exchanger (s : SourceLinearThreePair T D) : localJoin T L :=
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
      have hv : (⟨(x : G) * y, D.fullModule.mul_mem (pair_moved_le s x.property)
          (pair_partner_le s y.property)⟩ : D.fullModule) = factorProduct s hz (x,y) :=
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

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural.OriginalAction

-- Adapted from Overgroups/Closure/Parabolic/Natural/OriginalAction/Realization.lean.
open Subgroup Theory.GroupTheory
open scoped Matrix IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural.OriginalAction
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
open Chapter3.Section02 Geometry.Escape

private theorem matrix_realization (a : MulAut Eight) :
    ∃ m : Matrix.PSL3Two.SL, ∀ v : Eight,
      Multiplicative.ofAdd (m.val *ᵥ v.toAdd) = a v := by
  obtain ⟨m,rfl⟩ := Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut.surjective a
  refine ⟨m,fun v => ?_⟩
  exact (congrArg Multiplicative.ofAdd
    (Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut_apply m v)).symm

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreePair T D)
  (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)

private theorem preserving_realization (g : localJoin T L)
    (ha : (⁅D.fullModule,L⁆).map (MulAut.conj (g : G)).toMonoidHom = ⁅D.fullModule,L⁆)
    (hb : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
      (MulAut.conj (g : G)).toMonoidHom =
        (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) :
    ∃ w : Actor, ∀ v : D.fullModule,
      fullCoordinates s hz (joinAction D g v) = action w (fullCoordinates s hz v) := by
  let ca := movedCoordinates s hz
  let cb := partnerCoordinates s hz
  let ea : (⁅D.fullModule,L⁆ : Subgroup G) ≃* _ :=
    ((MulAut.conj (g : G)).subgroupMap ⁅D.fullModule,L⁆).trans (MulEquiv.subgroupCongr ha)
  let eb : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) ≃* _ :=
    ((MulAut.conj (g : G)).subgroupMap
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)).trans (MulEquiv.subgroupCongr hb)
  obtain ⟨ma,hma⟩ := matrix_realization ((ca.symm.trans ea).trans ca)
  obtain ⟨mb,hmb⟩ := matrix_realization ((cb.symm.trans eb).trans cb)
  refine ⟨⟨fun i => if i = 1 then ma else mb, 1⟩,fun v => ?_⟩
  obtain ⟨⟨a,b⟩,rfl⟩ := (factorProduct s hz).surjective v
  have he : joinAction D g (factorProduct s hz (a,b)) =
      factorProduct s hz (ea a,eb b) := by
    apply Subtype.ext
    rw [joinAction_apply,factorProduct_apply,factorProduct_apply]
    change (g : G) * ((a : G) * b) * (g : G)⁻¹ =
      ((g : G) * a * (g : G)⁻¹) * ((g : G) * b * (g : G)⁻¹)
    group
  rw [he]
  funext i
  rw [coordinates_factorProduct,action_apply]
  simp only [inv_one,one_mul]
  rw [coordinates_factorProduct]
  by_cases hi : i = 1
  · simp only [hi,ite_true]
    have hh := hma (ca a)
    simp only [MulEquiv.trans_apply] at hh
    rw [ca.symm_apply_apply] at hh
    exact hh.symm
  · simp only [hi,if_false]
    have hh := hmb (cb b)
    simp only [MulEquiv.trans_apply] at hh
    rw [cb.symm_apply_apply] at hh
    exact hh.symm

private theorem exchanging_realization (g : localJoin T L)
    (ha : (⁅D.fullModule,L⁆).map (MulAut.conj (g : G)).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)
    (hb : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
      (MulAut.conj (g : G)).toMonoidHom = ⁅D.fullModule,L⁆) :
    ∃ w : Actor, ∀ v : D.fullModule,
      fullCoordinates s hz (joinAction D g v) = action w (fullCoordinates s hz v) := by
  let ca := movedCoordinates s hz
  let cb := partnerCoordinates s hz
  let ea : (⁅D.fullModule,L⁆ : Subgroup G) ≃* _ :=
    ((MulAut.conj (g : G)).subgroupMap ⁅D.fullModule,L⁆).trans (MulEquiv.subgroupCongr ha)
  let eb : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) ≃* _ :=
    ((MulAut.conj (g : G)).subgroupMap
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)).trans (MulEquiv.subgroupCongr hb)
  obtain ⟨ma,hma⟩ := matrix_realization ((cb.symm.trans eb).trans ca)
  obtain ⟨mb,hmb⟩ := matrix_realization ((ca.symm.trans ea).trans cb)
  refine ⟨⟨fun i => if i = 1 then ma else mb, other⟩,fun v => ?_⟩
  obtain ⟨⟨a,b⟩,rfl⟩ := (factorProduct s hz).surjective v
  let _ : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hcomm : (a : G) * b = (b : G) * a :=
    congrArg Subtype.val (mul_comm
      (⟨a,pair_moved_le s a.property⟩ : D.fullModule)
      ⟨b,pair_partner_le s b.property⟩)
  have he : joinAction D g (factorProduct s hz (a,b)) =
      factorProduct s hz (eb b,ea a) := by
    apply Subtype.ext
    rw [joinAction_apply,factorProduct_apply,factorProduct_apply]
    change (g : G) * ((a : G) * b) * (g : G)⁻¹ =
      ((g : G) * b * (g : G)⁻¹) * ((g : G) * a * (g : G)⁻¹)
    rw [hcomm]
    group
  rw [he]
  funext i
  rw [coordinates_factorProduct,action_apply]
  rcases bit_cases i with rfl | rfl
  · simp only [other_inv,mul_one,coordinates_factorProduct,other_ne_one,if_false,ite_true]
    have hh := hma (cb b)
    simp only [MulEquiv.trans_apply] at hh
    rw [cb.symm_apply_apply] at hh
    exact hh.symm
  · simp only [other_inv,other_mul_self,coordinates_factorProduct,other_ne_one,if_false,ite_true]
    have hh := hmb (ca a)
    simp only [MulEquiv.trans_apply] at hh
    rw [ca.symm_apply_apply] at hh
    exact hh.symm

theorem element_realization (g : localJoin T L) :
    ∃ w : Actor, ∀ v : D.fullModule,
      fullCoordinates s hz (joinAction D g v) = action w (fullCoordinates s hz v) := by
  have hgm : (g : G) ∈ D.maximalLocal :=
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) g.property
  have hne : ⁅D.fullModule,L⁆ ≠ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
    intro he
    have hd := (pair_pair_disjoint s hz).eq_bot
    rw [←he,inf_idem] at hd
    have hc := moved_card s hz
    rw [hd,card_bot] at hc
    contradiction
  rcases pair_moved_pair s g hgm with ha | ha <;>
    rcases Geometry.Escape.partner_pair s g hgm with hb | hb
  · exact (hne (map_injective (MulAut.conj (g : G)).injective (ha.trans hb.symm))).elim
  · exact preserving_realization s hz g ha hb
  · exact exchanging_realization s hz g ha hb
  · exact (hne (map_injective (MulAut.conj (g : G)).injective (ha.trans hb.symm))).elim

@[expose] def originalLift : LiftData s hz := by
  let w := fun g => Classical.choose (element_realization s hz g)
  have hw (g : localJoin T L) (v : D.fullModule) :
      fullCoordinates s hz (joinAction D g v) = action (w g) (fullCoordinates s hz v) :=
    Classical.choose_spec (element_realization s hz g) v
  refine ⟨{ toFun := w, map_one' := ?_, map_mul' := ?_ },hw⟩
  · apply action_injective
    apply MulEquiv.ext
    intro z
    obtain ⟨v,rfl⟩ := (fullCoordinates s hz).surjective z
    rw [←hw,map_one,map_one]
    rfl
  · intro g h
    apply action_injective
    rw [map_mul]
    apply MulEquiv.ext
    intro z
    obtain ⟨v,rfl⟩ := (fullCoordinates s hz).surjective z
    rw [←hw,map_mul]
    change fullCoordinates s hz (joinAction D g (joinAction D h v)) = _
    rw [hw,hw]
    rfl

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural.OriginalAction

-- Adapted from Overgroups/Closure/Parabolic/Natural/OriginalAction/Kernel.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural.OriginalAction
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D}
  {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- The prescribed original action has a two-group kernel. -/
theorem LiftData.kernel_two (f : LiftData s hz) : IsPGroup 2 f.hom.ker := by
  let J := localJoin T L
  let R := (localOrbit T L).subgroupOf J
  let : R.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  have hgen : R ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show localOrbit T L ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hq : IsPGroup 2 (J ⧸ R) :=
    isPGroup_quotient_of_sup_eq_top R ((T : Subgroup G).subgroupOf J)
      T.isPGroup'.comap_subtype hgen
  apply f.hom.isPGroup_ker_of_card_image_eq_core_quotient R hq
  obtain ⟨e⟩ := CentralHall.LinearThree.quotient_equiv D s.quotient (pair_nonnormal s)
  let c : R ≃* localOrbit T L := subgroupOfEquivOfLe le_sup_left
  let q := (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e
  rw [show R.map f.hom = base.range from f.orbit_image,
    Nat.card_congr (MonoidHom.ofInjective base_injective).toEquiv.symm,
    Nat.card_congr q.toEquiv, Nat.card_fun, Nat.card_prod]
  have hbit : Nat.card Bit = 2 := by
    change Nat.card (ZMod 2) = 2
    exact Nat.card_zmod 2
  rw [hbit,pow_two]

/-- A lift alone suffices: its full image and two-group kernel have been proved. -/
def LiftData.actionData (f : LiftData s hz) : ActionData s hz where
  hom := f.hom
  onto := f.surjective
  kernel_two := f.kernel_two
  equivariant := f.equivariant

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural.OriginalAction

-- Adapted from Overgroups/Closure/Parabolic/Natural/Source.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D}
  {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- The marked homomorphism has exactly the original conjugation kernel. -/
theorem ActionData.ker_eq (a : ActionData s hz) :
    a.hom.ker = (centralizer (D.fullModule : Set G)).subgroupOf (localJoin T L) := by
  rw [← joinAction_ker D]
  ext g
  change a.hom g = 1 ↔ joinAction D g = 1
  constructor
  · intro hg
    apply MulEquiv.ext
    intro v
    apply (fullCoordinates s hz).injective
    rw [a.equivariant, hg, map_one]
    rfl
  · intro hg
    apply action_injective
    apply MulEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := (fullCoordinates s hz).surjective w
    rw [map_one, ← a.equivariant, hg]
    rfl

/-- Equivariance identifies the actual ambient centralizer, including its kernel. -/
theorem ActionData.stabilizer_preimage (a : ActionData s hz) (z : D.fullModule) :
    (diagonalParabolic T L (z : G)).subgroupOf (localJoin T L) =
      (pointStabilizer (fullCoordinates s hz z)).comap a.hom := by
  ext g
  change ((g : G) ∈ localJoin T L ∧ (g : G) ∈ centralizer ({(z : G)} : Set G)) ↔
    action (a.hom g) (fullCoordinates s hz z) = fullCoordinates s hz z
  constructor
  · intro hg
    rw [← a.equivariant]
    apply congrArg (fullCoordinates s hz)
    apply Subtype.ext
    rw [joinAction_apply, mem_centralizer_singleton_iff.mp hg.2, mul_inv_cancel_right]
  · intro hg
    refine ⟨g.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have he : joinAction D g z = z :=
      (fullCoordinates s hz).injective ((a.equivariant g z).trans hg)
    have hv := congrArg Subtype.val he
    rw [joinAction_apply] at hv
    exact mul_inv_eq_iff_eq_mul.mp hv

/-- The intrinsic quotient of an S₄-wreath stabilizer is the required S₃ wreath. -/
def pointQuotientEquiv (v : Space)
    (e : pointStabilizer v ≃* RegularWreathProduct (Equiv.Perm (Fin 4)) Bit) :
    (pointStabilizer v ⧸ pCore 2 (pointStabilizer v)) ≃* ParabolicWreath :=
  (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (SymmetricFourWreath.quotientEquivActor.trans
      (RegularWreathProduct.congr (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)
        (MulEquiv.refl Bit)))

/-- Restriction and both subgroup identifications preserve the actual two-core quotient. -/
def ActionData.parabolicQuotientEquiv (a : ActionData s hz) (z : D.fullModule)
    (e : pointStabilizer (fullCoordinates s hz z) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 4)) Bit) :
    (diagonalParabolic T L (z : G) ⧸ pCore 2 (diagonalParabolic T L (z : G))) ≃*
      ParabolicWreath := by
  let S := pointStabilizer (fullCoordinates s hz z)
  let r := a.hom.subgroupComap S
  have hr : Function.Surjective r :=
    a.hom.subgroupComap_surjective_of_surjective S a.onto
  have hk : r.ker = a.hom.ker.subgroupOf (S.comap a.hom) := by
    ext x
    change (r x : S) = 1 ↔ a.hom x = 1
    exact Subtype.ext_iff
  have hp : IsPGroup 2 r.ker := by
    rw [hk]
    exact a.kernel_two.comap_subtype
  let c : diagonalParabolic T L (z : G) ≃* S.comap a.hom :=
    (subgroupOfEquivOfLe (diagonalParabolic_le_join (T := T) (L := L) (z : G))).symm.trans
      (MulEquiv.subgroupCongr (a.stabilizer_preimage z))
  exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
    ((r.pCoreQuotientEquiv hr hp).trans (pointQuotientEquiv _ e))

/-- The model maximality is relative to the original L₀T, as in10.2.4. -/
theorem ActionData.parabolic_isCoatom (a : ActionData s hz) (z : D.fullModule)
    (hmax : IsCoatom (pointStabilizer (fullCoordinates s hz z))) :
    IsCoatom ((diagonalParabolic T L (z : G)).subgroupOf (localJoin T L)) := by
  rw [a.stabilizer_preimage z]
  exact isCoatom_comap_of_surjective a.onto hmax


end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural

module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.Pair
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag.Model
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.LinearThree.Placement
public import Theory.GroupTheory.PCoreActionCardKernel

/-!
# The faithful wreath quotient before the half-Sylow normalizer bound

The original maximal local permutes the two disjoint moved factors. Every
binary three-space automorphism is an SL₃(2) matrix, so the actual conjugation
action lifts to SL₃(2) wr C₂. The original component and exchanger give its
whole image. Orbit quotient counting makes its kernel a two-group.

These proofs adapt Parabolic/Natural/OriginalAction to the earlier selected
module data. The consumer constructs the quotient directly in the zero-kernel
branch of 10.2.5; no survivor or point-centralizer premise remains.
Source: Aschbacher--Smith 10.1.1(3), 10.2.4--5, pp.741,747--748.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Matrix IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02
open SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The original conjugation action, restricted to L₀T. -/
def joinAction (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    localJoin T L →* MulAut D.fullModule :=
  D.fullModule.normalizerMonoidHom.comp (inclusion
    ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
      D.maximalLocal_normalizes_fullModule))

theorem joinAction_apply (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (g : localJoin T L) (v : D.fullModule) :
    (joinAction D g v : G) = (g : G) * v * (g : G)⁻¹ := rfl

theorem joinAction_ker (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    (joinAction D).ker = (centralizer (D.fullModule : Set G)).subgroupOf (localJoin T L) := by
  ext g
  change D.fullModule.normalizerMonoidHom (inclusion _ g) = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  rfl

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : NaturalData D)
  (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)

/-- Only a lift of the original action; neither its image nor its kernel is assumed. -/
structure LiftData where
  hom : localJoin T L →* Actor
  equivariant (g : localJoin T L) (v : D.fullModule) :
    fullCoordinates s hz (joinAction D g v) = action (hom g) (fullCoordinates s hz v)

/-- The inclusion of the original component in its Sylow join. -/
def componentInclusion : L →* localJoin T L :=
  inclusion ((le_componentOrbit L T).trans le_sup_left)

/-- The prescribed component quotient, without a new choice of model. -/
def componentHom : L →* Matrix.PSL3Two.SL :=
  s.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem componentHom_surjective : Function.Surjective (componentHom s) :=
  s.quotient.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The first base factor in the literal wreath convention. -/
def firstBase : Matrix.PSL3Two.SL →* Actor where
  toFun a := ⟨fun i => if i = 1 then a else 1, 1⟩
  map_one' := by ext i <;> simp
  map_mul' a b := by
    ext i
    · by_cases hi : i = 1 <;> simp [hi]
    · simp

theorem firstBase_action (a : Matrix.PSL3Two.SL) (v : Space) (i : Bit) :
    action (firstBase a) v i =
      if i = 1 then Multiplicative.ofAdd (a.val *ᵥ (v i).toAdd) else v i := by
  rw [action_apply]
  by_cases hi : i = 1 <;> simp [firstBase, hi]

theorem coordinates_factorProduct
    (a : (⁅D.fullModule,L⁆ : Subgroup G))
    (b : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)) (i : Bit) :
    fullCoordinates s hz (factorProduct s hz (a,b)) i =
      if i = 1 then s.natural.coordinates a else partnerCoordinates s hz b := by
  convert fullCoordinates_mul s hz a b i using 2
  exact Subtype.ext (factorProduct_apply s hz a b)

theorem component_equivariant (l : L) (v : D.fullModule) :
    fullCoordinates s hz (joinAction D (componentInclusion l) v) =
      action (firstBase (componentHom s l)) (fullCoordinates s hz v) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (factorProduct s hz).surjective v
  let a' : (⁅D.fullModule,L⁆ : Subgroup G) := ⟨(l : G) * a * (l : G)⁻¹,
    (mem_normalizer_iff.mp (s.natural.normalized l.property) a).mp a.property⟩
  have hb : (l : G) * b * (l : G)⁻¹ = b := by
    rw [s.crossed b.property l l.property, mul_inv_cancel_right]
  have he : joinAction D (componentInclusion l) (factorProduct s hz (a,b)) =
      factorProduct s hz (a',b) := by
    apply Subtype.ext
    rw [joinAction_apply, factorProduct_apply, factorProduct_apply]
    change (l : G) * ((a : G) * b) * (l : G)⁻¹ =
      ((l : G) * a * (l : G)⁻¹) * b
    calc
      _ = ((l : G) * a * (l : G)⁻¹) * ((l : G) * b * (l : G)⁻¹) := by group
      _ = _ := by rw [hb]
  have hc (x : (⁅D.fullModule,L⁆ : Subgroup G))
      (y : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)) (i : Bit) :
      fullCoordinates s hz (factorProduct s hz (x,y)) i =
        if i = 1 then s.natural.coordinates x else partnerCoordinates s hz y := by
    convert fullCoordinates_mul s hz x y i using 2
    exact Subtype.ext (factorProduct_apply s hz x y)
  rw [he]
  funext i
  rw [firstBase_action, hc, hc]
  by_cases hi : i = 1
  · simp only [hi]
    exact congrArg Multiplicative.ofAdd (s.natural.equivariant l a)
  · simp only [hi, if_false]

/-- Faithfulness forces every lift to have the prescribed first-component marking. -/
theorem LiftData.component (f : LiftData s hz) (l : L) :
    f.hom (componentInclusion l) = firstBase (componentHom s l) := by
  apply action_injective
  apply MulEquiv.ext
  intro w
  obtain ⟨v,rfl⟩ := (fullCoordinates s hz).surjective w
  exact (f.equivariant _ v).symm.trans (component_equivariant s hz l v)

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
  {s : NaturalData D}
  {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

def exchanger (s : NaturalData D) : localJoin T L :=
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
      have hv : (⟨(x : G) * y, D.fullModule.mul_mem (selected_moved_le s x.property)
          (selected_partner_le s y.property)⟩ : D.fullModule) = factorProduct s hz (x,y) :=
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

private theorem matrix_realization (a : MulAut Eight) :
    ∃ m : Matrix.PSL3Two.SL, ∀ v : Eight,
      Multiplicative.ofAdd (m.val *ᵥ v.toAdd) = a v := by
  obtain ⟨m,rfl⟩ := Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut.surjective a
  refine ⟨m,fun v => ?_⟩
  exact (congrArg Multiplicative.ofAdd
    (Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut_apply m v)).symm

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : NaturalData D)
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
    simpa only [ca, movedCoordinates_apply] using hh.symm
  · simp only [hi,if_false]
    have hh := hmb (cb b)
    simp only [MulEquiv.trans_apply] at hh
    rw [cb.symm_apply_apply] at hh
    simpa only [ca, movedCoordinates_apply] using hh.symm

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
      (⟨a,selected_moved_le s a.property⟩ : D.fullModule)
      ⟨b,selected_partner_le s b.property⟩)
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
    simpa only [ca, movedCoordinates_apply] using hh.symm
  · simp only [other_inv,other_mul_self,coordinates_factorProduct,other_ne_one,if_false,ite_true]
    have hh := hmb (ca a)
    simp only [MulEquiv.trans_apply] at hh
    rw [ca.symm_apply_apply] at hh
    simpa only [ca, movedCoordinates_apply] using hh.symm

theorem element_realization (g : localJoin T L) :
    ∃ w : Actor, ∀ v : D.fullModule,
      fullCoordinates s hz (joinAction D g v) = action w (fullCoordinates s hz v) := by
  have hgm : (g : G) ∈ D.maximalLocal :=
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) g.property
  have hne : ⁅D.fullModule,L⁆ ≠ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
    intro he
    have hd := (selected_pair_disjoint s hz).eq_bot
    rw [←he,inf_idem] at hd
    have hc := moved_card s hz
    rw [hd,card_bot] at hc
    contradiction
  rcases selected_moved_pair s g hgm with ha | ha <;>
    rcases partner_pair s g hgm with hb | hb
  · exact (hne (map_injective (MulAut.conj (g : G)).injective (ha.trans hb.symm))).elim
  · exact preserving_realization s hz g ha hb
  · exact exchanging_realization s hz g ha hb
  · exact (hne (map_injective (MulAut.conj (g : G)).injective (ha.trans hb.symm))).elim

def originalLift : LiftData s hz := by
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

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D}
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
  obtain ⟨e⟩ := CentralHall.LinearThree.quotient_equiv D s.quotient (selected_nonnormal s)
  let c : R ≃* localOrbit T L := subgroupOfEquivOfLe le_sup_left
  let q := (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e
  rw [show R.map f.hom = base.range from f.orbit_image,
    Nat.card_congr (MonoidHom.ofInjective base_injective).toEquiv.symm,
    Nat.card_congr q.toEquiv, Nat.card_fun, Nat.card_prod]
  have hbit : Nat.card Bit = 2 := by
    change Nat.card (ZMod 2) = 2
    exact Nat.card_zmod 2
  rw [hbit,pow_two]


/-- The literal zero-kernel source branch has the complete wreath action,
with the given exchanger and actual component marking preserved. -/
theorem exists_wreath_action
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmodel : Selection.BinaryThreeNatural D) (hzero : sourceMovedFixed D = ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    ∃ s : NaturalData D, s.exchange = t ∧
      ∃ f : LiftData s s.fixed_zero,
        Function.Surjective f.hom ∧ IsPGroup 2 f.hom.ker ∧
        ((localOrbit T L).subgroupOf (localJoin T L)).map f.hom = base.range ∧
        (f.hom ⟨t,(show (T : Subgroup G) ≤ localJoin T L from le_sup_right) ht⟩).right = other := by
  obtain ⟨s,he⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  refine ⟨s,he,f,f.surjective,f.kernel_two,f.orbit_image,?_⟩
  simpa only [exchanger,he] using f.exchanger_right

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction

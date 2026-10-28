module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.PlaneGeometryModel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.Moving
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport

/-!
# Crossing planes in the original marked symplectic action

The earlier point-local identifications are recorded as `PointCoordinates`:
a symplectic basis for the original flag, the point-radical action of R₁,
and lifts of the point Levi through the original L₁. Every action equation
uses the supplied natural marking and the literal projection from V.
These are preceding flag/local-model inputs, whose construction remains
with the earlier source owners; they contain no crossing-plane conclusion.

When C_V(L)=1, the projection is injective. A moving radical element can
therefore be aligned by an actual L₁ lift, and its computed fixed space
and full displacement image give the required centralizer sandwich.
For the reverse direction, pull [V,Vᵍ]=V₂ back by g⁻¹. If the resulting
actor fixes V₃, the root calculation forces V₂≤V₁. Otherwise align it
again; mutual normalization identifies its displacement with V₂. Mapping
this equality back gives precisely the Lᵍ-plane orbit required by the
original transporter rechoice. No comparison of plane orders is used.

Both existing terminal consumers are applied below. The initial closure
core bound and C_V(L)=1 remain explicit, as permitted by the terminal
contract. Final source assembly must supply the preceding point geometry
and the independent second-radical calculation.

Source: Aschbacher--Smith, 11.5.7, refs/quasithin.pdf, printed pp.783--784.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
open Subgroup
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open scoped commutatorElement

variable {G : Type*} [Group G] {V : Subgroup G}
variable {F : Type*} [Field F]

/-- An actual normalizer element has the specified action in the displayed coordinates. -/
def Realizes (π : V →* Multiplicative (Vector F))
    (a : normalizer (V : Set G)) (b : Sp F) : Prop :=
  ∀ x : V, (π (V.normalizerMonoidHom a x)).toAdd = b • (π x).toAdd

namespace Realizes
variable {π : V →* Multiplicative (Vector F)}
    {a b : normalizer (V : Set G)} {r s : Sp F}

theorem mul (ha : Realizes π a r) (hb : Realizes π b s) :
    Realizes π (a*b) (r*s) := by
  intro x
  rw [map_mul,MulAut.mul_apply,ha,hb,mul_smul]

theorem inv (ha : Realizes π a r) : Realizes π a⁻¹ r⁻¹ := by
  intro x
  have h := ha (V.normalizerMonoidHom a⁻¹ x)
  have he : V.normalizerMonoidHom a (V.normalizerMonoidHom a⁻¹ x) = x := by
    rw [map_inv, MulAut.apply_inv_self]
  rw [he] at h
  rw [h,inv_smul_smul]

theorem conj (ha : Realizes π a r) (hb : Realizes π b s) :
    Realizes π (a*b*a⁻¹) (r*s*r⁻¹) := (ha.mul hb).mul ha.inv

end Realizes

variable [Finite G] {T : Sylow 2 G} {L : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- R₁ acts on the original seed via the given Sylow action. -/
theorem radical_normalizes_seed : E.R₁ ≤ normalizer (V : Set G) :=
  (LocalGeometry.localRadical_le_sylow E.V₁).trans E.input.sylow_normalizes

/-- Coordinates are the actual marked quotient followed by a symplectic basis change. -/
def markedProjection (m : MarkedFlag E) (s : Sp E.input.field.Carrier) :
    V →* Multiplicative (Vector E.input.field.Carrier) :=
  ((toLinear s).toAddEquiv.toMultiplicative.toMonoidHom).comp
    (LocalGeometry.Coordinates.sp4 m.action).projection

theorem markedProjection_surjective (m : MarkedFlag E) (s : Sp E.input.field.Carrier) :
    Function.Surjective (markedProjection E m s) :=
  (toLinear s).toAddEquiv.toMultiplicative.surjective.comp
    (LocalGeometry.Coordinates.sp4 m.action).projection_surjective

theorem markedProjection_injective (m : MarkedFlag E) (s : Sp E.input.field.Carrier)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    Function.Injective (markedProjection E m s) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hx' : (LocalGeometry.Coordinates.sp4 m.action).projection x = 1 := by
    apply (toLinear s).toAddEquiv.toMultiplicative.injective
    change markedProjection E m s x = 1 at hx
    exact hx.trans (map_one (toLinear s).toAddEquiv.toMultiplicative).symm
  have hxC := (LocalGeometry.Coordinates.sp4 m.action).projection_eq_one_iff x |>.mp hx'
  have hh : (x : G) ∈ V ⊓ centralizer (L : Set G) := ⟨x.property,hxC⟩
  rw [hc] at hh
  exact Subtype.ext hh

/-- Earlier point-local geometry in one symplectic basis. The actor equations
use the original quotient marking and literal normalizer conjugation. No
crossing subgroup, displacement plane or transporter is included. -/
structure PointCoordinates (m : MarkedFlag E) where
  basis : Sp E.input.field.Carrier
  point : ∀ x : V, (x : G) ∈ E.V₁ ↔
    (markedProjection E m basis x).toAdd ∈ Theory.SpecificGroups.SymplecticFour.point _
  plane : ∀ x : V, (x : G) ∈ E.V₂ ↔
    (markedProjection E m basis x).toAdd ∈ Theory.SpecificGroups.SymplecticFour.plane _
  three : ∀ x : V, (x : G) ∈ E.V₃ ↔
    (markedProjection E m basis x).toAdd (.inr 0) = 0
  radical : ∀ a : E.R₁, ∃ u v z : E.input.field.Carrier,
    Realizes (markedProjection E m basis)
      ⟨a.val,radical_normalizes_seed E a.property⟩ (PlaneModel.radical u v z)
  levi : ∀ b : Matrix.SpecialLinearGroup (Fin 2) E.input.field.Carrier,
    ∃ l : E.L₁, Realizes (markedProjection E m basis)
      ⟨l.val,D.normalizes (E.L₁_le l.property)⟩ (PlaneModel.levi b)

namespace PointCoordinates
variable {E} {m : MarkedFlag E} (p : PointCoordinates E m)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
include p

/-- Fixing V₃ leaves only the root action, whose displacement lies in V₁. -/
theorem commutator_le_point (A : Subgroup G) (hA : A ≤ E.R₁)
    (hz : A ≤ centralizer (E.V₃ : Set G)) : ⁅V,A⁆ ≤ E.V₁ := by
  let π := markedProjection E m p.basis
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha x hx
  let aN : normalizer (V : Set G) := ⟨a,radical_normalizes_seed E (hA ha)⟩
  obtain ⟨u,v,z,hr⟩ := p.radical ⟨a,hA ha⟩
  have huv : u=0 ∧ v=0 := by
    apply PlaneModel.radical_central_of_fixes_three u v z
    intro w hw
    obtain ⟨y,hy⟩ := markedProjection_surjective E m p.basis (Multiplicative.ofAdd w)
    change π y = Multiplicative.ofAdd w at hy
    have hy3 : (y : G) ∈ E.V₃ := p.three y |>.mpr (by change (π y).toAdd (.inr 0)=0; rw [hy]; exact hw)
    have hyfix : V.normalizerMonoidHom aN y = y := by
      apply Subtype.ext
      change a*y.val*a⁻¹=y.val
      rw [←hz ha y.val hy3,mul_inv_cancel_right]
    have he := hr y
    rw [hyfix] at he
    change (π y).toAdd = PlaneModel.radical u v z • (π y).toAdd at he
    simpa only [hy,toAdd_ofAdd] using he.symm
  rcases huv with ⟨rfl,rfl⟩
  let y : V := V.normalizerMonoidHom aN ⟨x,hx⟩ * (⟨x,hx⟩ : V)⁻¹
  have hy : (y : G)=⁅a,x⁆ := rfl
  rw [←hy]
  apply (p.point y).mpr
  change (π y).toAdd ∈ _
  simp only [y,map_mul,map_inv,toAdd_mul,toAdd_inv]
  rw [hr]
  simpa only [sub_eq_add_neg] using PlaneModel.central_displacement z (π ⟨x,hx⟩).toAdd

include hc in
/-- The source alignment follows from one moving radical element and the
actual Levi lift. The element's full displacement image is the marked plane. -/
theorem align (A : Subgroup G) (hA : A ≤ E.R₁)
    (hz : ¬ A ≤ centralizer (E.V₃ : Set G)) :
    ∃ l ∈ E.L₁,
      V ⊓ centralizer (A.map (MulAut.conj l).toMonoidHom : Set G) ≤ E.V₂ ∧
      E.V₂ ≤ ⁅V,A.map (MulAut.conj l).toMonoidHom⁆ := by
  let π := markedProjection E m p.basis
  have hi := markedProjection_injective E m p.basis hc
  obtain ⟨a,ha,han⟩ : ∃ a ∈ A, a ∉ centralizer (E.V₃ : Set G) := by
    simpa only [SetLike.le_def,not_forall,exists_prop] using hz
  let aN : normalizer (V : Set G) := ⟨a,radical_normalizes_seed E (hA ha)⟩
  obtain ⟨u,v,z,hr⟩ := p.radical ⟨a,hA ha⟩
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_contra! huv
    apply han
    intro x hx
    have hxV := D.centralQuotientPreimage_le E.threeSpace hx
    let xV : V := ⟨x,hxV⟩
    have he : V.normalizerMonoidHom aN xV = xV := by
      apply hi
      apply Multiplicative.toAdd.injective
      rw [hr,huv.1,huv.2]
      exact PlaneModel.central_fixes_three z _ ((p.three xV).mp hx)
    have he' : a*x*a⁻¹=x := congrArg Subtype.val he
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  obtain ⟨b,hb⟩ := PlaneModel.align_radical u v z huv
  obtain ⟨l,hl⟩ := p.levi b
  let lN : normalizer (V : Set G) := ⟨l.val,D.normalizes (E.L₁_le l.property)⟩
  let a' : normalizer (V : Set G) := lN*aN*lN⁻¹
  have hrep : Realizes π a' (PlaneModel.radical 1 0 z) := by
    have he := hl.conj hr
    rw [hb] at he
    exact he
  have ha' : a'.val ∈ A.map (MulAut.conj l.val).toMonoidHom :=
    mem_map_of_mem (MulAut.conj l.val).toMonoidHom ha
  refine ⟨l.val,l.property,?_,?_⟩
  · rintro x ⟨hx,hxc⟩
    let xV : V := ⟨x,hx⟩
    apply (p.plane xV).mpr
    apply (PlaneModel.aligned_fixed z _).mp
    rw [←hrep]
    change (π (V.normalizerMonoidHom a' xV)).toAdd = (π xV).toAdd
    apply congrArg (fun t : V => (π t).toAdd)
    apply Subtype.ext
    change a'.val*x*a'.val⁻¹=x
    rw [hxc a'.val ha',mul_inv_cancel_right]
  · intro x hx
    have hxV := D.centralQuotientPreimage_le E.plane hx
    let xV : V := ⟨x,hxV⟩
    obtain ⟨w,hw⟩ := PlaneModel.aligned_displacement z (π xV).toAdd ((p.plane xV).mp hx)
    obtain ⟨y,hy⟩ := markedProjection_surjective E m p.basis (Multiplicative.ofAdd w)
    change π y = Multiplicative.ofAdd w at hy
    let d : V := V.normalizerMonoidHom a' y * y⁻¹
    have he : d=xV := by
      apply hi
      apply Multiplicative.toAdd.injective
      change (π (V.normalizerMonoidHom a' y * y⁻¹)).toAdd = _
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,hrep]
      simpa only [hy,toAdd_ofAdd,sub_eq_add_neg] using hw
    have hmem : d.val ∈ ⁅V,A.map (MulAut.conj l.val).toMonoidHom⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator ha' y.property
    rwa [he] at hmem

omit p [Finite G] in
private theorem conjugate_cancel (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [he,map_id]

include hc in
/-- The reverse module calculation uses the same point-radical model on
V^(g⁻¹). Its central-root possibility would force V₂≤V₁. Alignment then
identifies the common plane geometrically in both natural modules. -/
theorem reverse_plane (hcore : E.W ≤ E.G₁.pCoreIn 2) (g : G) (hg : g ∈ E.G₁)
    (_hi : V ⊓ V.map (MulAut.conj g).toMonoidHom = E.V₂)
    (hd : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = E.V₂) :
    ∃ l ∈ L,
      (E.V₂.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom = E.V₂ := by
  let A := V.map (MulAut.conj g⁻¹).toMonoidHom
  have hA : A ≤ E.W := by
    rintro _ ⟨v,hv,rfl⟩
    exact subset_closure ⟨g⁻¹,E.G₁.inv_mem hg,v,hv,rfl⟩
  have hAR : A ≤ E.R₁ := hA.trans (closure_le_R₁ E m hcore)
  have hback : ⁅V,A⁆ = E.V₂.map (MulAut.conj g⁻¹).toMonoidHom := by
    have he := congrArg (map (MulAut.conj g⁻¹).toMonoidHom) hd
    rw [map_commutator,conjugate_cancel,commutator_comm] at he
    exact he
  have hbad : ¬ A ≤ centralizer (E.V₃ : Set G) := by
    intro hz
    have he := p.commutator_le_point A hAR hz
    rw [hback] at he
    have he' := map_mono (f := (MulAut.conj g).toMonoidHom) he
    have hp : E.V₁.map (MulAut.conj g).toMonoidHom = E.V₁ :=
      mem_normalizer_iff_map_conj_eq.mp hg
    have hcancel : (E.V₂.map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj g).toMonoidHom = E.V₂ := by
      simpa only [inv_inv] using conjugate_cancel E.V₂ g⁻¹
    rw [hcancel,hp] at he'
    rw [m.plane_preimage,m.point_preimage] at he'
    have hs := (LocalGeometry.Coordinates.sp4 m.action).preimage_le_iff _ _ |>.mp he'
    let : Module.Finite E.input.field.Carrier
        (LocalGeometry.Coordinates.sp4 m.action).Space :=
      inferInstanceAs (Module.Finite E.input.field.Carrier (Vector E.input.field.Carrier))
    have hn := Submodule.finrank_mono hs
    rw [m.flag.dimension 1,m.flag.dimension 0] at hn
    norm_num at hn
  obtain ⟨l,hl,hf,hm⟩ := p.align hc A hAR hbad
  have hlg : l*g⁻¹ ∈ E.G₁ := E.G₁.mul_mem
    (((residualIn_le _).trans inf_le_right) hl) (E.G₁.inv_mem hg)
  have hmap : V.map (MulAut.conj (l*g⁻¹)).toMonoidHom =
      A.map (MulAut.conj l).toMonoidHom := by
    rw [map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  have hplane := (intersection_eq_plane E (closure_normalizes_seed E m hcore) hlg
    (by rwa [hmap]) (by rwa [hmap])).2
  rw [hmap] at hplane
  have hVl : V.map (MulAut.conj l).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (D.normalizes (E.L₁_le hl))
  have he : (E.V₂.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj l).toMonoidHom = E.V₂ := by
    rw [←hback,map_commutator,hVl,hplane]
  have he' := congrArg (map (MulAut.conj l⁻¹).toMonoidHom) he
  rw [conjugate_cancel] at he'
  refine ⟨l⁻¹,L.inv_mem (E.L₁_le hl),?_⟩
  rw [←he']
  simpa only [inv_inv] using conjugate_cancel E.V₂ g⁻¹

include hc in
/-- Both crossing-plane calculations, with only the preceding marked local
geometry and the allowed initial core and fixed-space hypotheses. -/
theorem crossingPlanes (hcore : E.W ≤ E.G₁.pCoreIn 2) : CrossingPlanes E where
  align A _ hA _ hz := p.align hc A hA hz
  reverse_plane g hg hi hd := p.reverse_plane hc hcore g hg hi hd

end PointCoordinates

/-- The original escaping-conjugate consumer with both plane premises discharged. -/
theorem exists_crossing_plane_of_point_coordinates (m : MarkedFlag E)
    (p : PointCoordinates E m) (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hcore : E.W ≤ E.G₁.pCoreIn 2) (hne : ⁅V,E.U⁆ ≠ ⊥) :
    ∃ g ∈ E.G₁, V ⊓ V.map (MulAut.conj g).toMonoidHom = E.V₂ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = E.V₂ :=
  exists_crossing_plane E m (p.crossingPlanes hc hcore) hcore hne

/-- The actual terminal contradiction now retains only the preceding point
geometry, initial core bound, second-radical calculation and source 11.1.3. -/
theorem noncommuting_impossible_of_point_coordinates (m : MarkedFlag E)
    (p : PointCoordinates E m) (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (r : RadicalDisplacement E) (hcore : E.W ≤ E.G₁.pCoreIn 2)
    (hu : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved : ⁅V,E.L₂⁆ = V) (hne : ⁅V,E.U⁆ ≠ ⊥) : False :=
  noncommuting_impossible E m (p.crossingPlanes hc hcore) r hcore hu hmoved hne

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal

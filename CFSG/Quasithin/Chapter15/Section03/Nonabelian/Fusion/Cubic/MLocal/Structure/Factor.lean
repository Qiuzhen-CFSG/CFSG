module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.ActorCentralizer
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.QuotientCentralizer
public import Theory.GroupTheory.CubicNaturalFourExtension
/-!
# The symmetric factor in the marked cubic centralizer

The action centralizer has coordinates SL₂(2) times a cyclic group of
order three. The quotient-constituent calculation identifies its kernel
with the actual definite plane V₁. Coordinates on V₁ inherit the prescribed
natural action, so the natural-four extension theorem applies. Its
companion-plane projection splits off the central cubic and recognizes
the kernel of that projection as S₄, with two-core precisely V₁.

The involution calculation uses the actual orthogonal actor: outside V₁,
an involution in the cubic centralizer has a nonidentity actor and fixes
eight vectors. The only additional equality in the conditional factor
helper is the action-kernel calculation established in QuotientCentralizer;
the source wrapper is responsible for discharging it.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), setup of
15.3.60, printed p.1150, using 15.3.53–55 and 15.3.58–59.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
open OrthogonalGeometry
local instance factorOrthogonalAction : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction
local instance factorPlaneAction : MulDistribMulAction OrthogonalPlaneActor OrthogonalPlaneVector := FourGroupMatrixCoordinates.naturalAction
variable {G : Type*} [Group G] {M V : Subgroup G}

private theorem plane_support (d : NaturalOrthogonalAction M V) (i : OrthogonalPlaneIndex)
    (x : d.plane i) : d.coordinates ⟨x, d.plane_le i x.property⟩ ∈ orthogonalCoordinatePlane i := by
  obtain ⟨v, hv, he⟩ := x.property
  have hev : v = ⟨x, d.plane_le i x.property⟩ := Subtype.ext he
  exact hev ▸ hv

private def planeCoordinateHom (d : NaturalOrthogonalAction M V) (i : OrthogonalPlaneIndex) :
    d.plane i →* OrthogonalPlaneVector where
  toFun x := d.coordinates ⟨x, d.plane_le i x.property⟩ i
  map_one' := congrFun d.coordinates.map_one i
  map_mul' x y := congrFun (d.coordinates.map_mul
    ⟨x, d.plane_le i x.property⟩ ⟨y, d.plane_le i y.property⟩) i

private theorem planeCoordinateHom_bijective (d : NaturalOrthogonalAction M V)
    (i : OrthogonalPlaneIndex) : Function.Bijective (planeCoordinateHom d i) := by
  constructor
  · intro x y he
    have hc : d.coordinates ⟨x, d.plane_le i x.property⟩ =
        d.coordinates ⟨y, d.plane_le i y.property⟩ := by
      funext j
      by_cases hj : j = i
      · subst j; exact he
      · rw [plane_support d i x j hj, plane_support d i y j hj]
    exact Subtype.ext (congrArg (fun v : V => (v : G)) (d.coordinates.injective hc))
  · intro w
    let v := d.coordinates.symm (fun j => if j = i then w else 1)
    have hv : v ∈ (orthogonalCoordinatePlane i).comap d.coordinates.toMonoidHom := by
      change d.coordinates v ∈ orthogonalCoordinatePlane i
      rw [d.coordinates.apply_symm_apply]
      intro j hj
      exact if_neg hj
    refine ⟨⟨v, ⟨v, hv, rfl⟩⟩, ?_⟩
    change d.coordinates v i = w
    rw [d.coordinates.apply_symm_apply, if_pos rfl]

/-- The definite plane has coordinates inherited from the specified full module. -/
private noncomputable def planeCoordinates (d : NaturalOrthogonalAction M V) (i : OrthogonalPlaneIndex) :
    d.plane i ≃* OrthogonalPlaneVector :=
  MulEquiv.ofBijective (planeCoordinateHom d i) (planeCoordinateHom_bijective d i)

/-- Involutions in the actual cubic centralizer outside its action kernel
fix a hyperplane. This requires neither an abstract S₄ identification nor a
fixed-space premise. -/
theorem cubic_centralizer_involution_fixed [Finite G] (d : NaturalOrthogonalAction M V)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (i : OrthogonalPlaneIndex)
    (PM3 : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G))
    (hker : (M ⊓ centralizer (planeCubic M (d.plane i) PM3 : Set G)) ⊓
      centralizer (V : Set G) = d.plane i)
    (t : G) (ht : t ∈ M ⊓ centralizer (planeCubic M (d.plane i) PM3 : Set G))
    (htpow : orderOf t = 2) (htout : t ∉ d.plane i) :
    Nat.card (fixedPlane V (zpowers t)) = 8 := by
  obtain ⟨a, ha, _, hord, hne⟩ := planeCubic_generator d hcop i PM3
  have hpoint : d.actor a ∈ pointwise (orthogonalCoordinatePlane i) := by
    have h : a ∈ (centralizer (d.plane i : Set G)).subgroupOf M :=
      planeCubic_le_centralizer M (d.plane i) PM3 ha
    rwa [d.plane_eq_map, d.centralizer_map_eq_comap] at h
  have hpow : d.actor a ^ 3 = 1 := by rw [← map_pow, ← hord, pow_orderOf_eq_one, map_one]
  obtain ⟨hr, hi, hp, hn⟩ := ActorCentralizer.marked_coordinates i (d.actor a) hpow hne hpoint
  let tm : M := ⟨t, ht.1⟩
  have hct : d.actor tm * d.actor a = d.actor a * d.actor tm := by
    rw [← map_mul, ← map_mul]
    exact congrArg d.actor (Subtype.ext (ht.2 a ha).symm)
  have htp : d.actor tm ^ 2 = 1 := by
    rw [← map_pow]
    have h : tm ^ 2 = 1 := Subtype.ext (htpow ▸ pow_orderOf_eq_one t)
    rw [h, map_one]
  have htn : d.actor tm ≠ 1 := by
    intro h
    have hc : t ∈ centralizer (V : Set G) := by
      have hk : tm ∈ d.actor.ker := h
      rwa [d.ker_actor] at hk
    exact htout (hker ▸ ⟨ht, hc⟩)
  rw [card_fixedPlane_zpowers d tm, Nat.card_eq_fintype_card]
  exact ActorCentralizer.involution_fixed i (d.actor a) (d.actor tm) hr hi hp hn hct htp htn

/-- The remaining extension is split using the actual companion-plane projection.
The sole kernel equality is supplied by the quotient-constituent theorem. -/
theorem exists_symmetric_factor_of_cubic_kernel [Finite G]
    (d : NaturalOrthogonalAction M V)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (i : OrthogonalPlaneIndex)
    (PM3 : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G))
    (hker : (M ⊓ centralizer (planeCubic M (d.plane i) PM3 : Set G)) ⊓
      centralizer (V : Set G) = d.plane i) :
    ∃ (J : Subgroup G) (_ : J ≃* Equiv.Perm (Fin 4)), J ≤ M ∧
      Disjoint (planeCubic M (d.plane i) PM3) J ∧
      planeCubic M (d.plane i) PM3 ≤ centralizer (J : Set G) ∧
      M ⊓ centralizer (planeCubic M (d.plane i) PM3 : Set G) =
        planeCubic M (d.plane i) PM3 ⊔ J ∧
      d.plane i = Stellmacher.twoCoreAmbient J ∧
      (∀ t ∈ J, orderOf t = 2 → t ∉ d.plane i →
        Nat.card (fixedPlane V (zpowers t)) = 8) := by
  let D := planeCubic M (d.plane i) PM3
  let E := M ⊓ centralizer (D : Set G)
  have hDE : D ≤ E := by
    apply le_inf (planeCubic_le_M M (d.plane i) PM3)
    have hcard := card_planeCubic d hcop i PM3
    let _ : IsCyclic D := isCyclic_of_prime_card hcard
    exact D.le_centralizer
  have hVE : d.plane i ≤ E := hker.ge.trans inf_le_left
  obtain ⟨a, ha, hgen, hord, hne⟩ := planeCubic_generator d hcop i PM3
  have hpoint : d.actor a ∈ pointwise (orthogonalCoordinatePlane i) := by
    have h : a ∈ (centralizer (d.plane i : Set G)).subgroupOf M :=
      planeCubic_le_centralizer M (d.plane i) PM3 ha
    rwa [d.plane_eq_map, d.centralizer_map_eq_comap] at h
  have hpow : d.actor a ^ 3 = 1 := by rw [← map_pow, ← hord, pow_orderOf_eq_one, map_one]
  obtain ⟨hr, hi, hp, hn⟩ := ActorCentralizer.marked_coordinates i (d.actor a) hpow hne hpoint
  let B := centralizer ({(d.actor a).left (ActorCentralizer.other i)} : Set OrthogonalPlaneActor)
  let C := centralizer ({d.actor a} : Set OrthogonalActor)
  let raw : E →* OrthogonalActor := d.actor.comp (inclusion inf_le_left)
  have hraw : ∀ x : E, raw x ∈ C := by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    change d.actor ⟨x, x.property.1⟩ * d.actor a = d.actor a * d.actor ⟨x, x.property.1⟩
    rw [← map_mul, ← map_mul]
    exact congrArg d.actor (Subtype.ext (x.property.2 a ha).symm)
  let g : E →* C := raw.codRestrict C hraw
  have hgs : Function.Surjective g := by
    intro c
    have hCE : d.image E = C := by
      rw [image_centralizer_planeCubic d hcop i PM3]
      rw [show d.image D = zpowers (d.actor a) by
          change d.image (planeCubic M (d.plane i) PM3) = _
          rw [← hgen, image_zpowers],
        zpowers_eq_closure, centralizer_closure]
    have hc : (c : OrthogonalActor) ∈ d.image E := hCE.symm ▸ c.property
    obtain ⟨m, hm, he⟩ := hc
    exact ⟨⟨m, hm⟩, Subtype.ext he⟩
  let e := ActorCentralizer.coordinates i (d.actor a) hr hi hn
  let f : E →* OrthogonalPlaneActor × B := e.toMonoidHom.comp g
  have hf : Function.Surjective f := e.surjective.comp hgs
  have hfk : f.ker = (d.plane i).subgroupOf E := by
    change (e.toMonoidHom.comp g).ker = _
    rw [g.ker_comp_of_injective e.toMonoidHom e.injective]
    change (raw.codRestrict C hraw).ker = _
    rw [MonoidHom.ker_codRestrict]
    ext x
    constructor
    · intro hx
      have hm : (⟨x, x.property.1⟩ : M) ∈ d.actor.ker := hx
      rw [d.ker_actor] at hm
      exact hker ▸ ⟨x.property, hm⟩
    · intro hx
      have hx' : (x : G) ∈ E ⊓ centralizer (V : Set G) := hker.symm ▸ hx
      have hm : (⟨x, x.property.1⟩ : M) ∈ d.actor.ker := by
        rw [d.ker_actor]
        exact hx'.2
      exact hm
  let κ : f.ker ≃* OrthogonalPlaneVector :=
    ((MulEquiv.subgroupCongr hfk).trans (subgroupOfEquivOfLe hVE)).trans (planeCoordinates d i)
  have hκ : ∀ (x : E) (k : f.ker), κ (MulAut.conjNormal x k) = (f x).1 • κ k := by
    intro x k
    have hxright := ((ActorCentralizer.commute_coordinates i (d.actor a) (raw x) hr hi hn).mp
      (mem_centralizer_singleton_iff.mp (hraw x))).1
    have hkV : ((k : E) : G) ∈ V := d.plane_le i (show ((k : E) : G) ∈ d.plane i from
      (show k.val ∈ (d.plane i).subgroupOf E from hfk ▸ k.property))
    have hc := congrFun (d.compatible (⟨x, x.property.1⟩ : M) ⟨k.val, hkV⟩) i
    change _ = (raw x).left i • d.coordinates ⟨k.val, hkV⟩ ((raw x).right⁻¹ * i) at hc
    rw [hxright, inv_one, one_mul] at hc
    exact hc
  let aE : E := ⟨a, hDE ha⟩
  have hgenE : zpowers aE = D.subgroupOf E := by
    apply map_injective E.subtype_injective
    rw [MonoidHom.map_zpowers, map_subgroupOf_eq_of_le hDE]
    exact hgen
  have hBcard : Nat.card B = 3 := ActorCentralizer.card_companion _ hp hn
  have hDcard : Nat.card (D.subgroupOf E) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDE).toEquiv]
    exact card_planeCubic d hcop i PM3
  have hDcenter : D.subgroupOf E ≤ center E := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (y.property.2 x hx).symm
  have hDf : (D.subgroupOf E).map f = (⊥ : Subgroup OrthogonalPlaneActor).prod (⊤ : Subgroup B) := by
    rw [← hgenE, MonoidHom.map_zpowers]
    have hfa : f aE = (1, (⟨(d.actor a).left (ActorCentralizer.other i),
        mem_centralizer_singleton_iff.mpr rfl⟩ : B)) := Prod.ext hi rfl
    rw [hfa]
    let b : B := ⟨(d.actor a).left (ActorCentralizer.other i), mem_centralizer_singleton_iff.mpr rfl⟩
    have hb : zpowers b = ⊤ := ActorCentralizer.companion_zpowers_top _ hp hn
    apply le_antisymm
    · apply zpowers_le.mpr
      exact ⟨rfl, mem_top _⟩
    · rintro ⟨x, y⟩ ⟨hx, _⟩
      have hx1 : x = 1 := hx
      subst x
      have hy : y ∈ zpowers b := hb.symm ▸ mem_top _
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
      exact ⟨n, by change (1, b) ^ n = (1, b ^ n); simp⟩
  obtain ⟨J₀, e₀, _hJdef, _hJn, hd, hc, hs, _hkcard, _hJcard, _hkJ, _hkN, _hkC, hcore⟩ :=
    CubicNaturalFourExtension.exists_symmetric_complement f hf hBcard κ hκ
      (D.subgroupOf E) hDcenter hDcard hDf
  let J := J₀.map E.subtype
  let eJ : J₀ ≃* J := J₀.equivMapOfInjective E.subtype E.subtype_injective
  have hJle : J ≤ E := map_subtype_le _
  have hd' : Disjoint D J := by
    have hh := disjoint_map E.subtype_injective hd
    rwa [map_subgroupOf_eq_of_le hDE] at hh
  have hc' : D ≤ centralizer (J : Set G) := by
    intro x hx y hy
    obtain ⟨y, hy, rfl⟩ := hy
    exact congrArg Subtype.val (hc (show (⟨x, hDE hx⟩ : E) ∈ D.subgroupOf E from hx) y hy)
  have hs' : E = D ⊔ J := by
    have hh := congrArg (Subgroup.map E.subtype) hs
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hDE, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh.symm
  have hcore' : d.plane i = Stellmacher.twoCoreAmbient J := by
    have hh := congrArg (Subgroup.map E.subtype) hcore
    rw [map_map, hfk, map_subgroupOf_eq_of_le hVE] at hh
    change d.plane i = (pCore 2 J).map J.subtype
    rw [← pCore_map_iso 2 eJ, map_map]
    exact hh.symm
  exact ⟨J, eJ.symm.trans e₀, hJle.trans inf_le_left, hd', hc', hs', hcore',
    fun t ht ht2 hto => cubic_centralizer_involution_fixed d hcop i PM3 hker t (hJle ht) ht2 hto⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure

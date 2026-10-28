module

public import Theory.AlgebraicGroup.Reductive.Basic
public import Theory.AlgebraicGroup.Reductive.DerivedCenter
public import Theory.AlgebraicGroup.Tori.Semisimple
public import Theory.AlgebraicGroup.Unipotent.OneParameterCore

/-!
Regular root sections of a central quotient are rigid when the source group
upstairs is reductive. A central morphism from a connected unipotent group
lands in the toral identity component of the center and is therefore trivial.
Applying this to the difference of two sections lifts their conjugation laws.
A nontrivial scalar conjugation then writes every root element as a commutator.

The central kernel intersects the abstract derived subgroup in a finite set.
Consequently two regular maps into that subgroup with the same quotient map
agree everywhere on a connected domain once they agree at one point. This is
the comparison needed for root-word chart overlaps and multiplication defects;
it does not assert that those charts have already been constructed.

Sources: Borel, *Linear Algebraic Groups*, §§13.13--13.14 and 13.18;
GLS3, §§1.9--1.12. The proof retains finite central kernels in all
characteristics and makes no regular-inverse inference from point bijectivity.
-/

open Theory.AlgebraicGroup

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts.CentralLifting

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X Y Q : Variety k} [AlgebraicGroup X] [AlgebraicGroup Y] [AlgebraicGroup Q]

/-- A connected unipotent group has no nontrivial central image in a reductive group. -/
public theorem central_unipotent_morphism_eq_one
    (hY : IsReductiveAlgebraicGroup Y)
    (hX : Variety.IsConnected X) (hXu : IsUnipotentAlgebraicGroup X)
    (f : Morphism X Y) (hf : f.image ≤ Subgroup.center (Variety.Point Y))
    (x : Variety.Point X) : f.onPoints x = 1 := by
  let Z : ClosedSubgroup Y := (ClosedSubgroup.top (G := Y)).centralizer
  have hZ : Z.toSubgroup = Subgroup.center (Variety.Point Y) := by
    change Subgroup.centralizer (Set.univ : Set (Variety.Point Y)) = _
    exact Subgroup.centralizer_univ
  have himage : f.imageClosedSubgroup ≤ Z := by
    intro y hy
    change y ∈ Z.toSubgroup
    rw [hZ]
    exact hf hy
  have hconn := connected_closedSubgroup_le_identityComponentAmbient
    f.imageClosedSubgroup Z (f.imageClosedSubgroup_isConnected hX) himage
  have hx : f.onPoints x ∈ Z.identityComponentAmbient := hconn ⟨x, rfl⟩
  let z : Variety.Point Z.identityComponentAmbient.carrierVariety :=
    Z.identityComponentAmbient.pointEquiv.symm ⟨f.onPoints x, hx⟩
  have hs : IsSemisimpleElement Y (f.onPoints x) :=
    morphism_preserves_semisimpleElement Z.identityComponentAmbient.inclusion z
      ((center_identityComponent_isSubtorus_of_reductive hY).all_semisimple z)
  exact semisimple_unipotent_eq_one _ hs
    (morphism_preserves_unipotentElement f x (hXu x))

-- Pointwise central differences of regular homomorphisms are regular homomorphisms.
private def centralDifference (f g : Morphism X Y)
    (hc : ∀ x, f.onPoints x * (g.onPoints x)⁻¹ ∈ Subgroup.center (Variety.Point Y)) :
    Morphism X Y where
  toVariety := (mulMorphism Y).comp
    (f.toVariety.pair ((invMorphism Y).comp g.toVariety))
  map_one := by
    change f.onPoints 1 * (g.onPoints 1)⁻¹ = 1
    simp
  map_mul := by
    intro x y
    change f.onPoints (x*y) * (g.onPoints (x*y))⁻¹ =
      (f.onPoints x * (g.onPoints x)⁻¹) * (f.onPoints y * (g.onPoints y)⁻¹)
    rw [map_mul, map_mul]
    have hcomm := Subgroup.mem_center_iff.mp (hc y) (g.onPoints x)⁻¹
    calc
      _ = f.onPoints x * (f.onPoints y * (g.onPoints y)⁻¹) * (g.onPoints x)⁻¹ := by group
      _ = f.onPoints x * (g.onPoints x)⁻¹ * (f.onPoints y * (g.onPoints y)⁻¹) := by
        rw [mul_assoc, ← hcomm, ← mul_assoc]

/-- Regular maps from a connected unipotent group through a central quotient
of a reductive group have unique lifts. Surjectivity is not needed. -/
public theorem central_quotient_unipotent_morphism_ext
    (hY : IsReductiveAlgebraicGroup Y)
    (hX : Variety.IsConnected X) (hXu : IsUnipotentAlgebraicGroup X)
    (q : Morphism Y Q) (hq : q.kernel ≤ Subgroup.center (Variety.Point Y))
    (f g : Morphism X Y) (hfg : q.comp f = q.comp g) : f = g := by
  have hc (x : Variety.Point X) :
      f.onPoints x * (g.onPoints x)⁻¹ ∈ Subgroup.center (Variety.Point Y) := by
    apply hq
    change q.onPoints (f.onPoints x * (g.onPoints x)⁻¹) = 1
    rw [map_mul, map_inv]
    have he := congrArg (fun m : Morphism X Q => m.onPoints x) hfg
    change q.onPoints (f.onPoints x) = q.onPoints (g.onPoints x) at he
    rw [he, mul_inv_cancel]
  have hd (x : Variety.Point X) := central_unipotent_morphism_eq_one
    hY hX hXu (centralDifference f g hc) (by rintro _ ⟨x, rfl⟩; exact hc x) x
  apply Morphism.ext
  funext x
  exact mul_inv_eq_one.mp (hd x)

-- Conjugation as a regular group homomorphism.
private def conjugateHom (y : Variety.Point Y) : Morphism Y Y where
  toVariety := conjugationByMorphism Y y
  map_one := by simp [conjugationByMorphism_apply]
  map_mul := by
    intro a b
    simp only [conjugationByMorphism_apply]
    group

/-- A scalar conjugation law for the projected root curve holds literally upstairs. -/
public theorem root_conjugation_of_quotient_scaling
    (hY : IsReductiveAlgebraicGroup Y)
    (q : Morphism Y Q) (hq : q.kernel ≤ Subgroup.center (Variety.Point Y))
    (f : Morphism (KPlus k) Y) (y : Variety.Point Y) (a : k)
    (ha : ∀ t, q.onPoints (y * f.onPoints (kPlusPoint t) * y⁻¹) =
      q.onPoints (f.onPoints (kPlusPoint (a*t)))) (t : k) :
    y * f.onPoints (kPlusPoint t) * y⁻¹ = f.onPoints (kPlusPoint (a*t)) := by
  have he : (conjugateHom y).comp f = f.comp (additiveScalarMorphism a) := by
    apply central_quotient_unipotent_morphism_ext hY kPlus_isConnected
      kPlus_isUnipotentAlgebraicGroup q hq
    apply Morphism.ext
    funext s
    obtain ⟨b, rfl⟩ : ∃ b, kPlusPoint b = s := ⟨_, kPlusPoint_coordinate s⟩
    exact ha b
  exact congrArg (fun m : Morphism (KPlus k) Y => m.onPoints (kPlusPoint t)) he

open scoped commutatorElement in
/-- Nontrivial scalar conjugation in the quotient puts the entire root curve
in the actual abstract derived subgroup upstairs. -/
public theorem root_mem_commutator_of_quotient_scaling
    (hY : IsReductiveAlgebraicGroup Y)
    (q : Morphism Y Q) (hq : q.kernel ≤ Subgroup.center (Variety.Point Y))
    (f : Morphism (KPlus k) Y) (y : Variety.Point Y) (a : k) (ha1 : a ≠ 1)
    (ha : ∀ t, q.onPoints (y * f.onPoints (kPlusPoint t) * y⁻¹) =
      q.onPoints (f.onPoints (kPlusPoint (a*t)))) (t : k) :
    f.onPoints (kPlusPoint t) ∈ _root_.commutator (Variety.Point Y) := by
  let b := t / (a-1)
  have hab : a*b-b=t := by
    dsimp [b]
    field_simp [sub_ne_zero.mpr ha1]
  have hword : ⁅y, f.onPoints (kPlusPoint b)⁆ = f.onPoints (kPlusPoint t) := by
    change y * f.onPoints (kPlusPoint b) * y⁻¹ * (f.onPoints (kPlusPoint b))⁻¹ = _
    rw [root_conjugation_of_quotient_scaling hY q hq f y a ha,
      ← map_inv, ← map_mul]
    rw [show (kPlusPoint b)⁻¹ = kPlusPoint (-b) from rfl, kPlusPoint_mul]
    congr 2
    simpa only [sub_eq_add_neg] using hab
  rw [← hword]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The central kernel restricted to the actual abstract derived subgroup is finite. -/
public theorem central_derived_kernel_finite
    (hY : IsReductiveAlgebraicGroup Y)
    (q : Morphism Y Q) (hq : q.kernel ≤ Subgroup.center (Variety.Point Y)) :
    (((q.kernel ⊓ _root_.commutator (Variety.Point Y)) :
      Subgroup (Variety.Point Y)) : Set (Variety.Point Y)).Finite := by
  apply (reductive_commutator_center_finite hY).subset
  rintro x ⟨hxq, hxd⟩
  refine ⟨hxd, ?_⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro y _hy
  exact Subgroup.mem_center_iff.mp (hq hxq) y

omit [IsAlgClosed k] in
/-- Regular maps with finite kernel discrepancies on a connected domain
are determined by their quotient map and their value at one point. -/
public theorem regular_maps_eq_of_finite_kernel
    {V : Variety k} (hV : Variety.IsConnected V)
    (q : Morphism Y Q) (S : Subgroup (Variety.Point Y))
    (hfinite : (((q.kernel ⊓ S) : Subgroup (Variety.Point Y)) :
      Set (Variety.Point Y)).Finite)
    (f g : Variety.Morphism V Y)
    (hf : ∀ x, f.toFun x ∈ S) (hg : ∀ x, g.toFun x ∈ S)
    (hproj : ∀ x, q.onPoints (f.toFun x) = q.onPoints (g.toFun x))
    (x₀ : Variety.Point V) (h₀ : f.toFun x₀ = g.toFun x₀) : f = g := by
  let d : Variety.Morphism V Y := (mulMorphism Y).comp
    (f.pair ((invMorphism Y).comp g))
  have hd (x : Variety.Point V) : d.toFun x = f.toFun x * (g.toFun x)⁻¹ := rfl
  have hrange : (Set.range d.toFun).Finite := hfinite.subset (by
    rintro _ ⟨x, rfl⟩
    change d.toFun x ∈ q.kernel ∧ d.toFun x ∈ S
    rw [hd]
    constructor
    · change q.onPoints (f.toFun x * (g.toFun x)⁻¹) = 1
      rw [map_mul, map_inv, hproj, mul_inv_cancel]
    · exact S.mul_mem (hf x) (S.inv_mem (hg x)))
  have hc := connected_finite_morphism_range_subsingleton d hV hrange
  apply Variety.Morphism.ext
  funext x
  apply mul_inv_eq_one.mp
  have he := hc (Set.mem_range_self x) (Set.mem_range_self x₀)
  simpa only [hd, h₀, mul_inv_cancel] using he

/-- Compare regular maps into the actual derived subgroup of a reductive central cover. -/
public theorem regular_derived_maps_eq
    {V : Variety k} (hV : Variety.IsConnected V)
    (hY : IsReductiveAlgebraicGroup Y)
    (q : Morphism Y Q) (hq : q.kernel ≤ Subgroup.center (Variety.Point Y))
    (f g : Variety.Morphism V Y)
    (hf : ∀ x, f.toFun x ∈ _root_.commutator (Variety.Point Y))
    (hg : ∀ x, g.toFun x ∈ _root_.commutator (Variety.Point Y))
    (hproj : ∀ x, q.onPoints (f.toFun x) = q.onPoints (g.toFun x))
    (x₀ : Variety.Point V) (h₀ : f.toFun x₀ = g.toFun x₀) : f = g :=
  regular_maps_eq_of_finite_kernel hV q _ (central_derived_kernel_finite hY q hq)
    f g hf hg hproj x₀ h₀

end Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts.CentralLifting

module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.Sections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.PermittedChoice.ActorOrbits.Cubic

/-!
# The two actual L₁ orbits used to choose the critical point

A literal L₁ actor whose d.qH-image is an upper conjugate of a nontrivial
split diagonal supplies both orbit calculations. Its powers act transitively
on the nonzero upper natural line and conjugate the three nonidentity upper
unipotents. The proofs here transport those calculations through the original
projection p, the original conjugation coordinates, and the actual star map.

For the first orbit, earlier65 identifies the upper fixed space with
Ṽ + ker p. Descent is constructed by `Data.actionDescentOfCore`, and its
projection is the same p. Thus all points of U₀V outside U₀ project to
nonzero upper-line vectors. Equality of their conjugated projections is
exactly membership of their quotient in the original U₀. ModuleSeparation
supplies a nonzero projected point of the actual V₂, giving direct placement
in U₀V₂. The later rank restriction is unnecessary for these orbit facts.

For the second orbit, `UpperMarking` and the literal earlier Q*=R₁* identity
identify each nonidentity image with an upper unipotent. The same cubic
calculation yields equality in H/O₂(H), using the injectivity of d.model.
No transitivity, critical path, centrality or permitted-choice conclusion
occurs among the premises. The returned actors lie in both H and the actual L₁.

The local cubic witness and compatible earlier65 marking have producers
qt-14-03/qt-14-07; ModuleSeparation is earlier14.7.2(1), and core
centralization is14.5.15(4), owned by qt-14-05. These earlier source inputs
remain explicit as authorized. Final construction of one permitted critical
rechoice and discharge of its selection obligations belong to
qt-14-07-rechoice-permitted-selection. This module imports Preparation.Sections
directly and does not import its eventual PermittedChoice consumer.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004, proof of
14.7.70, printed p.1073 (PDF p.1090), the two L₁-conjugation choices.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.PermittedChoice.ActorOrbits
open Subgroup Representation Chapter12.Section08 Matrix.SpecialLinearGroup
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W)

/-- The literal earlier local cubic, in the original natural marking.
Its earlier 14.3/14.7 producers are qt-14-03 and qt-14-07. The upper
conjugate allows compatibility with `UpperMarking` without changing d.qH.
This input asserts an actual actor image, and neither orbit conclusion. -/
def LocalCubic : Prop :=
  ∃ l : F.H, (l : G) ∈ F.Li L 1 ∧ ∃ a : SL2FourNatural.F,
    ∃ ha : a ≠ 0, a ≠ 1 ∧ ∃ r : SL2FourNatural.F,
      d.qH l = alternatingActor d.naturalQuotient
        (SL2FourNatural.upper r * diag2 a ha * (SL2FourNatural.upper r)⁻¹)

private theorem projection_upper
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (h65 : SL2CentralExtension.upperFixed
      ((d.actionDescentOfCore hcore).action.comp (alternatingActor d.naturalQuotient)) =
        tilde d V ⊔ d.projection.toLinearMap.ker)
    (x : F.U) (hx : (x : G) ∈ d.U₀ ⊔ V) :
    d.projection (d.conjugationSection.coordinates x).toAdd 1 = 0 := by
  let s := d.actionDescentOfCore hcore
  let p := restrictedProjection d.naturalQuotient s.projection
  apply (SL2CentralExtension.mem_upperFixed_iff _ p.toLinearMap d.projection_onto
    (fun g v => LinearMap.congr_fun (p.isIntertwining' g) v)
    (fun v hv g => s.kernel_fixed hv g) _).mp
  rw [h65, ← tilde_U₀ d, ← tilde_sup d (Data.V_le_U F) d.U₀_le_U, sup_comm V]
  exact (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨x, hx, rfl⟩

/-- The first L₁ orbit calculation of 14.7.70, on the original U₀V/U₀.
The chosen conjugator is the inverse of a power of the actual cubic lift. -/
theorem exists_conjugate_mod_U₀ (cubic : LocalCubic d)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (h65 : SL2CentralExtension.upperFixed
      ((d.actionDescentOfCore hcore).action.comp (alternatingActor d.naturalQuotient)) =
        tilde d V ⊔ d.projection.toLinearMap.ker)
    (x y : F.U) (hx : (x : G) ∈ d.U₀ ⊔ V) (hy : (y : G) ∈ d.U₀ ⊔ V)
    (hx0 : (x : G) ∉ d.U₀) (hy0 : (y : G) ∉ d.U₀) :
    ∃ l : F.H, (l : G) ∈ F.Li L 1 ∧
      ((l : G)⁻¹ * (x : G) * l) * (y : G)⁻¹ ∈ d.U₀ := by
  obtain ⟨l, hl, a, ha, ha1, r, he⟩ := cubic
  have hxn : d.projection (d.conjugationSection.coordinates x).toAdd ≠ 0 := by
    intro hz
    exact hx0 ((d.mem_U₀ x).mpr hz)
  have hyn : d.projection (d.conjugationSection.coordinates y).toAdd ≠ 0 := by
    intro hz
    exact hy0 ((d.mem_U₀ y).mpr hz)
  obtain ⟨n, hn⟩ := Cubic.vector_orbit a ha ha1 r _ _ hxn hyn
    (projection_upper d hcore h65 x hx) (projection_upper d hcore h65 y hy)
  let k : F.H := l^n
  let z : F.U := ⟨(k : G) * (x : G) * (k : G)⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized k.property) x).mp x.property⟩
  have hz : d.projection (d.conjugationSection.coordinates z).toAdd =
      d.projection (d.conjugationSection.coordinates y).toAdd := by
    rw [d.conjugationSection.equivariant k x]
    have hp : d.projection (d.action k (d.conjugationSection.coordinates x).toAdd) =
        d.naturalQuotient.action (d.qH k)
          (d.projection (d.conjugationSection.coordinates x).toAdd) :=
      LinearMap.congr_fun (d.projection.isIntertwining' k) _
    rw [hp]
    change d.naturalQuotient.action (d.qH (l^n)) _ = _
    rw [map_pow, he, ← map_pow]
    exact (d.naturalQuotient.restriction _ _).trans hn
  have hm : ((z * y⁻¹ : F.U) : G) ∈ d.U₀ := by
    apply (d.mem_U₀ _).mpr
    change d.projection (d.conjugationSection.coordinates (z * y⁻¹)).toAdd = 0
    rw [map_mul, map_inv]
    rw [toAdd_mul, toAdd_inv, map_add, map_neg, hz, add_neg_cancel]
  refine ⟨k⁻¹, (F.Li L 1).inv_mem ((F.Li L 1).pow_mem hl n), ?_⟩
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using hm

/-- Apply the first orbit to the genuinely nonzero plane point furnished
by earlier 14.7.2(1), retaining both its ambient placement and the same p. -/
theorem exists_conjugate_mod_U₀_in_plane (cubic : LocalCubic d)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (h65 : SL2CentralExtension.upperFixed
      ((d.actionDescentOfCore hcore).action.comp (alternatingActor d.naturalQuotient)) =
        tilde d V ⊔ d.projection.toLinearMap.ker)
    (separation : d.ModuleSeparation)
    (x : F.U) (hx : (x : G) ∈ d.U₀ ⊔ V) (hx0 : (x : G) ∉ d.U₀) :
    ∃ y : F.U, (y : G) ∈ F.Vi 2 ∧ (y : G) ∉ d.U₀ ∧
      ∃ l : F.H, (l : G) ∈ F.Li L 1 ∧
        ((l : G)⁻¹ * (x : G) * l) * (y : G)⁻¹ ∈ d.U₀ := by
  obtain ⟨y, hy, hyn⟩ := d.exists_plane_point separation
  have hy0 : (y : G) ∉ d.U₀ := fun h => hyn ((d.mem_U₀ y).mp h)
  exact ⟨y, hy, hy0, exists_conjugate_mod_U₀ d cubic hcore h65 x y hx
    (mem_sup_right (F.le_seed 2 hy)) hx0 hy0⟩

/-- Direct placement of the conjugated point in the original plane product. -/
theorem exists_conjugate_in_plane_product (cubic : LocalCubic d)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (h65 : SL2CentralExtension.upperFixed
      ((d.actionDescentOfCore hcore).action.comp (alternatingActor d.naturalQuotient)) =
        tilde d V ⊔ d.projection.toLinearMap.ker)
    (separation : d.ModuleSeparation)
    (x : F.U) (hx : (x : G) ∈ d.U₀ ⊔ V) (hx0 : (x : G) ∉ d.U₀) :
    ∃ l : F.H, (l : G) ∈ F.Li L 1 ∧
      (l : G)⁻¹ * (x : G) * l ∈ d.U₀ ⊔ F.Vi 2 := by
  obtain ⟨y, hy, _, l, hl, hm⟩ :=
    exists_conjugate_mod_U₀_in_plane d cubic hcore h65 separation x hx hx0
  refine ⟨l, hl, ?_⟩
  have h := (d.U₀ ⊔ F.Vi 2).mul_mem (mem_sup_left hm) (mem_sup_right hy)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

private theorem upper_zero : SL2FourNatural.upper 0 = 1 := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [SL2FourNatural.upper]

private theorem star_upper_parameter (mark : UpperMarking d)
    (x : HStar F.H) (hx : x ∈ star F (F.Ri L 1)) (hx1 : x ≠ 1) :
    ∃ t : SL2FourNatural.F, t ≠ 0 ∧
      d.model x = alternatingActor d.naturalQuotient (SL2FourNatural.upper t) := by
  have hm : d.model x ∈ ((F.Ri L 1).subgroupOf F.H).map d.qH := by
    obtain ⟨h, hh, he⟩ := hx
    exact ⟨h, hh, congrArg d.model he⟩
  rw [mark] at hm
  obtain ⟨g, hg, hge⟩ := hm
  obtain ⟨t, ht⟩ := (mem_upperUnipotent SL2FourNatural.F g).mp hg
  have hgt : g = SL2FourNatural.upper t :=
    ht.symm.trans (SL2FourCentralCover.upper_transvection t).symm
  refine ⟨t, ?_, (hgt ▸ hge).symm⟩
  intro hz
  subst t
  rw [hgt, upper_zero, map_one] at hge
  exact hx1 (d.model.injective (hge.symm.trans d.model.map_one.symm))

/-- The second L₁ orbit calculation of 14.7.70, inside the literal Q*.
The earlier equality Q*=R₁* and compatible upper marking identify the actual
images; cubic conjugacy is then lifted through the original d.qH and starMap. -/
theorem exists_star_conjugate (cubic : LocalCubic d) (mark : UpperMarking d)
    (himage : star F (Q T L) = star F (F.Ri L 1))
    (x y : HStar F.H) (hx : x ∈ star F (Q T L)) (hy : y ∈ star F (Q T L))
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ l : F.H, (l : G) ∈ F.Li L 1 ∧
      (starMap F l)⁻¹ * x * starMap F l = y := by
  obtain ⟨l, hl, a, ha, ha1, r, he⟩ := cubic
  obtain ⟨t, ht, hx'⟩ := star_upper_parameter d mark x (himage ▸ hx) hx1
  obtain ⟨s, hs, hy'⟩ := star_upper_parameter d mark y (himage ▸ hy) hy1
  obtain ⟨n, hn⟩ := Cubic.upper_orbit a ha ha1 r t s ht hs
  refine ⟨(l^n)⁻¹, (F.Li L 1).inv_mem ((F.Li L 1).pow_mem hl n), ?_⟩
  apply d.model.injective
  simp only [map_mul, map_inv]
  change (d.qH (l^n))⁻¹⁻¹ * d.model x * (d.qH (l^n))⁻¹ = d.model y
  rw [inv_inv, map_pow, he, ← map_pow, hx', hy']
  simpa only [map_mul, map_inv] using congrArg (alternatingActor d.naturalQuotient) hn

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.PermittedChoice.ActorOrbits

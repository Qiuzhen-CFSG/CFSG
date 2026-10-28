module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement.Source.Images
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Pencils

/-!
# The incident seed and its full-actor orbit

The image of the first layer at d is fixed by the incident core, by the
original first-layer commutator bound. Every incident first layer is a
conjugate of that seed under the full opposite actor. The checked three-neighbor
generation therefore spans all of Y/Z_alpha. Along with the actual U image
and its invariance and displacement bounds, this constructs the source pencil.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement.Source
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {i : Bool} {d : M}
  {marking : ParabolicMarking source i d}
namespace QuotientModule
variable (b : QuotientModule source i d marking)

/-- The image of the first layer at the same incident flag. -/
noncomputable def seed : Submodule (ZMod 2) b.Space := b.image (firstFlagLayer (R := R) d)

/-- The original first-core commutator bound fixes the seed modulo Z_alpha. -/
theorem seed_fixed (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (hkernel : flagKernel source i = Q R (beta R)) :
    b.seed ≤ fixedSpace b.representation incidentCore := by
  intro v hv k
  obtain ⟨x, hx, rfl⟩ := (b.mem_image _ v).mp hv
  obtain ⟨a, ha, he⟩ := (show (k : Actor) ∈
      ((localFlagKernel source i d).subgroupOf (localFlagActor source (!i) d)).map
        marking.hom by rw [marking.incident_image]; exact k.property)
  have hc : ⁅localFlagKernel source i d, firstFlagLayer (R := R) d⁆ ≤ Z R (alpha R) := by
    rw [commutator_comm]
    exact (firstFlagLayer_commutator_le_localFlagZ source geometry common early i hkernel d).trans
      inf_le_left
  have hk : conjugate a x * x⁻¹ ∈ b.coordinates.ker := by
    rw [b.kernel]
    exact commutator_le.mp hc a ha x hx
  have hh := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hk)
  rw [b.commutator_coordinates, he] at hh
  exact sub_eq_zero.mp hh

/-- Each incident first layer is a translate of the seed under the full local actor. -/
theorem incident_image_le_orbit [Finite M] (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (hkernel : flagKernel source i = Q R (beta R))
    (g : M) (hinc : flagIncident source i g d) :
    b.image (firstFlagLayer (R := R) g) ≤ ⨆ a : Actor, b.seed.map (b.representation a) := by
  obtain ⟨m, hgm, hdm⟩ := hinc
  have hgm' : firstFlagLayer (R := R) g = firstFlagLayer (R := R) m := by
    have h := firstFlagLayer_right_mul_of_kernel source geometry hlarge i hkernel g (g⁻¹ * m) hgm
    simpa only [mul_inv_cancel_left] using h.symm
  let c := m * d⁻¹
  have hc : embedM R c ∈ localFlagActor source (!i) d := by
    refine ⟨embedM R (d⁻¹ * m), mem_map_of_mem _ hdm, ?_⟩
    change embedM R d * embedM R (d⁻¹ * m) * (embedM R d)⁻¹ = embedM R c
    simp only [map_mul, map_inv, mul_inv_cancel_left, c]
  let a : localFlagActor source (!i) d := ⟨embedM R c, hc⟩
  have he : localConjugate (firstFlagLayer (R := R) d) c = firstFlagLayer (R := R) m := by
    change localConjugate (localConjugate (V R (beta R)) d) c = _
    rw [← localConjugate_mul]
    simp only [c, inv_mul_cancel_right]
    rfl
  have hf : firstFlagLayer (R := R) d ≤ Y source i d :=
    first_le_Y source i d d ⟨d, by rw [inv_mul_cancel]; exact one_mem _,
      by rw [inv_mul_cancel]; exact one_mem _⟩
  intro v hv
  obtain ⟨x, hx, rfl⟩ := (b.mem_image _ v).mp hv
  rw [hgm', ← he] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  let z : Y source i d := ⟨y, hf hy⟩
  apply (le_iSup (fun a : Actor => b.seed.map (b.representation a)) (marking.hom a))
  apply Submodule.mem_map.mpr
  refine ⟨(b.coordinates z).toAdd, (b.mem_image _ _).mpr ⟨z, hy, rfl⟩, ?_⟩
  exact (b.action a z x hyx.symm).symm

/-- The genuine three-neighbor generation spans the entire quotient. -/
theorem seed_generated [Finite M] (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (hkernel : flagKernel source i = Q R (beta R)) :
    (⨆ a : Actor, b.seed.map (b.representation a)) = ⊤ := by
  let T : Submodule (ZMod 2) b.Space := ⨆ a : Actor, b.seed.map (b.representation a)
  let B := (T.toAddSubgroup.toSubgroup.comap b.coordinates).map (Y source i d).subtype
  have hYB : Y source i d ≤ B := by
    obtain ⟨g, hinc, hgen, _⟩ := exists_three_layers source geometry hlarge i hkernel d
    rw [hgen]
    apply iSup_le
    intro j x hx
    let xY : Y source i d := ⟨x, first_le_Y source i (g j) d (hinc j) hx⟩
    refine ⟨xY, ?_, rfl⟩
    exact b.incident_image_le_orbit geometry hlarge hkernel (g j) (hinc j)
      ((b.mem_image _ _).mpr ⟨xY, hx, rfl⟩)
  apply top_unique
  intro v _
  obtain ⟨x, hx⟩ := b.onto (Multiplicative.ofAdd v)
  obtain ⟨y, hy, hyx⟩ := hYB x.property
  have he : y = x := Subtype.ext hyx
  subst y
  change (b.coordinates x).toAdd ∈ T at hy
  have hxv : (b.coordinates x).toAdd = v := congrArg Multiplicative.toAdd hx
  rw [hxv] at hy
  exact hy

/-- The pencil comes from the actual incident seed and actual U image. -/
noncomputable def pencil [Finite M] (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (hkernel : flagKernel source i = Q R (beta R)) :
    Pencil b.representation (b.image (secondFlagLayer source i d)) where
  seed := b.seed
  invariant := b.image_invariant _
    (Incident.secondFlagLayer_normalized source geometry common.large_distance i d)
  core_displacement := b.core_displacement geometry common early hkernel
  seed_fixed := b.seed_fixed geometry common early hkernel
  generated := b.seed_generated geometry common.large_distance hkernel

end QuotientModule
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement.Source

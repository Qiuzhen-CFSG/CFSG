module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Reductions

/-!
# Transfer from the pencil module to the source commutator

Coordinates with exact kernel Z_alpha turn linear preimages into actual
subgroups of Y. The ambient conjugation equation sends commutators to
linear displacements. In particular, centralization of D by the local core
means that the full-actor fixed preimage in the pencil is core-fixed.

An explicit pencil calculation then makes [Y,core] fixed by the full actor,
contradicting the transported genuine source triple. Combined with Residual,
this gives both noncontainments conditionally on the source action and the
abstract pencil calculation. Those two inputs are not constructed here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {i : Bool} {d : M}

namespace SourceAction
variable (b : SourceAction source i d)

private noncomputable def preimage (A : Submodule (ZMod 2) b.Space) : Subgroup (FreeAmalgam R) :=
  (A.toAddSubgroup.toSubgroup.comap b.coordinates).map (Y source i d).subtype

private theorem mem_preimage (A : Submodule (ZMod 2) b.Space) (y : Y source i d) :
    (y : FreeAmalgam R) ∈ b.preimage A ↔ (b.coordinates y).toAdd ∈ A := by
  constructor
  · rintro ⟨z, hz, he⟩
    have hzy : z = y := Subtype.ext he
    subst z
    exact hz
  · intro hy
    exact ⟨y, hy, rfl⟩

private theorem preimage_mono {A B : Submodule (ZMod 2) b.Space} (h : A ≤ B) :
    b.preimage A ≤ b.preimage B := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

private theorem preimage_top : b.preimage ⊤ = Y source i d := by
  simp [preimage]
  rw [← MonoidHom.range_eq_map, range_subtype]

private theorem preimage_bot : b.preimage ⊥ = Z R (alpha R) := by
  change b.coordinates.ker.map (Y source i d).subtype = _
  rw [b.kernel, map_subgroupOf_eq_of_le (Z_le_Y source i d)]

private def conjugate (g : localFlagActor source (!i) d) (x : Y source i d) :
    Y source i d :=
  ⟨(g : FreeAmalgam R) * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
    (mem_normalizer_iff.mp (Y_normalized source i d g.property) x).mp x.property⟩

private theorem commutator_coordinates (g : localFlagActor source (!i) d)
    (x : Y source i d) :
    (b.coordinates (conjugate g x * x⁻¹)).toAdd =
      b.representation (b.marking g) (b.coordinates x).toAdd - (b.coordinates x).toAdd := by
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv,
    ← sub_eq_add_neg]
  rw [b.action g x (conjugate g x) rfl]

private theorem commutator_preimage_le (A : Submodule (ZMod 2) b.Space)
    (E : Subgroup (FreeAmalgam R)) (hEP : E ≤ localFlagActor source (!i) d) :
    ⁅b.preimage A, E⁆ ≤ b.preimage
      (subspaceCommutator b.representation A
        ((E.subgroupOf (localFlagActor source (!i) d)).map b.marking)) := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let a : localFlagActor source (!i) d := ⟨g, hEP hg⟩
  apply (b.mem_preimage _ (conjugate a y * y⁻¹)).mpr
  rw [commutator_coordinates]
  exact Submodule.subset_span ⟨b.marking a, ⟨a, hg, rfl⟩,
    (b.coordinates y).toAdd, hy, rfl⟩

private theorem full_image :
    (((localFlagActor source (!i) d).subgroupOf (localFlagActor source (!i) d)).map
      b.marking) = ⊤ := by
  rw [subgroupOf_self, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr b.marking_onto]

private theorem fixedModulo_le_fixed_of_D_core_le
    (h : ⁅D source i d, localFlagKernel source (!i) d⁆ ≤ Z R (alpha R)) :
    fixedModulo b.representation b.layer ≤ fixedSpace b.representation modelCore := by
  intro v hv k
  obtain ⟨y, hy⟩ := b.onto (Multiplicative.ofAdd v)
  have hyv : (b.coordinates y).toAdd = v := congrArg Multiplicative.toAdd hy
  have hyD : (y : FreeAmalgam R) ∈ D source i d :=
    (b.fixed_preimage y).mp (hyv ▸ hv)
  obtain ⟨a, ha, hka⟩ := (show (k : Actor) ∈
      ((localFlagKernel source (!i) d).subgroupOf
        (localFlagActor source (!i) d)).map b.marking by
    rw [b.core_image]
    exact k.property)
  have hc : conjugate a y * y⁻¹ ∈ b.coordinates.ker := by
    rw [b.kernel]
    exact (show ⁅localFlagKernel source (!i) d, D source i d⁆ ≤ Z R (alpha R) by
      rwa [commutator_comm]) (commutator_mem_commutator ha hyD)
  have he : (b.coordinates (conjugate a y * y⁻¹)).toAdd = 0 :=
    congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hc)
  rw [commutator_coordinates, hyv, hka] at he
  exact sub_eq_zero.mp he

private theorem triple_le_of_fixedModulo_calculation
    (hcalc : fixedModulo b.representation b.layer ≤ fixedSpace b.representation modelCore →
      subspaceCommutator b.representation ⊤ modelCore ≤ fixedSpace b.representation ⊤)
    (h : ⁅D source i d, localFlagKernel source (!i) d⁆ ≤ Z R (alpha R)) :
    ⁅⁅Y source i d, localFlagKernel source (!i) d⁆,
      localFlagActor source (!i) d⁆ ≤ Z R (alpha R) := by
  have hk := b.commutator_preimage_le ⊤ (localFlagKernel source (!i) d)
    (map_mono (flagKernel_le source (!i)))
  rw [b.preimage_top, b.core_image] at hk
  have hfirst : ⁅Y source i d, localFlagKernel source (!i) d⁆ ≤
      b.preimage (fixedSpace b.representation ⊤) :=
    hk.trans (b.preimage_mono (hcalc (b.fixedModulo_le_fixed_of_D_core_le h)))
  have ht := b.commutator_preimage_le (fixedSpace b.representation ⊤)
    (localFlagActor source (!i) d) le_rfl
  rw [b.full_image,
    (subspaceCommutator_eq_bot_iff b.representation
      (fixedSpace b.representation ⊤) ⊤).mpr le_rfl, b.preimage_bot] at ht
  exact (commutator_mono hfirst le_rfl).trans ht

/-- The exact source action and the separate pencil calculation contradict claim (3). -/
theorem D_core_commutator_not_le_of_calculation
    (geometry : Geometry R) (p : SourceFlagPreparatoryData source geometry i)
    (hcalc : fixedModulo b.representation b.layer ≤ fixedSpace b.representation modelCore →
      subspaceCommutator b.representation ⊤ modelCore ≤ fixedSpace b.representation ⊤) :
    ¬ ⁅D source i d, localFlagKernel source (!i) d⁆ ≤ Z R (alpha R) := by
  intro h
  exact Y_core_triple_not_le source geometry i p d
    (b.triple_le_of_fixedModulo_calculation hcalc h)

/-- Conditional final assembly of both movement conclusions. The action
presentation and the pencil calculation remain explicit until constructed. -/
theorem displacement_and_residual_not_le_of_calculation [Finite M]
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : SourceFlagPreparatoryData source geometry i)
    (hcalc : fixedModulo b.representation b.layer ≤ fixedSpace b.representation modelCore →
      subspaceCommutator b.representation ⊤ modelCore ≤ fixedSpace b.representation ⊤) :
    (¬ ⁅D source i d, localFlagKernel source (!i) d⁆ ≤ Z R (alpha R)) ∧
      ¬ ⁅X source i d, localFlagResidual source (!i) d⁆ ≤ Z R (alpha R) := by
  have h := b.D_core_commutator_not_le_of_calculation geometry p hcalc
  exact ⟨h, (X_residual_commutator_not_le_iff_D_core_commutator_not_le
    source geometry common early i d).mpr h⟩

end SourceAction
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement

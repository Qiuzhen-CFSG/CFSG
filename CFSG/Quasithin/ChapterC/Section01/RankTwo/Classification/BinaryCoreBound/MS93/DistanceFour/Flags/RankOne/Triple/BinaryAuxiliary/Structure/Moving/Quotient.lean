module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Quotient

/-!
# The genuine binary auxiliary quotient and its action

The early radius commutator and square bounds make the literal quotient
Y_delta/U_delta elementary abelian. Relative normalization constructs the
full actor's conjugation action on that quotient. `auxiliaryModule` retains
the onto projection, its exact kernel and the ambient conjugation equation.
Its image-cardinality and action-kernel lemmas translate back to relative
indices and commutators of the original subgroups.

These constructions do not assert naturality of the moving part. That
requires the separate geometric displacement comparison and binary
representation recognition.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
universe u
variable {M : Type u} [Group M] {L R : Subgroup M}

/-- Normality is inside Y, not inside the free amalgam. -/
theorem quotient_normal [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (d : M) :
    ((secondFlagLayer source i d).subgroupOf (Y source i d)).Normal :=
  normal_subgroupOf_of_le_normalizer (Y_normalizes_second source geometry hlarge i d)

/-- The actual auxiliary quotient is elementary abelian. -/
theorem quotient_elementary [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (d : M) :
    letI := quotient_normal source geometry common.large_distance i d
    IsElementaryAbelian 2
      (Y source i d ⧸ (secondFlagLayer source i d).subgroupOf (Y source i d)) := by
  let := quotient_normal source geometry common.large_distance i d
  let H := Y source i d
  let N := (secondFlagLayer source i d).subgroupOf H
  have hc : _root_.commutator H ≤ N := by
    intro x hx
    have hh := mem_map_of_mem H.subtype hx
    rw [map_subtype_commutator] at hh
    exact Z_le_secondFlagLayer source i d (((commutator_mono (Y_le_radius source i d)
      ((Y_le_radius source i d).trans (V_le_Q geometry common.large_distance _ rfl))).trans
        (early.commutator_le_Z _ rfl)) hh)
  let : IsMulCommutative (H ⧸ N) := Normal.quotient_commutative_iff_commutator_le.mpr hc
  refine { exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Z_le_secondFlagLayer source i d
    (Propagation.radius_square_mem_Z common early ⟨y, Y_le_radius source i d y.property⟩)

/-- An exact presentation of Y/U carrying its original full-actor conjugation. -/
structure AuxiliaryModule (source : LocalSource L R) (i : Bool) (d : M) where
  Space : Type u
  [addCommGroup : AddCommGroup Space]
  [module : Module (ZMod 2) Space]
  [finite : Finite Space]
  representation : Representation (ZMod 2) (localFlagActor source (!i) d) Space
  projection : Y source i d →* Multiplicative Space
  onto : Function.Surjective projection
  kernel : projection.ker = (secondFlagLayer source i d).subgroupOf (Y source i d)
  action : ∀ (a : localFlagActor source (!i) d) (x y : Y source i d),
    (y : FreeAmalgam R) = (a : FreeAmalgam R) * (x : FreeAmalgam R) *
      (a : FreeAmalgam R)⁻¹ →
    (projection y).toAdd = representation a (projection x).toAdd

attribute [instance] AuxiliaryModule.addCommGroup AuxiliaryModule.module AuxiliaryModule.finite

/-- The carrier is constructed as the literal quotient, rather than postulated. -/
noncomputable def auxiliaryModule [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (d : M) : AuxiliaryModule source i d := by
  let H := Y source i d
  let N := (secondFlagLayer source i d).subgroupOf H
  let : N.Normal := quotient_normal source geometry common.large_distance i d
  let : IsElementaryAbelian 2 (H ⧸ N) := quotient_elementary source geometry common early i d
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite H := Finite.of_injective
    (inclusion ((Y_le_radius source i d).trans (geometry.V_local _ rfl common.large_distance)))
    (inclusion_injective _)
  let D := H ⧸ N
  let h := exists_quotient_conjugation_action (localFlagActor source (!i) d) H
    (secondFlagLayer source i d) (Y_normalized source i d)
    (Incident.secondFlagLayer_normalized source geometry common.large_distance i d) inferInstance
  let a := Classical.choose h
  have ha := Classical.choose_spec h
  let : MulDistribMulAction (localFlagActor source (!i) d) D := MulDistribMulAction.compHom D a
  let ρ : Representation (ZMod 2) (localFlagActor source (!i) d) (Additive D) :=
    Representation.ofElementaryAbelianAction
  let p : H →* Multiplicative (Additive D) :=
    (MulEquiv.multiplicativeAdditive (H := D)).symm.toMonoidHom.comp (QuotientGroup.mk' N)
  exact {
    Space := Additive D
    representation := ρ
    projection := p
    onto := (MulEquiv.multiplicativeAdditive (H := D)).symm.surjective.comp
      (QuotientGroup.mk'_surjective N)
    kernel := (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' N)
      (MulEquiv.multiplicativeAdditive (H := D)).symm.toMonoidHom
      (MulEquiv.multiplicativeAdditive (H := D)).symm.injective).trans (QuotientGroup.ker_mk' N)
    action := by
      intro g x y hy
      change QuotientGroup.mk' N y = a g (QuotientGroup.mk' N x)
      rw [ha]
      congr 1
      exact Subtype.ext hy }


namespace AuxiliaryModule
variable {source : LocalSource L R} {i : Bool} {d : M}

/-- Image in the actual auxiliary quotient, with a lift in the named ambient subgroup. -/
noncomputable def image (b : AuxiliaryModule source i d) (A : Subgroup (FreeAmalgam R)) :
    Submodule (ZMod 2) b.Space :=
  AddSubgroup.toZModSubmodule 2 ((A.subgroupOf (Y source i d)).map b.projection).toAddSubgroup

/-- Relative index is precisely the cardinality of the image under the quotient map. -/
theorem image_card (b : AuxiliaryModule source i d) (A : Subgroup (FreeAmalgam R))
    (hA : A ≤ Y source i d) :
    Nat.card (image b A) = (secondFlagLayer source i d).relIndex A := by
  let J := A.subgroupOf (Y source i d)
  have hc : Nat.card (image b A) = Nat.card (J.map b.projection) := rfl
  rw [hc, ← relIndex_ker, b.kernel, relIndex_subgroupOf hA]

/-- The kernel of the genuine quotient action means literal commutator containment. -/
theorem kernel_iff (b : AuxiliaryModule source i d) (E : Subgroup (FreeAmalgam R))
    (hE : E ≤ localFlagActor source (!i) d) :
    E.subgroupOf (localFlagActor source (!i) d) ≤ b.representation.ker ↔
      ⁅Y source i d, E⁆ ≤ secondFlagLayer source i d := by
  have hnorm := Y_normalized source i d
  let conj (g : localFlagActor source (!i) d) (x : Y source i d) : Y source i d :=
    ⟨(g : FreeAmalgam R) * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
      (mem_normalizer_iff.mp (hnorm g.property) x).mp x.property⟩
  constructor
  · intro h
    rw [commutator_comm]
    apply commutator_le.mpr
    intro g hg x hx
    let a : localFlagActor source (!i) d := ⟨g, hE hg⟩
    let v : Y source i d := ⟨x, hx⟩
    have hr : b.representation a = 1 := h hg
    have he : b.projection (conj a v) = b.projection v := by
      have hh := b.action a v (conj a v) rfl
      rw [hr] at hh
      exact hh
    have hk : conj a v * v⁻¹ ∈ b.projection.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    rw [b.kernel] at hk
    exact hk
  · intro h g hg
    apply MonoidHom.mem_ker.mpr
    ext v
    change b.representation g v = v
    obtain ⟨x, hx⟩ := b.onto (Multiplicative.ofAdd v)
    have hv : (b.projection x).toAdd = v := congrArg Multiplicative.toAdd hx
    have hk : conj g x * x⁻¹ ∈ b.projection.ker := by
      rw [b.kernel]
      have hEY : ⁅E, Y source i d⁆ ≤ secondFlagLayer source i d := by
        rwa [commutator_comm]
      exact commutator_le.mp hEY g hg x x.property
    have he : b.projection (conj g x) = b.projection x := by
      simpa only [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] using hk
    rw [← hv, ← b.action g x (conj g x) rfl]
    exact congrArg Multiplicative.toAdd he

end AuxiliaryModule

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving

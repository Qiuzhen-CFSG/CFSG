module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement.Source.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Quotient
public import Theory.Representation.ElementaryAbelianAction

/-!
# The literal quotient Y/Z_alpha and descent of its full action

The early radius bounds make Y/Z_alpha elementary abelian. Conjugation by
the full local actor acts on this quotient; [Y,Q_alpha] <= Z_alpha kills
the exact kernel of a compatible parabolic marking. Descent therefore
constructs a linear action of the literal point parabolic, preserving the
original conjugation equation and the coordinate map's exact kernel.

No natural-module or nonvanishing assertion is used.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement.Source

universe u
variable {M : Type u} [Group M] {L R : Subgroup M}

/-- Only relative normality inside Y is needed for the quotient. -/
theorem denominator_normal (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (d : M) :
    ((Z R (alpha R)).subgroupOf (Y source i d)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (((Y_le_radius source i d).trans (geometry.V_local _ rfl hlarge)).trans
      (Z_normalized R _))

/-- The actual source quotient is elementary abelian from the early bounds. -/
theorem quotient_elementary (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (d : M) :
    letI := denominator_normal source geometry common.large_distance i d
    IsElementaryAbelian 2 (Y source i d ⧸ (Z R (alpha R)).subgroupOf (Y source i d)) := by
  let := denominator_normal source geometry common.large_distance i d
  let H := Y source i d
  let N := (Z R (alpha R)).subgroupOf H
  have hc : _root_.commutator H ≤ N := by
    intro x hx
    have hh := mem_map_of_mem H.subtype hx
    rw [map_subtype_commutator] at hh
    exact ((commutator_mono (Y_le_radius source i d)
      ((Y_le_radius source i d).trans (V_le_Q geometry common.large_distance _ rfl))).trans
        (early.commutator_le_Z _ rfl)) hh
  let : IsMulCommutative (H ⧸ N) := Normal.quotient_commutative_iff_commutator_le.mpr hc
  refine { exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Propagation.radius_square_mem_Z common early ⟨y, Y_le_radius source i d y.property⟩

/-- Construct the quotient and descend its genuine conjugation action through
the original Q_alpha kernel. The marking is supplied separately. -/
noncomputable def quotientModule [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool) (d : M)
    (marking : ParabolicMarking source i d) : QuotientModule source i d marking := by
  let H := Y source i d
  let N := (Z R (alpha R)).subgroupOf H
  let : N.Normal := denominator_normal source geometry common.large_distance i d
  let : IsElementaryAbelian 2 (H ⧸ N) := quotient_elementary source geometry common early i d
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite H := Finite.of_injective
    (inclusion ((Y_le_radius source i d).trans (geometry.V_local _ rfl common.large_distance)))
    (inclusion_injective _)
  let B := H ⧸ N
  let h := exists_quotient_conjugation_action (localFlagActor source (!i) d) H
    (Z R (alpha R)) (Y_normalized source i d)
    ((localFlagActor_le_stabilizer source (!i) d).trans (Z_normalized R _)) inferInstance
  let a := Classical.choose h
  have ha := Classical.choose_spec h
  have hkill : marking.hom.ker ≤ a.ker := by
    rw [marking.kernel]
    exact quotient_conjugation_action_kills_commutator_layer _ H (Z R (alpha R))
      (Q R (alpha R)) inferInstance (Y_normalized source i d)
      ((commutator_mono (Y_le_radius source i d) le_rfl).trans
        (early.commutator_le_Z _ rfl)) a ha
  let descended : Actor →* MulAut B := marking.hom.liftOfSurjective marking.onto ⟨a, hkill⟩
  have hdesc (g : localFlagActor source (!i) d) : descended (marking.hom g) = a g :=
    marking.hom.liftOfRightInverse_comp_apply _ _ ⟨a, hkill⟩ g
  let : MulDistribMulAction Actor B := MulDistribMulAction.compHom B descended
  let ρ : Representation (ZMod 2) Actor (Additive B) := Representation.ofElementaryAbelianAction
  let p : H →* Multiplicative (Additive B) :=
    (MulEquiv.multiplicativeAdditive (H := B)).symm.toMonoidHom.comp (QuotientGroup.mk' N)
  exact {
    Space := Additive B
    representation := ρ
    coordinates := p
    onto := (MulEquiv.multiplicativeAdditive (H := B)).symm.surjective.comp
      (QuotientGroup.mk'_surjective N)
    kernel := (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' N)
      (MulEquiv.multiplicativeAdditive (H := B)).symm.toMonoidHom
      (MulEquiv.multiplicativeAdditive (H := B)).symm.injective).trans (QuotientGroup.ker_mk' N)
    action := by
      intro g x y hy
      change QuotientGroup.mk' N y = descended (marking.hom g) (QuotientGroup.mk' N x)
      rw [hdesc, ha]
      congr 1
      exact Subtype.ext hy }

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement.Source

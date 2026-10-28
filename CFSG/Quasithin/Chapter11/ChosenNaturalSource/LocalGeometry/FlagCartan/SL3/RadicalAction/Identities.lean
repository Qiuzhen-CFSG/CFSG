module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.RadicalAction.Action

/-!
# Original SL₃ radical commutators and fixed subgroups

The proved vanishing of C_V(L) identifies V itself with the marked natural
three-space. The original group commutator becomes the vector displacement
under the same alignment. The full shear family has both its displacement
span and its common fixed space equal to the plane. Thus [V,R₂] and C_V(R₂)
are exactly V₂, before any quotient is taken.

The final application supplies centralization and commutator containment for
every actual A ≤ R₂, the local inputs used after that inclusion in 11.2.4.
No offender or weak-closure assertion is assumed or proved here.

Source: Aschbacher--Smith, 11.2.4, printed pp.769--770.
-/

open Subgroup Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative commutatorElement
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.RadicalAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The subgroup commutator in the original V, with the left conjugation convention. -/
def vectorCommutator (r : (flag D S m).Ri 1) (v : V) : V :=
  V.normalizerMonoidHom (inclusion (ambientJoin_normalizes_seed D S)
    (radicalInclusion D S m r)) v * v⁻¹

theorem vectorCommutator_coe (r : (flag D S m).Ri 1) (v : V) :
    (vectorCommutator D S m r v : G) = ⁅(r : G),(v : G)⁆ := rfl

theorem vectorCommutator_coordinates (r : (flag D S m).Ri 1) (v : V) :
    (vectorEquiv D S m (vectorCommutator D S m r v)).toAdd =
      radicalOperator D S m r (vectorEquiv D S m v).toAdd -
        (vectorEquiv D S m v).toAdd := by
  rw [vectorCommutator,map_mul,map_inv]
  change (vectorEquiv D S m (V.normalizerMonoidHom _ v)).toAdd +
    -(vectorEquiv D S m v).toAdd = _
  rw [←sub_eq_add_neg,alignedAction_projection]
  rfl

/-- The complete original commutator subgroup, rather than only its quotient image. -/
theorem commutator_eq_plane : ⁅V,(flag D S m).Ri 1⁆ = (flag D S m).Vi 1 := by
  rw [commutator_comm V]
  apply le_antisymm
  · apply commutator_le.mpr
    intro r hr v hv
    let r' : (flag D S m).Ri 1 := ⟨r,hr⟩
    let v' : V := ⟨v,hv⟩
    change (vectorCommutator D S m r' v' : G) ∈ (flag D S m).Vi 1
    apply (vectorEquiv_mem_plane D S m _).mpr
    rw [vectorCommutator_coordinates]
    obtain ⟨a,b,h⟩ := radicalOperator_shear D S m r'
    rw [h]
    simp
  · intro w hw
    let w' : V := ⟨w,D.centralQuotientPreimage_le _ hw⟩
    let u := (vectorEquiv D S m w').toAdd
    have hu : u 2 = 0 := (vectorEquiv_mem_plane D S m w').mp hw
    obtain ⟨r,hr⟩ := radicalOperator_realizes D S m (u 0) (u 1)
    obtain ⟨v,hv⟩ := (vectorEquiv D S m).surjective (Multiplicative.ofAdd ![0,0,1])
    have he : vectorCommutator D S m r v = w' := by
      apply (vectorEquiv D S m).injective
      apply Multiplicative.toAdd.injective
      rw [vectorCommutator_coordinates,hv,hr]
      change _ = u
      ext i
      fin_cases i <;> simp [hu]
    have hc := commutator_mem_commutator r.property v.property
    rw [← vectorCommutator_coe D S m,he] at hc
    exact hc

/-- The fixed subgroup of the whole original radical is the original plane. -/
theorem fixed_eq_plane : V ⊓ centralizer ((flag D S m).Ri 1 : Set G) = (flag D S m).Vi 1 := by
  apply le_antisymm
  · intro v hv
    let v' : V := ⟨v,hv.1⟩
    obtain ⟨r,hr⟩ := radicalOperator_realizes D S m 1 0
    have he : vectorCommutator D S m r v' = 1 := by
      apply Subtype.ext
      rw [vectorCommutator_coe]
      exact commutatorElement_eq_one_iff_commute.mpr
        (show Commute (r : G) v from hv.2 r r.property)
    have hh := congrFun (vectorCommutator_coordinates D S m r v') 0
    rw [he,map_one,hr] at hh
    have hz : (vectorEquiv D S m v').toAdd 2 = 0 := by
      simpa using hh.symm
    exact (vectorEquiv_mem_plane D S m v').mpr hz
  · exact le_inf (D.centralQuotientPreimage_le _)
      (le_centralizer_iff.mp (radical_centralizes_plane D S m))

/-- Both local facts used after A ≤ R₂ in source 11.2.4, on the original subgroups. -/
theorem subgroup_action {A : Subgroup G} (hA : A ≤ (flag D S m).Ri 1) :
    A ≤ centralizer ((flag D S m).Vi 1 : Set G) ∧ ⁅V,A⁆ ≤ (flag D S m).Vi 1 := by
  refine ⟨subgroup_centralizes_plane D S m hA,?_⟩
  exact (commutator_mono le_rfl hA).trans_eq (commutator_eq_plane D S m)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.RadicalAction

module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Reductions

/-!
# The fixed and moving summands in the midpoint comparison

The coordinate map of the natural X factor shows X is not contained in its
central denominator. Consequently D properly contains U. A vector fixed by
all of SL2(2) is zero, so D meets the moving natural summand only in U.
Transitivity of the full opposite actor on incident first layers then shows
that every first layer escapes that summand. These are the D > U deductions
used to obtain the central-layer containment at the midpoint.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), printed p.907, paragraph beginning “Hence q = 2”.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary

private theorem binary_fixed_zero : ∀ v : Fin 2 → ZMod 2,
    (∀ a : SL2, a.val.mulVec v = v) → v = 0 := by decide

private theorem factor_not_le_denominator {G : Type*} [Group G]
    {P H N : Subgroup G} (n : RankOnePairing.RankOneFactor P H N) : ¬ H ≤ N := by
  intro h
  obtain ⟨y, hy⟩ := n.coordinates_surjective (Multiplicative.ofAdd (1 : Fin 2 → ZMod 2))
  have hk : y ∈ n.coordinates.ker := n.kernel.symm ▸ h y.property
  have he := MonoidHom.mem_ker.mp hk
  rw [hy] at he
  have hv := congrArg (fun w : Multiplicative (Fin 2 → ZMod 2) => w.toAdd 0) he
  exact (by decide : (1 : ZMod 2) ≠ 0) hv

private theorem factor_fixed_le_denominator {G : Type*} [Group G]
    {P H N S : Subgroup G} (n : RankOnePairing.RankOneFactor P H N)
    (hSH : S ≤ H) (hcomm : ⁅S,P⁆ ≤ N) : S ≤ N := by
  intro x hx
  let u : H := ⟨x, hSH hx⟩
  have hfixed : ∀ a : SL2, a.val.mulVec (n.coordinates u).toAdd = (n.coordinates u).toAdd := by
    intro a
    obtain ⟨p,hp⟩ := n.surjective a
    let v : H := ⟨(p : G) * x * (p : G)⁻¹,
      (mem_normalizer_iff.mp (n.normalized p.property) _).mp u.property⟩
    have hk : v * u⁻¹ ∈ n.coordinates.ker := by
      rw [n.kernel]
      exact (commutator_comm S P ▸ hcomm) (commutator_mem_commutator p.property hx)
    have he : n.coordinates v = n.coordinates u := by
      have he := MonoidHom.mem_ker.mp hk
      rwa [map_mul, map_inv, mul_inv_eq_one] at he
    have ha := n.action p u v rfl
    rw [hp,he] at ha
    exact ha.symm
  have hk : u ∈ n.coordinates.ker := by
    apply MonoidHom.mem_ker.mpr
    apply Multiplicative.toAdd.injective
    exact binary_fixed_zero _ hfixed
  rw [n.kernel] at hk
  exact hk

variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The actual natural X factor forces the full-actor fixed preimage D to
properly contain U. Otherwise its defining core commutator lies in Z_alpha. -/
theorem D_not_le_second_of_XFactor (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (d : M) (x : XFactor source i d) :
    ¬ D source i d ≤ secondFlagLayer source i d := by
  intro h
  apply factor_not_le_denominator x.val
  exact sup_le ((commutator_mono h le_rfl).trans
    (Incident.secondFlagLayer_commutator_le_Z source geometry hlarge i d)) le_rfl

variable [Finite M]

/-- The fixed preimage meets the moving natural summand only in U. -/
theorem D_inf_moving_le_second (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (d : M) (moving : MovingFactor source i d) :
    D source i d ⊓ (⁅Y source i d, localFlagActor source (!i) d⁆ ⊔
      secondFlagLayer source i d) ≤ secondFlagLayer source i d := by
  exact factor_fixed_le_denominator moving.val inf_le_right
    ((commutator_mono inf_le_left le_rfl).trans
      (D_commutator_actor source geometry hlarge i d))

/-- Every incident first layer escapes the moving summand. If one lay in it,
full-actor transitivity would put all of Y in it, contradicting D > U. -/
theorem first_not_le_moving (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (natural : FlagNaturalSection source i)
    (d : M) (moving : MovingFactor source i d) (x : XFactor source i d)
    (g : M) (hg : flagIncident source i g d) :
    ¬ firstFlagLayer (R := R) g ≤ ⁅Y source i d, localFlagActor source (!i) d⁆ ⊔
      secondFlagLayer source i d := by
  intro h
  let H := ⁅Y source i d, localFlagActor source (!i) d⁆ ⊔ secondFlagLayer source i d
  have hY : Y source i d ≤ H := by
    apply iSup_le
    intro b
    apply iSup_le
    intro hb
    obtain ⟨a, ha, he⟩ := exists_incident_first_transporter source i natural d g b hg hb
    rw [← he]
    exact (map_mono h).trans_eq (mem_normalizer_iff_map_conj_eq.mp (moving.val.normalized ha))
  exact D_not_le_second_of_XFactor source geometry hlarge i d x
    ((le_inf le_rfl ((D_le_Y source i d).trans hY)).trans
      (D_inf_moving_le_second source geometry hlarge i d moving))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary

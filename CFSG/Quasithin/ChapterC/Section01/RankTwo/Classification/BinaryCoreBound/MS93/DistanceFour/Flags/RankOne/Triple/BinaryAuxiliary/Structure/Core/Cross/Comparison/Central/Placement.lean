module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.Comparison.Central.Index
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Crossing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Nontrivial

/-!
# Placement of the original center at every escaping midpoint flag

Split according to whether the transported second layer lies in the original
opposite core. In the contained case its commutator with U_delta0 lies in
Z_alpha, but escapes Z_middle by the nonzero source triple. Since Z_beta has
index two in Z_alpha and lies in the transported second layer, this forces
all of Z_alpha into that layer. In the crossing case the proved reverse
index comparison and the marked moving action give the required placement.

Both branches use the supplied incident flag and transporter. In particular,
no existential selection or transfer between escaping flags is needed, and
the original and midpoint centers retain their distinct denominators.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), printed p.907, first paragraph and its center containment.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary

private theorem le_of_index_two_and_crossing {G : Type*} [Group G]
    (A B F C : Subgroup G) (hBA : B ≤ A) (hBF : B ≤ F)
    (hi : B.relIndex A = 2) (hCA : C ≤ A) (hCF : C ≤ F)
    (hcross : ¬ C ≤ B) : A ≤ F := by
  have hm := relIndex_mul_relIndex B (A ⊓ F) A (le_inf hBA hBF) inf_le_left
  rw [hi] at hm
  have hn : B.relIndex (A ⊓ F) ≠ 1 :=
    fun h => hcross ((le_inf hCA hCF).trans (relIndex_eq_one.mp h))
  have hd : B.relIndex (A ⊓ F) ∣ 2 := ⟨_, hm.symm⟩
  have he := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hn
  rw [he] at hm
  exact (relIndex_eq_one.mp (by omega : (A ⊓ F).relIndex A = 1)).trans inf_le_right

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- When the transported second layer lies in the original opposite core,
its nontrivial commutator supplies the missing coset of Z_beta in Z_alpha.
This branch needs no marked moving or X factor. -/
theorem middle_center_le_second_of_contained_core
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (e : M) (he : flagIncident source i 1 e)
    (hescape : ¬ secondFlagLayer source i p.delta0 ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom)
    (hcontained : (secondFlagLayer source i e).map t.conjugation.toMonoidHom ≤
      localFlagKernel source (!i) p.delta0) :
    Z R (alpha R) ≤ (secondFlagLayer source i e).map t.conjugation.toMonoidHom := by
  let E := secondFlagLayer source i p.delta0
  let F := (secondFlagLayer source i e).map t.conjugation.toMonoidHom
  let C := ⁅E,F⁆
  have hEP : E ≤ (localFlagActor source (!i) e).map t.conjugation.toMonoidHom :=
    ((secondFlagLayer_le_radius source i p.delta0).trans
      ((V_le_Q geometry common.large_distance _ rfl).trans
        (Q_le_adjacent_h R rfl (base_adjacent R)))).trans
      ((t.map_first_kernel source i hkernel).symm.le.trans
        (map_mono (Incident.flagKernel_le_incidentActor source i e he)))
  have hCA : C ≤ Z R (alpha R) :=
    (commutator_mono le_rfl hcontained).trans
      (Incident.secondFlagLayer_commutator_le_Z source geometry common.large_distance i p.delta0)
  have hCF : C ≤ F := le_normalizer_iff_commutator_le_right.mp
    (hEP.trans ((map_mono
      (Incident.secondFlagLayer_normalized source geometry common.large_distance i e)).trans
        (le_normalizer_map _)))
  have hTF : Z R p.middle ≤ F := by
    rw [← t.map_Z_alpha]
    exact map_mono (Z_le_secondFlagLayer source i e)
  have hcol : color R p.middle = false := by
    have hh := adjacent_color_ne R p.middle_neighbor
    have hbeta : color R (beta R) = true := rfl
    cases hc : color R p.middle <;> simp_all
  have hBT : Z R (beta R) ≤ Z R p.middle :=
    edge_Z_le p.middle (beta R) hcol (adjacent_symm R p.middle_neighbor)
  have hge := Moving.middle_second_commutator_index_ge_two source geometry common early
    i hkernel p t e hEP hescape
  have hCB : ¬ C ≤ Z R (beta R) := by
    intro h
    have hc : (Z R p.middle).relIndex C = 1 := relIndex_eq_one.mpr (h.trans hBT)
    change 2 ≤ (Z R p.middle).relIndex C at hge
    omega
  exact le_of_index_two_and_crossing (Z R (alpha R)) (Z R (beta R)) F C
    (edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)) (hBT.trans hTF)
    (early.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R)) hCA hCF hCB

set_option linter.unusedVariables false in
/-- The original center lies in the moving summand at every supplied flag
whose transported core is escaped by X_delta0. The source interface retains
`hb`, `natural` and `x`; this earlier placement already follows without using
those three additional inputs. -/
theorem middle_center_le_moving_of_X_crossing
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (moving : MovingFactor source i p.delta0) (x : XFactor source i p.delta0)
    (e : M) (he : flagIncident source i 1 e)
    (hcross : ¬ X source i p.delta0 ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom) :
    Z R (alpha R) ≤
      (⁅Y source i e, localFlagActor source (!i) e⁆ ⊔ secondFlagLayer source i e).map
        t.conjugation.toMonoidHom := by
  by_cases hc : (secondFlagLayer source i e).map t.conjugation.toMonoidHom ≤
      localFlagKernel source (!i) p.delta0
  · have hescape : ¬ secondFlagLayer source i p.delta0 ≤
        (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom :=
      fun h => hcross ((X_le_second source geometry common.large_distance i p.delta0).trans h)
    exact (middle_center_le_second_of_contained_core source geometry common early i hkernel
      p t e he hescape hc).trans (map_mono le_sup_right)
  · exact middle_center_le_moving_of_reverse_index source geometry common early i hkernel
      p t moving e he hcross
      (Moving.reverse_comparison_of_second_core_escape source geometry common early
        i hkernel p t e hc)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary

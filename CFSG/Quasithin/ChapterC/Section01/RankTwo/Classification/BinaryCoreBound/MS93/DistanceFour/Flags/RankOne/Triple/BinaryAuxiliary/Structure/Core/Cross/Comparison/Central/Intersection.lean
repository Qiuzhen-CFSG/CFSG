module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.Comparison.Preparation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Escape.FixedPreimage.FirstIntersection

/-!
# The first layer meets the moving plane only in the second layer

In a binary natural plane, a nonidentity actor has at most one nonzero fixed
vector. If the incident first layer met the moving plane nontrivially modulo
U, every fixed vector of that actor in the moving plane would lie in the
first layer times U. Generation by the first layer and the moving subgroup
would give D <= V_beta U. The proved D intersect V_beta <= U would then
force D <= U, contradicting the nonzero natural X factor.

The core crossing is explicit and uses the actual marked actor kernel. No
splitting of the whole Y/U or identification of distinct centers is assumed.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), printed p.907, paragraph beginning “Hence q = 2”.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary

private theorem binary_fixed_line : ∀ (a : SL2) (v w : Fin 2 → ZMod 2),
    (a ≠ 1 ∧ v ≠ 0 ∧ a.val.mulVec v = v ∧ a.val.mulVec w = w) → w = 0 ∨ w = v := by
  decide

private theorem coordinates_fixed {G : Type*} [Group G] {P S U : Subgroup G}
    (n : RankOnePairing.RankOneFactor P S U) (a : P) (v : S)
    (hv : ⁅(a : G), (v : G)⁆ ∈ U) :
    (n.projection a).val.mulVec (n.coordinates v).toAdd = (n.coordinates v).toAdd := by
  let c : S := ⟨(a : G) * (v : G) * (a : G)⁻¹,
    (mem_normalizer_iff.mp (n.normalized a.property) _).mp v.property⟩
  have hk : c * v⁻¹ ∈ n.coordinates.ker := by
    rw [n.kernel]
    exact hv
  have hh := MonoidHom.mem_ker.mp hk
  rw [map_mul, map_inv, mul_inv_eq_one] at hh
  rw [← n.action a v c rfl, hh]

private theorem first_inf_moving_le {G : Type*} [Group G]
    (P Y F U : Subgroup G)
    (n : RankOnePairing.RankOneFactor P (⁅Y,P⁆ ⊔ U) U)
    (hYP : Y ≤ P) (hUY : U ≤ Y) (hPU : P ≤ normalizer U)
    (hgen : Y = F ⊔ ⁅Y,P⁆)
    (hinter : commutatorPreimage Y P U ⊓ F ≤ U)
    (hnot : ¬ commutatorPreimage Y P U ≤ U)
    (a : P) (ha : n.projection a ≠ 1)
    (hFa : ⁅F, zpowers (a : G)⁆ ≤ U) : F ⊓ (⁅Y,P⁆ ⊔ U) ≤ U := by
  let S := ⁅Y,P⁆ ⊔ U
  let D := commutatorPreimage Y P U
  let E := zpowers (a : G)
  have hFY : F ≤ Y := hgen ▸ le_sup_left
  have hYN : Y ≤ normalizer U := hYP.trans hPU
  have hFS : F ≤ normalizer S :=
    (le_inf (hFY.trans (normalizer_commutator_ge_left Y P))
      (hFY.trans hYN)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hgen' : Y = F ⊔ S := by
    dsimp [S]
    rw [← sup_assoc, ← hgen, sup_eq_left.mpr hUY]
  have hEP : E ≤ P := zpowers_le.mpr a.property
  have hUD : U ≤ D := le_commutatorPreimage hUY
    (le_normalizer_iff_commutator_le_left.mp hPU)
  have hFF : F ≤ commutatorPreimage Y E U := le_commutatorPreimage hFY hFa
  have hDF : D ≤ commutatorPreimage Y E U := le_commutatorPreimage
    (commutatorPreimage_le _ _ _)
    ((commutator_mono le_rfl hEP).trans (commutator_commutatorPreimage_le _ _ _ hYN))
  by_contra h
  obtain ⟨v, hv, hvU⟩ := SetLike.not_le_iff_exists.mp h
  let vS : S := ⟨v,hv.2⟩
  have hvn : (n.coordinates vS).toAdd ≠ 0 := by
    intro hz
    apply hvU
    have hk : vS ∈ n.coordinates.ker := by
      apply MonoidHom.mem_ker.mpr
      exact Multiplicative.toAdd.injective hz
    rw [n.kernel] at hk
    exact hk
  have hvfix := coordinates_fixed n a vS
    ((commutator_comm F E ▸ hFa) (commutator_mem_commutator (mem_zpowers _) hv.1))
  have hfixed (s : S) (hs : ⁅(a : G), (s : G)⁆ ∈ U) : (s : G) ∈ F ⊔ U := by
    have hsf := coordinates_fixed n a s hs
    rcases binary_fixed_line _ _ _ ⟨ha, hvn, hvfix, hsf⟩ with hz | he
    · have hk : s ∈ n.coordinates.ker :=
        MonoidHom.mem_ker.mpr (Multiplicative.toAdd.injective hz)
      rw [n.kernel] at hk
      exact mem_sup_right hk
    · have he' : n.coordinates s = n.coordinates vS := Multiplicative.toAdd.injective he
      have hk : s * vS⁻¹ ∈ n.coordinates.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, he', mul_inv_cancel]
      rw [n.kernel] at hk
      have hh := (F ⊔ U).mul_mem (mem_sup_right hk) (mem_sup_left hv.1)
      change (s : G) * v⁻¹ * v ∈ F ⊔ U at hh
      simpa only [inv_mul_cancel_right] using hh
  have hD : D ≤ F ⊔ U := by
    intro d hd
    have hp : d ∈ (F : Set G) * (S : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hFS, ← hgen']
      exact commutatorPreimage_le _ _ _ hd
    obtain ⟨f,hf,s,hs,rfl⟩ := hp
    have hsF : s ∈ commutatorPreimage Y E U := by
      simpa only [inv_mul_cancel_left] using
        (commutatorPreimage Y E U).mul_mem
          ((commutatorPreimage Y E U).inv_mem (hFF hf)) (hDF hd)
    have hcomm := commutator_commutatorPreimage_le Y E U hYN
    rw [commutator_comm] at hcomm
    exact (F ⊔ U).mul_mem (mem_sup_left hf)
      (hfixed ⟨s,hs⟩ (hcomm (commutator_mem_commutator (mem_zpowers _) hsF)))
  apply hnot
  intro d hd
  have hp : d ∈ (F : Set G) * (U : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ (hFY.trans hYN)]
    exact hD hd
  obtain ⟨f,hf,u,hu,rfl⟩ := hp
  have hfD : f ∈ D := by
    simpa only [mul_inv_cancel_right] using D.mul_mem hd (D.inv_mem (hUD hu))
  exact U.mul_mem (hinter ⟨hfD,hf⟩) hu

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

omit [Finite M] in
private theorem first_generation (source : LocalSource L R) (i : Bool)
    (natural : FlagNaturalSection source i) (d : M) (hd : flagIncident source i 1 d) :
    Y source i d = V R (beta R) ⊔ ⁅Y source i d, localFlagActor source (!i) d⁆ := by
  have hFY : V R (beta R) ≤ Y source i d := by
    simpa only [firstFlagLayer, localConjugate_one] using first_le_Y source i 1 d hd
  apply le_antisymm ?_ (sup_le hFY
    (le_normalizer_iff_commutator_le_left.mp (Y_normalized source i d)))
  apply iSup_le
  intro g
  apply iSup_le
  intro hg
  obtain ⟨a,ha,he⟩ := exists_incident_first_transporter source i natural d 1 g hd hg
  rw [← he]
  rintro z ⟨v,hv,rfl⟩
  have hv' : v ∈ V R (beta R) := by
    simpa only [firstFlagLayer, localConjugate_one, SetLike.mem_coe] using hv
  have hc : ⁅embedM R a,v⁆ ∈ ⁅Y source i d,localFlagActor source (!i) d⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator ha (hFY hv')
  have hh := (V R (beta R) ⊔ ⁅Y source i d,localFlagActor source (!i) d⁆).mul_mem
    (mem_sup_right hc) (mem_sup_left hv')
  change embedM R a * v * (embedM R a)⁻¹ ∈ _
  simpa only [commutatorElement_def, inv_mul_cancel_right] using hh

/-- The actual first layer has zero intersection with the moving plane modulo
U when its core has nontrivial image in the opposite marked actor. -/
theorem first_inf_moving_le_second_of_core_crossing
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i) (d : M) (hd : flagIncident source i 1 d)
    (moving : MovingFactor source i d) (x : XFactor source i d)
    (hcross : ¬ Q R (beta R) ≤ localFlagKernel source (!i) d) :
    V R (beta R) ⊓ (⁅Y source i d,localFlagActor source (!i) d⁆ ⊔
      secondFlagLayer source i d) ≤ secondFlagLayer source i d := by
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hcross
  have hQP : Q R (beta R) ≤ localFlagActor source (!i) d :=
    hkernel ▸ Incident.flagKernel_le_incidentActor source i d hd
  let ap : localFlagActor source (!i) d := ⟨a,hQP ha⟩
  have hap : moving.val.projection ap ≠ 1 := by
    intro he
    have hk := MonoidHom.mem_ker.mpr he
    rw [moving.property] at hk
    exact han hk
  apply first_inf_moving_le (localFlagActor source (!i) d) (Y source i d)
    (V R (beta R)) (secondFlagLayer source i d) moving.val
    (Y_le_actor source geometry common.large_distance i d) (second_le_Y source i d)
    (Incident.secondFlagLayer_normalized source geometry common.large_distance i d)
    (first_generation source i natural d hd)
    (D_inf_first_le_second source geometry common early i hkernel d hd)
    (D_not_le_second_of_XFactor source geometry common.large_distance i d x) ap hap
  exact ((commutator_mono le_rfl (zpowers_le.mpr ha)).trans
    (edgeRadius_commutator_le_edgeZ geometry common.large_distance early)).trans
      ((edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)).trans
        (Z_le_secondFlagLayer source i d))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary

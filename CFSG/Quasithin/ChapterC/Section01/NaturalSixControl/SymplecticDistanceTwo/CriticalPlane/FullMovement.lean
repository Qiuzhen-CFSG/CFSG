module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointMovement
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.CriticalPlane.Cardinality
public import Theory.GroupTheory.Commutator.CentralizingComplement
/-!
# Full orbit image generates the opposite critical plane

The full orbit image means A Qc is the common edge kernel. Since Qc
centralizes Zc, the commutator [A,Zc] is [Zc,Qb]. The original natural
moving layer at c has displacement of order eight under that edge kernel,
and its intersection with the edge seed has order at most two. Therefore
[A,Zc]Zb has index at least four over Zb. It is contained in the maximal
critical plane, which has index four, giving equality.

The explicit fullness premise belongs to the strict-offender recognition
argument. Every other premise is supplied by the original native source;
the final theorem uses the literal characteristic replacement.
Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
include s

private theorem movement_edge_coordinates (h : NativeCentralLayer s) {c b : Vertex R}
    (hc : color R c = false) (hcb : Adjacent R c b) :
    ∃ i : M →* FreeAmalgam R, Function.Injective i ∧
      R.map i = Q R b ∧ W.map i ≤ Z R c ∧ (omegaCenter R).map i = Z R b := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
    have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
    have hiR : R.map i = Q R (hVertex R g) := by
      have he := Q_act R g (beta R)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,Q_beta,map_map] using he.symm
    refine ⟨i,hi,hiR,?_,?_⟩
    · have hZ : (W ⊔ omegaCenter R).map i = Z R (mVertex R g) := by
        have he := Z_act R g (alpha R)
        rw [SymplecticSeed.Z_eq_seedHull,s.seedHull_eq_module_sup_seed h] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      exact (map_mono le_sup_left).trans_eq hZ
    · rw [←omegaCenter_map R i hi,hiR]
      simp only [Z,show color R (hVertex R g) = true from rfl,Bool.true_eq_false,if_false,edgeOmega]
  · rw [hg.1] at hc
    cases hc

/-- Full orbit image in the actual edge quotient generates the maximal plane
by its displacement of the opposite layer, together with the edge seed. -/
theorem criticalOrbit_opposite_commutator_sup_edge_eq_plane
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (himage : criticalOrbit R c b ⊔ Q R c = Q R b) :
    ⁅criticalOrbit R c b,Z R c⁆ ⊔ Z R b = criticalPlane R c b := by
  let A := criticalOrbit R c b
  let D := ⁅A,Z R c⁆ ⊔ Z R b
  have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
  have hbpos : 0 < criticalDistance R (alpha R) (s.geometry.exists_critical (alpha R) rfl) := by
    change 0 < s.geometry.b R
    omega
  have hne : core R (alpha R) ≠ U R (alpha R) := by
    intro he
    apply hlarge
    rw [he]
    exact ((U_le_Z _).trans s.Z_le_X).trans le_sup_right
  have hAQ : A ≤ Q R (alpha R) := (s.criticalOrbit_le_Q_iff hb hc b).mpr
    (s.criticalPlane_le_Q_of_core_ne hb hc hab hcb hne)
  have hAR : A ≤ Q R b := le_sup_left.trans_eq himage
  have hAnZ : A ≤ normalizer (Z R c : Set (FreeAmalgam R)) :=
    (hAR.trans (fun _ hx => hx.2 c (adjacent_symm R hcb))).trans (Z_normalized R c)
  have hZAn : Z R c ≤ normalizer (A : Set (FreeAmalgam R)) :=
    (critical_Z_le_stabilizer R s.geometry (alpha R) rfl hbpos hc).trans
      (criticalOrbit_normalized c b)
  have hDY : D ≤ criticalPlane R c b := by
    apply sup_le _ (s.edge_Z_le_criticalPlane hc hab hcb)
    rw [s.criticalPlane_eq_opposite_inf_Q h t hfull hb hlarge hc hab hcb]
    exact le_inf (le_normalizer_iff_commutator_le_right.mp hAnZ)
      ((le_normalizer_iff_commutator_le_left.mp hZAn).trans hAQ)
  have hmove : ⁅A,Z R c⁆ = ⁅Z R c,Q R b⁆ := by
    rw [commutator_comm]
    apply commutator_eq_of_centralizing_sup
      (show Q R c ⊔ A = Q R b by rw [sup_comm];exact himage) _ hAnZ
    exact le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R c hc0))
  obtain ⟨i,hi,hiR,hiW,hiS⟩ := s.movement_edge_coordinates h hc0 hcb
  let F := (⁅W,R⁆ ⊔ omegaCenter R).map i
  have hZF : Z R b ≤ F := by
    rw [←hiS]
    exact map_mono le_sup_right
  have hFD : F ≤ D := by
    dsimp only [F,D]
    rw [Subgroup.map_sup,map_commutator,hiR,hiS,hmove]
    exact sup_le_sup_right (commutator_mono hiW le_rfl) _
  have hFY := hFD.trans hDY
  have hfour : 4 ≤ (Z R b).relIndex F := by
    rw [←hiS,relIndex_map_map_of_injective _ _ hi]
    exact s.module_commutator_seed_index_four_le t hfull
  have hmul := relIndex_mul_relIndex (Z R b) F (criticalPlane R c b) hZF hFY
  rw [s.criticalPlane_edge_relIndex_four h t hfull hb hlarge hc hab hcb] at hmul
  have hpos : 0 < F.relIndex (criticalPlane R c b) := Nat.pos_of_ne_zero (by
    intro he
    rw [he,mul_zero] at hmul
    omega)
  have hone : F.relIndex (criticalPlane R c b) = 1 := by nlinarith
  exact le_antisymm hDY ((relIndex_eq_one.mp hone).trans hFD)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T)

/-- The actual characteristic replacement generates the maximal critical plane
from the full orbit image, using the specified quotient and relabeler. -/
theorem reducedSource_criticalOrbit_opposite_commutator_sup_edge_eq_plane (h : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hfull : r.radical.map ((originalSource d h).reduce r).projection =
      pointCore.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom)
    (hb : ((originalSource d h).reduce r).geometry.b r.radical = 2)
    (hlarge : ¬ core r.radical (alpha r.radical) ≤
      (frattini (Q r.radical (alpha r.radical))).map
        (Q r.radical (alpha r.radical)).subtype ⊔ X r.radical (alpha r.radical))
    {c b : Vertex r.radical}
    (hc : CriticalPair r.radical (alpha r.radical) c
      (((originalSource d h).reduce r).geometry.exists_critical (alpha r.radical) rfl))
    (hab : Adjacent r.radical (alpha r.radical) b)
    (hcb : Adjacent r.radical c b)
    (himage : criticalOrbit r.radical c b ⊔ Q r.radical c = Q r.radical b) :
    ⁅criticalOrbit r.radical c b,Z r.radical c⁆ ⊔ Z r.radical b =
      criticalPlane r.radical c b :=
  Source.criticalOrbit_opposite_commutator_sup_edge_eq_plane ((originalSource d h).reduce r)
    (reduced_nativeCentralLayer d h r) d.relabeler.val⁻¹ hfull hb hlarge hc hab hcb himage

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData

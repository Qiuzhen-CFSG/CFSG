module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaCore
public import Theory.GroupTheory.PResidual.FrattiniControl
public import Theory.Frattini.Intersection

/-!
# Frattini obstruction for the central seed

The seed cannot lie in Phi(Q_alpha) times the adjacent-core intersection.
Indeed the beta-core derived bound makes that intersection central modulo D
for the beta core. Opposite-neighbor conjugation and the two critical-center
generators then make the whole seed central modulo Phi(Q_alpha)D for the
alpha actor. Residual commutator idempotence and the Frattini automorphism
kernel remove the Frattini factor, contradicting the earlier (6.5) movement.

This supplies an alternative to the Cartan splitting in the saturation
argument. BTwoSuzukiExclusion applies it to an actual nonlinear beta model;
no quotient selection, saturation or source recognition is assumed here.
Source: DGS, Groups and Graphs (1985), (10.7), printed pp.158--159.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G]

private theorem relative_frattini_control
    (L Q D R : Subgroup G) [Finite L]
    (hQL : Q ≤ L) (hDL : D ≤ L) (hRL : R ≤ L)
    (hnQ : L ≤ normalizer (Q : Set G)) (hnD : L ≤ normalizer (D : Set G))
    (hQ : IsPGroup 2 Q) (hR : IsPPerfect 2 R)
    (hc : ⁅Q,R⁆ ≤ (frattini Q).map Q.subtype ⊔ D) : ⁅Q,R⁆ ≤ D := by
  let Q₀ := Q.subgroupOf L
  let D₀ := D.subgroupOf L
  let R₀ := R.subgroupOf L
  let : Q₀.Normal := (normal_subgroupOf_iff_le_normalizer hQL).mpr hnQ
  let : D₀.Normal := (normal_subgroupOf_iff_le_normalizer hDL).mpr hnD
  have hR₀ : IsPPerfect 2 R₀ := hR.of_surjective
    (subgroupOfEquivOfLe hRL).symm.toMonoidHom (subgroupOfEquivOfLe hRL).symm.surjective
  have hphi : ((frattini Q₀).map Q₀.subtype).map L.subtype =
      (frattini Q).map Q.subtype := by
    rw [←frattini_image_map Q₀ L.subtype L.subtype_injective,
      map_subgroupOf_eq_of_le hQL]
  have hc₀ : ⁅Q₀,R₀⁆ ≤ (frattini Q₀).map Q₀.subtype ⊔ D₀ := by
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [map_commutator,Subgroup.map_sup,hphi,
      map_subgroupOf_eq_of_le hQL,map_subgroupOf_eq_of_le hRL,
      map_subgroupOf_eq_of_le hDL]
    exact hc
  have hh := map_mono (f := L.subtype)
    (commutator_le_of_le_frattini_sup_of_isPPerfect Q₀ R₀ D₀ hQ.comap_subtype hR₀ hc₀)
  simpa only [Q₀,R₀,D₀,map_commutator,map_subgroupOf_eq_of_le hQL,
    map_subgroupOf_eq_of_le hRL,map_subgroupOf_eq_of_le hDL] using hh

private theorem relative_residual_idempotent
    (L Q : Subgroup G) [Finite L] (hQL : Q ≤ L)
    (hQ : IsPGroup 2 Q) (hn : L ≤ normalizer (Q : Set G)) :
    ⁅⁅Q,(pResidual 2 L).map L.subtype⁆,(pResidual 2 L).map L.subtype⁆ =
      ⁅Q,(pResidual 2 L).map L.subtype⁆ := by
  let : (Q.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hQL).mpr hn
  have hh := congrArg (map L.subtype)
    (commutator_isPPerfect_idempotent (pResidual 2 L) (Q.subgroupOf L)
      (isPPerfect_pResidual 2) hQ.comap_subtype le_normalizer_of_normal)
  simpa only [map_commutator,map_subgroupOf_eq_of_le hQL] using hh

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The moving seed cannot be absorbed by the alpha Frattini subgroup
and one adjacent-core intersection. No beta quotient model is assumed. -/
theorem BTwoCenterActionData.seed_not_le_frattini_sup_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    : ¬ centralSeed F v m t ≤ (frattini (Q F v)).map (Q F v).subtype ⊔
        (Q F v ⊓ Q F m) := by
  intro hJcover
  let := finite_endpoints h
  let : Finite c.actor := Finite.of_injective (inclusion c.actor_le) (inclusion_injective _)
  let : Finite (Q F v) := Finite.of_injective
    (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)
  let : Finite (Q F m) := Finite.of_injective
    (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  let : Fact (IsPGroup 2 (Q F v)) := ⟨isPGroup_pCoreIn 2 (stabilizer F v)⟩
  let : Fact (IsPGroup 2 (Q F m)) := ⟨isPGroup_pCoreIn 2 (stabilizer F m)⟩
  have hS := source_kernel_sylow h hB hSyl
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  let J := centralSeed F v m t
  let I := Q F v ⊓ Q F m
  let Φ := (frattini (Q F v)).map (Q F v).subtype
  let N := Φ ⊔ D F m t
  let R := (pResidual 2 c.actor).map c.actor.subtype
  have hJQ : J ≤ Q F v := sup_le (sup_le inf_le_right inf_le_right) d.separated
  have hJL : J ≤ c.actor := hJQ.trans c.core_le
  have hDL : D F m t ≤ c.actor := d.separated.trans c.core_le
  have hΦQ : Φ ≤ Q F v := map_subtype_le _
  have hΦL : Φ ≤ c.actor := hΦQ.trans c.core_le
  have hnQ : c.actor ≤ normalizer (Q F v : Set G) :=
    c.actor_le.trans (CommutingNontrivial.stabilizer_normalizes_Q F v)
  have hnΦ : c.actor ≤ normalizer (Φ : Set G) :=
    hnQ.trans (normalizer_le_normalizer_characteristic_image _ (frattini (Q F v)))
  have hnD : c.actor ≤ normalizer (D F m t : Set G) := hd ▸ d.normalized h hS hb
  have hnN : c.actor ≤ normalizer (N : Set G) :=
    (le_inf hnΦ hnD).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hderPhi : ⁅Q F v,Q F v⁆ ≤ Φ := by
    have hh := map_mono (f := (Q F v).subtype)
      (commutator_le_frattini_of_isPGroup (p := 2) (R := Q F v))
    simpa only [_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
  have hbeta : ⁅Q F m,Q F m⁆ ≤ Z F m := by
    have hh := map_mono (f := (Q F m).subtype)
      (commutator_le_frattini_of_isPGroup (p := 2) (R := Q F m))
    have hder : ⁅Q F m,Q F m⁆ ≤ (frattini (Q F m)).map (Q F m).subtype := by
      simpa only [_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
    exact hder.trans (c.beta_core_frattini_le h hB hSyl hb hactor hcentral ht hne hcomm)
  have hZD : Z F v ≤ D F m t := (d.decomposition h hS hb) ▸ le_sup_left
  have hZmD : Z F m ≤ D F m t :=
    (center_le_of_central_neighbor h hB hSyl c.middle hcentral).trans hZD
  have hJm : ⁅J,Q F m⁆ ≤ N := by
    apply (commutator_mono hJcover le_rfl).trans
    apply commutator_sup_le_of_relative_normal c.actor Φ I (Q F m) N hnN
      hΦL (inf_le_left.trans c.core_le)
    · exact (le_normalizer_iff_commutator_le_left.mp (c.neighbor_core_le.trans hnΦ)).trans le_sup_left
    · exact ((commutator_mono inf_le_right le_rfl).trans hbeta).trans
        (hZmD.trans le_sup_right)
  have hnJ : c.actor ≤ normalizer (J : Set G) :=
    c.actor_le.trans (c.seed_stabilizer_normalized h hS hb ht hne)
  have hJt : ⁅J,Q F t⁆ ≤ N := by
    have hh := map_mono (f := (MulAut.conj (g : G)).toMonoidHom) hJm
    have hj : J.map (MulAut.conj (g : G)).toMonoidHom = J :=
      mem_normalizer_iff_map_conj_eq.mp (hnJ g.property)
    have hn : N.map (MulAut.conj (g : G)).toMonoidHom = N :=
      mem_normalizer_iff_map_conj_eq.mp (hnN g.property)
    rwa [map_commutator,hj,←Q_translate,hg,hn] at hh
  have hZwV : Z F w ≤ V F m 1 :=
    le_iSup_of_le w (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl c.terminal)) le_rfl)
  have hZzV : Z F ((g : G) • w) ≤ V F t 1 :=
    le_iSup_of_le _ (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl d.opposite)) le_rfl)
  have hZmQ := hZwV.trans (graph_V_le_Q_of_short h hS m (i := 1) (by rw [hb]; decide))
  have hZzQ := hZzV.trans (graph_V_le_Q_of_short h hS t (i := 1) (by rw [hb]; decide))
  have hgen : c.actor = (Z F w ⊔ Z F ((g : G) • w)) ⊔ Q F v := hd.symm.trans d.actor_generators
  have hWL : Z F w ⊔ Z F ((g : G) • w) ≤ c.actor := le_sup_left.trans hgen.ge
  have hJLcomm : ⁅J,c.actor⁆ ≤ N := by
    rw [commutator_comm,hgen]
    apply commutator_sup_le_of_relative_normal c.actor _ _ J N hnN hWL c.core_le
    · apply commutator_sup_le_of_relative_normal c.actor _ _ J N hnN
        (le_sup_left.trans hWL) (le_sup_right.trans hWL)
      · rw [commutator_comm]
        exact (commutator_mono le_rfl hZmQ).trans hJm
      · rw [commutator_comm]
        exact (commutator_mono le_rfl hZzQ).trans hJt
    · exact ((commutator_mono le_rfl hJQ).trans hderPhi).trans le_sup_left
  have hRL : R ≤ c.actor := map_subtype_le _
  have hR : IsPPerfect 2 R := (isPPerfect_pResidual 2 (G := c.actor)).of_surjective
    (c.actor.subtype.subgroupMap (pResidual 2 c.actor))
    (c.actor.subtype.subgroupMap_surjective (pResidual 2 c.actor))
  have hmove : ⁅Q F v,R⁆ ≤ J := by
    have hh := d.core_residual_le_seed h hS hb (hd.symm ▸ c.actor_le)
    rwa [hd] at hh
  have hbound : ⁅Q F v,R⁆ ≤ N := by
    rw [←relative_residual_idempotent c.actor (Q F v) c.core_le
      (isPGroup_pCoreIn 2 (stabilizer F v)) hnQ]
    exact (commutator_mono hmove hRL).trans hJLcomm
  have hkill := relative_frattini_control c.actor (Q F v) (D F m t) R
    c.core_le hDL hRL hnQ hnD (isPGroup_pCoreIn 2 (stabilizer F v)) hR hbound
  exact c.seed_residual_not_le_D h hB hSyl hb ht hne hnot
    ((commutator_mono hJQ le_rfl).trans hkill)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

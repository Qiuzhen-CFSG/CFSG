module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.CriticalIndex
public import Theory.GroupTheory.Commutator.FaithfulSimpleImage
public import Theory.Frattini.Intersection

/-!
# The critical comparison forced by a non-Frattini intrinsic core

A critical endpoint escapes Q. Its normal action kernel modulo Phi(Q)X
therefore contains the faithful simple component in the original quotient.
This forces the full commutator core into Phi(Q)X whenever the local critical
commutator is contained there. At distance two, contraposition gives the
literal failed comparison in (3.3), and the reciprocal comparison makes both
critical indices four. Outer automorphisms and fixed central layers remain.

The last transport lemma starts from the actual embedded intrinsic core.
Source: Meierfrankenfeld--Stellmacher (1993), (3.6), pp.870--871, using (3.3).
-/

public section
open Subgroup Representation Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
variable {M J : Type*} [Group M] [Finite M] [Group J]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}

omit [Finite M] in
private theorem local_frattini_map (P S : Subgroup (FreeAmalgam R)) (hPS : P ≤ S) :
    ((frattini (P.subgroupOf S)).map (P.subgroupOf S).subtype).map S.subtype =
      (frattini P).map P.subtype := by
  let e := subgroupOfEquivOfLe hPS
  calc
    _ = ((frattini (P.subgroupOf S)).map e.toMonoidHom).map P.subtype := by
      rw [map_map,map_map]
      rfl
    _ = _ := by rw [frattini_map_equiv]

theorem core_le_frattini_of_local_commutator_le
    (a : Vertex R) (E₀ : Subgroup (FreeAmalgam R))
    (hE₀ : E₀ ≤ stabilizer R a) (hnot : ¬ E₀ ≤ Q R a)
    (hp : IsPGroup 2 (Q R a))
    (κ : stabilizer R a →* J) (hκ : Function.Surjective κ)
    (hk : κ.ker.map (stabilizer R a).subtype = Q R a)
    [(((Ltilde R a).subgroupOf (stabilizer R a)).map κ).Normal]
    [IsSimpleGroup (((Ltilde R a).subgroupOf (stabilizer R a)).map κ)]
    (hna : ¬ IsMulCommutative (((Ltilde R a).subgroupOf (stabilizer R a)).map κ))
    (hc : centralizer (((Ltilde R a).subgroupOf (stabilizer R a)).map κ : Set J) = ⊥)
    (hcomm : ⁅Q R a,E₀⁆ ≤
      (frattini (Q R a)).map (Q R a).subtype ⊔ X R a) :
    core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a := by
  let S := stabilizer R a
  let P := (Q R a).subgroupOf S
  let W := (X R a).subgroupOf S
  let N := (frattini P).map P.subtype ⊔ W
  let E := E₀.subgroupOf S
  let L := (Ltilde R a).subgroupOf S
  let : Finite S := finite_stabilizer R a
  let : P.Normal := Q_normal R a
  let : W.Normal := X_normal R a
  let : ((frattini P).map P.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  let : Fact (IsPGroup 2 P) := ⟨hp.comap_subtype⟩
  have hP : Q R a ≤ S := fun _ hx => hx.1
  have hW : X R a ≤ S := (omegaCenter_le _).trans hP
  have hPm : P.map S.subtype = Q R a := map_subgroupOf_eq_of_le hP
  have hWm : W.map S.subtype = X R a := map_subgroupOf_eq_of_le hW
  have hNm : N.map S.subtype =
      (frattini (Q R a)).map (Q R a).subtype ⊔ X R a := by
    rw [Subgroup.map_sup,hWm,local_frattini_map _ _ hP]
  have hEm : E.map S.subtype = E₀ := map_subgroupOf_eq_of_le hE₀
  have hPP : ⁅P,P⁆ ≤ N := by
    apply le_trans _ le_sup_left
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hE : ¬ E ≤ P := by
    intro h
    apply hnot
    simpa only [hEm,hPm] using map_mono (f := S.subtype) h
  have hPE : ⁅P,E⁆ ≤ N := by
    apply (map_le_map_iff_of_injective S.subtype_injective).mp
    simpa only [map_commutator,hPm,hEm,hNm] using hcomm
  have hkP : κ.ker = P := by
    apply (map_injective S.subtype_injective)
    exact hk.trans hPm.symm
  have hPL := commutator_le_of_faithful_simple_image κ hκ P N E L hna hc hkP hPP hE hPE
  have hm := map_mono (f := S.subtype) hPL
  rw [map_commutator,hPm,hNm,map_subgroupOf_eq_of_le (Ltilde_le_stabilizer a)] at hm
  exact hm
theorem core_le_frattini_of_critical_commutator_le
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R) (hp : IsPGroup 2 (Q R a))
    (κ : stabilizer R a →* J) (hκ : Function.Surjective κ)
    (hk : κ.ker.map (stabilizer R a).subtype = Q R a)
    [(((Ltilde R a).subgroupOf (stabilizer R a)).map κ).Normal]
    [IsSimpleGroup (((Ltilde R a).subgroupOf (stabilizer R a)).map κ)]
    (hna : ¬ IsMulCommutative (((Ltilde R a).subgroupOf (stabilizer R a)).map κ))
    (hc : centralizer (((Ltilde R a).subgroupOf (stabilizer R a)).map κ : Set J) = ⊥)
    (hcomm : ⁅Q R a,Z R z⁆ ≤
      (frattini (Q R a)).map (Q R a).subtype ⊔ X R a) :
    core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a := by
  have hba : 0 < criticalDistance R a (geometry.exists_critical a path.start_color) := by
    rw [geometry.distance_constant a path.start_color]; exact hb
  have hr := critical_reverse R geometry hC a path.start_color hba z path.end_color path.critical
  have hZ : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  exact core_le_frattini_of_local_commutator_le a (Z R z) hZ hr.2 hp κ hκ hk hna hc hcomm

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
variable {M J : Type*} [Group M] [Finite M] [Group J]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}

theorem critical_bad_comparison_of_nonfrattini
    (path : CriticalPath R geometry a z) (hb : geometry.b R = 2)
    (hC : EdgeCentralizerCondition R) (hp : IsPGroup 2 (Q R a))
    (κ : stabilizer R a →* J) (hκ : Function.Surjective κ)
    (hk : κ.ker.map (stabilizer R a).subtype = Q R a)
    [(((Ltilde R a).subgroupOf (stabilizer R a)).map κ).Normal]
    [IsSimpleGroup (((Ltilde R a).subgroupOf (stabilizer R a)).map κ)]
    (hna : ¬ IsMulCommutative (((Ltilde R a).subgroupOf (stabilizer R a)).map κ))
    (hc : centralizer (((Ltilde R a).subgroupOf (stabilizer R a)).map κ : Set J) = ⊥)
    (hlarge : ¬ core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a) :
    ¬ ⁅Z R z,Q R a⁆ ≤ ⁅X R a,X R z⁆ ⊔ ⁅X R a ⊓ Q R z,Q R a⁆ := by
  have hd : (cosetGraph R).dist a z = 2 :=
    path.critical.1.trans ((geometry.distance_constant a path.start_color).trans hb)
  have hzero : ⁅X R a ⊓ Q R z,Q R a⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (inf_le_left.trans (le_centralizer_iff.mp (Q_le_centralizer_X R a)))
  have hXX : ⁅X R a,X R z⁆ ≤ X R a :=
    le_normalizer_iff_commutator_le_left.mp
      ((omegaCenter_le _).trans
        ((Q_le_stabilizer_of_dist_two R z a path.end_color (by rwa [SimpleGraph.dist_comm])).trans
          (X_normalized R a)))
  intro h
  apply hlarge
  apply core_le_frattini_of_critical_commutator_le path (by omega) hC hp κ hκ hk hna hc
  rw [hzero,sup_bot_eq] at h
  rw [commutator_comm]
  exact h.trans (hXX.trans le_sup_right)

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
open ChapterB.QuasisimpleSource MSCentralOrbit SourceComparison
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

theorem original_critical_indices_eq_four_of_nonfrattini
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : geometry.b R = 2)
    (hlarge : ¬ core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a) :
    (Q R z).relIndex (Z R a) = 4 ∧ (Q R a).relIndex (Z R z) = 4 := by
  obtain ⟨i,hi,hir,hiL,_,hiQ⟩ := vertex_coordinates_with_kernel R hp hQR path.start_color
  let κ := ElementaryMovedCover.embeddedQuotient q i hi (stabilizer R a) hir
  have hκ : Function.Surjective κ :=
    ElementaryMovedCover.embeddedQuotient_surjective q i hi _ hir hq
  have hkQ : κ.ker.map (stabilizer R a).subtype = Q R a := by
    rw [ElementaryMovedCover.embeddedQuotient_kernel,hcore]
    exact hiQ
  have hL : ((Ltilde R a).subgroupOf (stabilizer R a)).map κ = (pResidual 2 H).map q := by
    rw [←hiL]
    exact ElementaryMovedCover.embeddedQuotient_subgroup q i hi _ hir _
  let : (((Ltilde R a).subgroupOf (stabilizer R a)).map κ).Normal := hL ▸ inferInstance
  let : IsSimpleGroup (((Ltilde R a).subgroupOf (stabilizer R a)).map κ) := hL ▸ inferInstance
  have hna : ¬ IsMulCommutative (((Ltilde R a).subgroupOf (stabilizer R a)).map κ) := by
    rw [hL]
    exact Group.IsPerfect.not_isMulCommutative _
  have hcent : centralizer (((Ltilde R a).subgroupOf (stabilizer R a)).map κ : Set J) = ⊥ := by
    rw [hL]; exact hC
  have hbad := critical_bad_comparison_of_nonfrattini path hb
    (MSCentralOrbit.edgeCentralizerCondition R hp hQR hfaith)
    (Q_isPGroup R hp hQR a path.start_color) κ hκ hkQ hna hcent hlarge
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two R a z
    (path.critical.1.trans ((geometry.distance_constant a path.start_color).trans hb))
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases hcol : color R t <;> simp_all [path.start_color]
  have hZa : Z R a ≤ X R a := geometry.omega_bound a path.start_color (by
    exact lt_of_lt_of_eq (show 0 < geometry.b R by omega)
      (geometry.distance_constant a path.start_color).symm)
  have hcomm : ⁅Z R a,Z R z⁆ ≤ X R a :=
    (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path).trans hZa
  apply original_critical_indices_eq_four_of_adjacent_core R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path (by omega) (Q R a) hzt
    (Q_le_adjacent_h R ht hat)
    ((Q_le_centralizer_X R a).trans (centralizer_le hcomm)) hbad
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
variable {H : Type*} [Group H] [Finite H]

theorem graph_core_nonfrattini_of_intrinsic (K R : Subgroup H) [K.Normal]
    (hp : IsPGroup 2 R) (hQR : pCore 2 H ≤ R) (hres : pResidual 2 H = K)
    (hlarge : ¬ (blockU K).map K.subtype ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔ omegaCenterIn (pCore 2 H)) :
    ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R) := by
  intro h
  apply hlarge
  rw [MSCentralOrbit.graphCore_eq_intrinsic K R hp hQR hres,
    X,Q_alpha R hp hQR,omegaCenter_map _ _ (embedM_injective R),
    frattini_image_map _ _ (embedM_injective R),←Subgroup.map_sup] at h
  exact (map_le_map_iff_of_injective (embedM_injective R)).mp h

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
variable {H : Type*} [Group H] (R : Subgroup H)

theorem nonfrattini_act_iff (g : FreeAmalgam R) (a : Vertex R) :
    (¬ core R (act R g a) ≤
      (frattini (Q R (act R g a))).map (Q R (act R g a)).subtype ⊔ X R (act R g a)) ↔
    ¬ core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a := by
  rw [core_act,Q_act,X_act,frattini_image_map _ _ (MulAut.conj g⁻¹).injective,
    ←Subgroup.map_sup,map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]

theorem nonfrattini_at_vertex
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {a : Vertex R} (ha : color R a = false) :
    ¬ core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  have h := (nonfrattini_act_iff R g (alpha R)).mpr hlarge
  have he : act R g (alpha R) = mVertex R g := by simp only [alpha,act_mVertex,one_mul]
  rw [he] at h
  exact h
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction

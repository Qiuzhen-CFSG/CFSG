module
public import Stellmacher.SectionNine.NineFourAuxiliaryCore
public import Stellmacher.SectionNine.CubicTwoNeighborKernel

/-!
# The core quotient in the all-central case of (9.4)

Let N be Q_a intersect Q_next and let Qstar be the intersection of its
F-conjugates for the literal auxiliary group F. If the auxiliary residual
core lies in Q_a, the proved residual/core supplement for F makes N
intersect F normal in F. Consequently Q_next intersect Q_remote and
[N,Q_a intersect Q_remote] lie in Qstar.

The cubic two-neighbor kernel puts the two remote/next cores' intersection
inside Q_a. Its containment in F intersect Q_next then places it in O₂(F).
The identity [O²(F),O₂(F)]≤O₂(O²(F)) shows that O²(F) normalizes N intersect F;
the core-intersection generator and the retained quotient kernel normalize
it directly. The supplied generation equality is precisely the independent
actual-input theorem `nine_four_auxiliary_residual_core_supplement`.
Normalization places this subgroup in every F-conjugate of N. Finally the
two elementary commutator bounds put [N,Q_a intersect Q_remote] in the
remote/next core intersection.

Source: Stellmacher (9.4), printed pp.51–52, the two containments preceding
the faithful action on Q_next/Qstar, in refs/files/stellmacher-n-group.pdf.
The quotient action itself is not asserted here.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_central_kernel_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hremote : remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : remote ≠ ctx.criticalPath.firstStep)
    (actor : G) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hcore : twoCoreIn (twoResidualIn
      ((QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote) ⊔
        Subgroup.zpowers actor)) ≤ QAt ctx.Γ ctx.criticalPath.a)
    (hgeneration :
      let D := QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote
      let F := D ⊔ Subgroup.zpowers actor
      F = (twoResidualIn F ⊔ D) ⊔ (F ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)) :
    let D := QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote
    let F := D ⊔ Subgroup.zpowers actor
    let N := QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep
    let Qstar := ⨅ mover : F, N.map (MulAut.conj (mover : G)).toMonoidHom
    F ≤ Subgroup.normalizer (N ⊓ F : Subgroup G) ∧
      QAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ remote ≤ Qstar ∧
      ⁅N,D⁆ ≤ Qstar := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Qa := QAt Γ cp.a
  let Qn := QAt Γ cp.firstStep
  let Qd := QAt Γ remote
  let D := Qa ⊓ Qd
  let F := D ⊔ Subgroup.zpowers actor
  let R := twoResidualIn F
  let Q := twoCoreIn R
  let N := Qa ⊓ Qn
  let J := N ⊓ F
  let K := F ⊓ Qn
  let I := Qn ⊓ Qd
  let Qstar := ⨅ mover : F, N.map (MulAut.conj (mover : G)).toMonoidHom
  have hgeometry := nine_four_auxiliary_core_geometry ctx hb remote actor hactor
  have hFP : F ≤ GAt Γ cp.firstStep := hgeometry.1
  have hQn : Q ≤ Qn := hgeometry.2.1
  have hQaEdge : Qa ≤ GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
    (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans cp.S_le_edge_stabilizers
  have hQnEdge : Qn ≤ GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
    (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2.trans cp.S_le_edge_stabilizers
  have hintersection : I ≤ Qa := by
    have hmodel := (lemma_nine_three_ambient ctx hb cp.a ⟨1, Γ.act_one _⟩).1
    have hQdSelf : Qd ≤ GAt Γ remote := by
      change Γ.twoCoreAt remote ≤ Γ.vertexStabilizer remote
      rw [Γ.twoCoreAt_def]
      exact twoCoreIn_le _
    intro z hz
    exact cubic_mem_core_of_fix_two_neighbors Γ cp.a remote cp.firstStep
      (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven cp.a hmodel)
      ((mem_neighborhood_iff_adjacent Γ).mp hremote) cp.firstStep_adj hne
      ⟨z, (hQnEdge hz.1).1⟩
      ((Set.ext_iff.mp (Γ.stabilizer_def remote) z).mp (hQdSelf hz.2))
      ((Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) z).mp (hQnEdge hz.1).2)
  have hEdgeN : GAt Γ cp.a ⊓ GAt Γ cp.firstStep ≤ Subgroup.normalizer N :=
    (le_inf (inf_le_left.trans (stabilizer_le_normalizer_q Γ cp.a))
      (inf_le_right.trans (stabilizer_le_normalizer_q Γ cp.firstStep))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hQF : Q ≤ F := (twoCoreIn_le R).trans (twoResidualIn_le F)
  have hQJ : Q ≤ J := le_inf (le_inf hcore hQn) hQF
  have hFK : F ≤ Subgroup.normalizer K :=
    (le_inf F.le_normalizer (hFP.trans (stabilizer_le_normalizer_q Γ cp.firstStep))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hKnormal : (K.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (show K ≤ F from inf_le_left)).mpr hFK
  have hKtwo : IsPGroup 2 K := by
    have hQntwo : IsPGroup 2 Qn := by
      change IsPGroup 2 (Γ.twoCoreAt cp.firstStep)
      rw [Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := GAt Γ cp.firstStep)).map _
    exact hQntwo.to_le inf_le_right
  have hKcore : K ≤ twoCoreIn F := by
    have hnative : K.subgroupOf F ≤ pCore 2 F :=
      le_sSup ⟨hKnormal, hKtwo.comap_subtype⟩
    change K ≤ (pCore 2 F).map F.subtype
    rw [← Subgroup.map_subgroupOf_eq_of_le (show K ≤ F from inf_le_left)]
    exact Subgroup.map_mono hnative
  have hJcore : J ≤ twoCoreIn F :=
    (le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans hKcore
  have hRJ : R ≤ Subgroup.normalizer J := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    rw [Subgroup.commutator_comm]
    exact ((Subgroup.commutator_mono le_rfl hJcore).trans
      (residual_commutator_core_le F)).trans hQJ
  have hDJ : D ≤ Subgroup.normalizer J :=
    (le_inf (inf_le_left.trans (hQaEdge.trans hEdgeN))
      (le_sup_left.trans F.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hKJ : K ≤ Subgroup.normalizer J :=
    (le_inf (inf_le_right.trans (hQnEdge.trans hEdgeN))
      (inf_le_left.trans F.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hFJ : F ≤ Subgroup.normalizer J := by
    have hgen : F = (R ⊔ D) ⊔ K := hgeneration
    rw [hgen]
    exact sup_le (sup_le hRJ hDJ) hKJ
  have hIJ : I ≤ J := by
    apply le_inf (le_inf hintersection inf_le_left)
    exact (le_inf hintersection inf_le_right).trans le_sup_left
  have hJstar : J ≤ Qstar := by
    apply le_iInf
    intro mover element helement
    apply Subgroup.mem_map_equiv.mpr
    change (mover : G)⁻¹ * element * (mover : G) ∈ N
    have hm := (Subgroup.mem_normalizer_iff.mp (hFJ (F.inv_mem mover.property)) element).mp helement
    have hn : (mover : G)⁻¹ * element * ((mover : G)⁻¹)⁻¹ ∈ N := hm.1
    simpa only [inv_inv] using hn
  have hQaD : Qa ≤ Subgroup.normalizer D :=
    (le_inf Qa.le_normalizer
      (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a remote
        hremote default).2.2.trans (stabilizer_le_normalizer_q Γ remote))).trans
          Subgroup.inf_normalizer_le_normalizer_inf
  have hND : ⁅N,D⁆ ≤ I := by
    apply le_inf
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono le_rfl inf_le_right).trans
        (Subgroup.le_normalizer_iff_commutator_le_right.mp
          ((le_sup_left.trans hFP).trans (stabilizer_le_normalizer_q Γ cp.firstStep)))
    · exact (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (inf_le_left.trans hQaD)).trans inf_le_right
  exact ⟨hFJ, hIJ.trans hJstar, hND.trans (hIJ.trans hJstar)⟩

end Stellmacher.SectionNine

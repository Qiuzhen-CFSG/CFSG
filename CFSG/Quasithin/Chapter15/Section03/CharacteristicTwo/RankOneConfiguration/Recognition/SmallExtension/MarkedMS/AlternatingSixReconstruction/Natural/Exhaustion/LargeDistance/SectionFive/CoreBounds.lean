module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Transport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SelectedSpan

/-!
# Common-core action on the selected natural section

When the selected span's derived subgroup is fixed by the residual and the
actual core commutator is contained in the starting seed times the selected
moved span, the common two-core intersection acts on that core
modulo its derived subgroup trivially. Enlarge the intersection by the core
commutator. The incident radical and residual normalize this enlargement,
so its bound on the second seed extends to the entire selected orbit span.
This supplies the opposite-core commutator premise in the terminal argument
without a full point-radical image or a split moving cover.

Source: MS93 (3.10) and the terminal paragraph of (5.12), pp.879--881,927.
The selected-path estimates remain with this task's final assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
private theorem normalizes_commutator {F : Type*} [Group F] (J A B : Subgroup F)
    (hA : J ≤ normalizer (A : Set F)) (hB : J ≤ normalizer (B : Set F)) :
    J ≤ normalizer ((⁅A,B⁆ : Subgroup F) : Set F) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅A,B⁆ : Subgroup F).map (MulAut.conj g).toMonoidHom = ⁅A,B⁆
  rw [map_commutator]
  exact congrArg₂ (fun X Y : Subgroup F => ⁅X,Y⁆)
    (mem_normalizer_iff_map_conj_eq.mp (hA hg))
    (mem_normalizer_iff_map_conj_eq.mp (hB hg))

private theorem conjugate_span_commutator_le {F : Type*} [Group F]
    (J A N H : Subgroup F) (hAJ : A ≤ J)
    (hJN : J ≤ normalizer (N : Set F)) (hJH : J ≤ normalizer (H : Set F))
    (hAN : ⁅A,N⁆ ≤ H) :
    ⁅⨆ g : J, A.map (MulAut.conj (g : F)⁻¹).toMonoidHom,N⁆ ≤ H := by
  apply commutator_iSup_le_of_relative_normal J N H _ hJH
  · intro g x hx
    obtain ⟨a,ha,rfl⟩ := hx
    exact J.mul_mem (J.mul_mem (J.inv_mem g.property) (hAJ ha))
      (J.inv_mem (J.inv_mem g.property))
  · intro g
    have hm := map_mono (f := (MulAut.conj (g : F)⁻¹).toMonoidHom) hAN
    have hnN : N.map (MulAut.conj (g : F)⁻¹).toMonoidHom = N :=
      mem_normalizer_iff_map_conj_eq.mp (hJN (J.inv_mem g.property))
    have hnH : H.map (MulAut.conj (g : F)⁻¹).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (hJH (J.inv_mem g.property))
    rwa [map_commutator,hnN,hnH] at hm

private theorem core_cross_commutator_of_span {F : Type*} [Group F]
    (J A B K T Z S P W : Subgroup F)
    (hKJ : K ≤ J) (hAJ : A ≤ J) (hTJ : T ≤ J) (hZJ : Z ≤ J)
    (hPA : P ≤ A) (hWP : W ≤ P) (hSP : S ≤ P)
    (hJA : J ≤ normalizer (A : Set F)) (hJK : J ≤ normalizer (K : Set F))
    (hTB : T ≤ normalizer (B : Set F)) (hgen : K ⊔ T = J)
    (hZA : Z ≤ centralizer (A : Set F)) (hSB : S ≤ centralizer (B : Set F))
    (hspan : P = ⨆ g : J, S.map (MulAut.conj (g : F)⁻¹).toMonoidHom)
    (hder : ⁅P,P⁆ = ⁅⁅A,K⁆,⁅A,K⁆⁆) (hsupp : ⁅A,K⁆ ≤ Z ⊔ W) :
    ⁅A ⊓ B,⁅A,K⁆⁆ ≤ ⁅⁅A,K⁆,⁅A,K⁆⁆ := by
  let C := ⁅A,K⁆
  let D := A ⊓ B
  let N := D ⊔ C
  let H := ⁅C,C⁆
  have hCA : C ≤ A := le_normalizer_iff_commutator_le_left.mp (hKJ.trans hJA)
  have hJC : J ≤ normalizer (C : Set F) := normalizes_commutator J A K hJA hJK
  have hJH : J ≤ normalizer (H : Set F) := normalizes_commutator J C C hJC hJC
  have hCP : ⁅C,P⁆ ≤ H := by
    apply (commutator_mono hsupp le_rfl).trans
    apply commutator_sup_le_of_relative_normal J Z W P H hJH hZJ
      (hWP.trans (hPA.trans hAJ))
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (hZA.trans (centralizer_le hPA))).le.trans bot_le
    · exact (commutator_mono hWP le_rfl).trans_eq hder
  have hNA : N ≤ A := sup_le inf_le_left hCA
  have hKN : K ≤ normalizer (N : Set F) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono hNA le_rfl).trans (show C ≤ N from le_sup_right))
  have hTN : T ≤ normalizer (N : Set F) :=
    (le_inf
      ((le_inf (hTJ.trans hJA) hTB).trans inf_normalizer_le_normalizer_inf)
      (hTJ.trans hJC)).trans (normalizer_inf_normalizer_le_normalizer_sup D C)
  have hJN : J ≤ normalizer (N : Set F) := by
    rw [←hgen]
    exact sup_le hKN hTN
  have hSN : ⁅S,N⁆ ≤ H := by
    rw [commutator_comm]
    apply commutator_sup_le_of_relative_normal J D C S H hJH
      (inf_le_left.trans hAJ) (hCA.trans hAJ)
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (inf_le_right.trans (le_centralizer_iff.mp hSB))).le.trans bot_le
    · exact (commutator_mono le_rfl hSP).trans hCP
  have hPN : ⁅P,N⁆ ≤ H := by
    rw [hspan]
    exact conjugate_span_commutator_le J S N H (hSP.trans (hPA.trans hAJ))
      hJN hJH hSN
  rw [commutator_comm]
  apply (commutator_mono hsupp le_rfl).trans
  apply commutator_sup_le_of_relative_normal J Z W D H hJH hZJ
    (hWP.trans (hPA.trans hAJ))
  · exact (commutator_eq_bot_iff_le_centralizer.mpr
      (hZA.trans (centralizer_le inf_le_left))).le.trans bot_le
  · exact (commutator_mono hWP le_sup_left).trans hPN

variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include h in
private theorem core_residual_edge_generation {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    Ltilde d.radical a ⊔ Q d.radical t = stabilizer d.radical a := by
  have hsup : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d g
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d,Q_beta,←Subgroup.map_sup,hsup]
    exact (MonoidHom.range_eq_map (embedM d.radical)).symm.trans (stabilizer_m_base d.radical).symm
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at ha
    cases ha

include h in
/-- The common two-core intersection centralizes the actual core modulo its
derived subgroup, using the selected span's fixed derived subgroup and the
proved core supplement. -/
theorem selected_core_cross_commutator_of_supplement
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hsupp : ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤
      Z d.radical (alpha d.radical) ⊔ forwardMovedSpan d.radical (p.walk.getVert 2)) :
    let C := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
    ⁅Q d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2),C⁆ ≤ ⁅C,C⁆ := by
  let a := alpha d.radical
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let J := stabilizer d.radical a
  let P := localZSpan d.radical c a
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hQa : Q d.radical t ≤ J := fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hQc : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hQJ : Q d.radical a ≤ J := fun _ hx => hx.1
  have hPQ : P ≤ Q d.radical a := by
    apply (localZSpan_le_V d.radical _).trans
      (V_le_Q d.radical (geometry := replacementGeometry h d) rfl hb)
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  have hJL : J ≤ normalizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    obtain ⟨z,hz,rfl⟩ := hx
    refine ⟨⟨g,hg⟩ * z * ⟨g,hg⟩⁻¹,?_,rfl⟩
    exact (inferInstance : (pResidual 2 (stabilizer d.radical a)).Normal).conj_mem z hz ⟨g,hg⟩
  have he : ⁅P,P⁆ =
      ⁅⁅Q d.radical a,Ltilde d.radical a⁆,⁅Q d.radical a,Ltilde d.radical a⁆⁆ :=
    (selected_span_derived_eq_moved hb p hfixed).trans
      (selected_core_derived_eq_of_supplement hb p hsupp).symm
  exact core_cross_commutator_of_span J (Q d.radical a) (Q d.radical c)
    (Ltilde d.radical a) (Q d.radical t) (Z d.radical a) (Z d.radical c) P
    (forwardMovedSpan d.radical c) (Ltilde_le_stabilizer _) hQJ hQa
    (Z_le_stabilizer d.radical a) hPQ (forwardMovedSpan_le d.radical c)
    (Z_le_localZSpan d.radical c a) (Q_normalized d.radical a) hJL
    (hQc.trans (Q_normalized d.radical c)) (core_residual_edge_generation (h := h) rfl hat)
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a rfl))
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c hc))
    (localZSpan_eq_conjugates d.radical c a) he hsupp

include h in
/-- The same common-core bound at every vertex, using the path's literal
second vertex and conjugation maps. -/
theorem selected_core_cross_commutator_of_supplement_at
    (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) a,
      localZSpan d.radical (p.walk.getVert 2) a⁆ ≤
      centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)))
    (hsupp : ⁅Q d.radical a,Ltilde d.radical a⁆ ≤
      Z d.radical a ⊔ ⁅localZSpan d.radical (p.walk.getVert 2) a,Ltilde d.radical a⁆) :
    let C := ⁅Q d.radical a,Ltilde d.radical a⁆
    ⁅Q d.radical a ⊓ Q d.radical (p.walk.getVert 2),C⁆ ≤ ⁅C,C⁆ := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ (mVertex d.radical g) = alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have base := selected_core_cross_commutator_of_supplement (h := h) hb
    (a' := act d.radical g⁻¹ a')
  dsimp only [forwardMovedSpan] at base
  rw [←hbase] at base
  have hf := (map_mono (f := (MulAut.conj g).toMonoidHom) hfixed).trans
    (map_centralizer_le_centralizer_image _ _)
  have hf' : ⁅localZSpan d.radical ((p.act g⁻¹).walk.getVert 2)
        (act d.radical g⁻¹ (mVertex d.radical g)),
      localZSpan d.radical ((p.act g⁻¹).walk.getVert 2)
        (act d.radical g⁻¹ (mVertex d.radical g))⁆ ≤
      centralizer (Ltilde d.radical (act d.radical g⁻¹ (mVertex d.radical g)) :
        Set (FreeAmalgam d.radical)) := by
    change ⁅localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2)
        (act d.radical g⁻¹ (mVertex d.radical g)),
      localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2)
        (act d.radical g⁻¹ (mVertex d.radical g))⁆ ≤ _
    rw [actWalk_getVert,LocalCommutator.CriticalCase.localZSpan_act,Ltilde_act,inv_inv,
      ←map_commutator]
    exact hf
  have hs : ⁅Q d.radical (act d.radical g⁻¹ (mVertex d.radical g)),
      Ltilde d.radical (act d.radical g⁻¹ (mVertex d.radical g))⁆ ≤
      Z d.radical (act d.radical g⁻¹ (mVertex d.radical g)) ⊔
        ⁅localZSpan d.radical ((p.act g⁻¹).walk.getVert 2)
          (act d.radical g⁻¹ (mVertex d.radical g)),
          Ltilde d.radical (act d.radical g⁻¹ (mVertex d.radical g))⁆ := by
    change ⁅Q d.radical (act d.radical g⁻¹ (mVertex d.radical g)),
      Ltilde d.radical (act d.radical g⁻¹ (mVertex d.radical g))⁆ ≤
      Z d.radical (act d.radical g⁻¹ (mVertex d.radical g)) ⊔
        ⁅localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2)
          (act d.radical g⁻¹ (mVertex d.radical g)),
          Ltilde d.radical (act d.radical g⁻¹ (mVertex d.radical g))⁆
    rw [actWalk_getVert,Q_act,Ltilde_act,Z_act,
      LocalCommutator.CriticalCase.localZSpan_act,inv_inv,
      ←map_commutator,←map_commutator,←Subgroup.map_sup]
    exact map_mono hsupp
  have hh := base (p.act g⁻¹) hf' hs
  change ⁅Q d.radical (act d.radical g⁻¹ (mVertex d.radical g)) ⊓
      Q d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2),
      ⁅Q d.radical (act d.radical g⁻¹ (mVertex d.radical g)),
        Ltilde d.radical (act d.radical g⁻¹ (mVertex d.radical g))⁆⁆ ≤
      ⁅⁅Q d.radical (act d.radical g⁻¹ (mVertex d.radical g)),
        Ltilde d.radical (act d.radical g⁻¹ (mVertex d.radical g))⁆,
        ⁅Q d.radical (act d.radical g⁻¹ (mVertex d.radical g)),
          Ltilde d.radical (act d.radical g⁻¹ (mVertex d.radical g))⁆⁆ at hh
  rwa [actWalk_getVert,Q_act,Q_act,Ltilde_act,inv_inv,
    ←Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ←map_commutator,←map_commutator,←map_commutator,
    map_le_map_iff_of_injective (MulAut.conj g).injective] at hh

/-- On the original replacement, the natural selected quotient and source
endpoint estimates give both the derived-line order and the common-core
commutator bound needed at the opposite endpoint. -/
theorem selected_core_bounds_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2)
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2), Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical))
    (hcoreIndex : (Q d.radical (p.walk.getVert 2)).relIndex
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤ 2)
    (hcoreActor : ⁅⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    let C := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
    Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅Q d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2),C⁆ ≤ ⁅C,C⁆ := by
  have hs := selected_core_derived_transfer_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p hsmall hnonabelian
    hfixed hindex hcomm hcoreIndex hcoreActor
  exact ⟨hs.2.1,selected_core_cross_commutator_of_supplement hb p hfixed hs.1⟩

/-- The terminal application now derives its cross-commutator estimate
from a selected opposite path and its core supplement. The equality of
second vertices preserves the common source graph and starting seed. -/
theorem selected_natural_terminal_false_of_opposite_supplement_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2)
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical))
    (hCcard : Nat.card (⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ :
        Subgroup (FreeAmalgam d.radical)) ≤ 2)
    {v : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) v)
    (hq : q.walk.getVert 2 = alpha d.radical)
    (hfixedOpp : ⁅localZSpan d.radical (alpha d.radical) (p.walk.getVert 2),
      localZSpan d.radical (alpha d.radical) (p.walk.getVert 2)⁆ ≤
      centralizer (Ltilde d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)))
    (hsuppOpp : ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆ ≤
      Z d.radical (p.walk.getVert 2) ⊔
        ⁅localZSpan d.radical (alpha d.radical) (p.walk.getVert 2),
          Ltilde d.radical (p.walk.getVert 2)⁆) : False := by
  have hf : ⁅localZSpan d.radical (q.walk.getVert 2) (p.walk.getVert 2),
      localZSpan d.radical (q.walk.getVert 2) (p.walk.getVert 2)⁆ ≤
      centralizer (Ltilde d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
    simpa only [hq] using hfixedOpp
  have hs : ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆ ≤
      Z d.radical (p.walk.getVert 2) ⊔
        ⁅localZSpan d.radical (q.walk.getVert 2) (p.walk.getVert 2),
          Ltilde d.radical (p.walk.getVert 2)⁆ := by
    simpa only [hq] using hsuppOpp
  have hcross := selected_core_cross_commutator_of_supplement_at hb q hf hs
  dsimp only at hcross
  rw [hq] at hcross
  have hPQ : localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ≤
      Q d.radical (alpha d.radical) := by
    apply (localZSpan_le_V d.radical _).trans
      (V_le_Q d.radical (geometry := replacementGeometry h d) rfl hb)
    rw [SimpleGraph.dist_comm,p.dist_start (by
      have hl : p.walk.length = replacementDistance h d := p.length_eq_b
      omega)]
  exact selected_natural_terminal_false_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p hnonabelian hsmall
    hfixed hindex hcomm hCcard
    ((commutator_mono (le_inf inf_le_right (inf_le_left.trans hPQ)) le_rfl).trans hcross)

/-- The source core estimates at the original path determine the derived order
at the opposite vertex. Nonabelianness constructs the opposite critical path,
so neither its existence nor its common second vertex is an extra premise. -/
theorem selected_natural_terminal_false_of_core_estimates_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2)
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical))
    (hcoreIndex : (Q d.radical (p.walk.getVert 2)).relIndex
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤ 2)
    (hcoreActor : ⁅⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical))
    (hfixedOpp : ⁅localZSpan d.radical (alpha d.radical) (p.walk.getVert 2),
      localZSpan d.radical (alpha d.radical) (p.walk.getVert 2)⁆ ≤
      centralizer (Ltilde d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)))
    (hsuppOpp : ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆ ≤
      Z d.radical (p.walk.getVert 2) ⊔
        ⁅localZSpan d.radical (alpha d.radical) (p.walk.getVert 2),
          Ltilde d.radical (p.walk.getVert 2)⁆) : False := by
  have hs := selected_core_derived_transfer_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p hsmall hnonabelian hfixed hindex hcomm hcoreIndex hcoreActor
  have hl : 2 ≤ p.walk.length := by
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have hc : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color hl).mpr (by decide)
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical hc
  have he : act d.radical g (alpha d.radical) = p.walk.getVert 2 := by
    rw [hg]
    simp only [alpha,act_mVertex,one_mul]
  have hCcard : Nat.card (⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ :
        Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
    rw [←he,Q_act,Ltilde_act,←map_commutator,←map_commutator,
      card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hs.2.1.le
  obtain ⟨_,x,hx,q,_,hq,_⟩ := selected_span_conjugate_critical_path hb p hnonabelian
  exact selected_natural_terminal_false_of_opposite_supplement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hnonabelian hsmall hfixed hindex hcomm
    hCcard q hq hfixedOpp hsuppOpp

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

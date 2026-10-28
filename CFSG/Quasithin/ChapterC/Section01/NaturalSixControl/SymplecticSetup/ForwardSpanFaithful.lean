module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpanAction
public import Theory.GroupTheory.LocalNormalizerUniqueness
/-!
# Faithfulness of the terminal central quotient

At critical distance four, conjugation on the forward normal span P descends
through the marked symmetric-six quotient to P/Z(P). Any nontrivial kernel
contains the alternating component. In that case the elementary seed Z_c
has invariant image under both the component and the first edge kernel, hence
under the whole vertex group. Its image therefore fills P/Z(P), making P
abelian, contrary to the derived subgroup having order two.

The action is the literal descended action: the theorem proves faithfulness
for any homomorphism with the stated factorization identity. This supplies
the faithful action required for terminal module recognition in MS93 (5.12),
printed p.927, and includes the characteristic reduction and original
Chapter 13 consumers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- Every descended action with the literal factorization identity is faithful. -/
theorem forward_span_symmetric_central_action_injective
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (ρ : Model.S →* MulAut ((localZSpan R (p.walk.getVert 2) (alpha R)) ⧸
      center (localZSpan R (p.walk.getVert 2) (alpha R))))
    (hρ : ∀ m : M, ρ (s.projection m)=forwardSpanCentralAction R (p.walk.getVert 2) m) :
    Function.Injective ρ := by
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  by_contra hne
  have hAlt : alternatingGroup (Fin 6)≤ρ.ker :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((nontrivial_iff_ne_bot _).mpr hne)
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan R c (alpha R)
  let C := (center P).map P.subtype
  let B := Z R c⊔C
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hc : color R c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) t := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R c t :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hZP : Z R c≤P := Z_le_localZSpan R _ _
  have hCP : C≤P := map_subtype_le _
  have hCC : C≤centralizer (P:Set (FreeAmalgam R)) := by
    rintro _ ⟨z,hz,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)
  have hBP : B≤P := sup_le hZP hCP
  have hPL : ⁅P,Ltilde R (alpha R)⁆≤C := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl z hz
    rw [Ltilde_alpha,s.residual] at hl
    obtain ⟨m,hm,rfl⟩ := hl
    have hmAlt : s.projection m∈alternatingGroup (Fin 6) :=
      s.component_image ▸ mem_map_of_mem s.projection hm
    have he := hρ m
    rw [MonoidHom.mem_ker.mp (hAlt hmAlt)] at he
    have hh := DFunLike.congr_fun he (QuotientGroup.mk' (center P) ⟨z,hz⟩)
    have hq : QuotientGroup.mk' (center P)
        (forwardSpanAction R c m ⟨z,hz⟩) = QuotientGroup.mk' (center P) ⟨z,hz⟩ := by
      exact (forwardSpanCentralAction_apply R c m ⟨z,hz⟩).symm.trans
        (by simpa only [MulAut.one_apply] using hh.symm)
    have hmem := QuotientGroup.eq_iff_div_mem.mp hq
    refine ⟨forwardSpanAction R c m ⟨z,hz⟩/⟨z,hz⟩,hmem,?_⟩
    change embedM R m*z*(embedM R m)⁻¹/z=⁅embedM R m,z⁆
    rw [div_eq_mul_inv,commutatorElement_def]
  have hLB : Ltilde R (alpha R)≤normalizer (B:Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono hBP le_rfl).trans (hPL.trans le_sup_right))
  have hQtG : Q R t≤stabilizer R (alpha R) := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hQtGc : Q R t≤stabilizer R c := fun _ hx => hx.2 _ (adjacent_symm R hct)
  have hGC : stabilizer R (alpha R)≤normalizer (C:Set (FreeAmalgam R)) :=
    (localZSpan_normalized R _ _).trans
      (normalizer_le_normalizer_characteristic_image P (center P))
  have hQtB : Q R t≤normalizer (B:Set (FreeAmalgam R)) :=
    (le_inf (hQtGc.trans (Z_normalized R c)) (hQtG.trans hGC)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hGB : stabilizer R (alpha R)≤normalizer (B:Set (FreeAmalgam R)) := by
    rw [←s.residual_edge_generation rfl hat]
    exact sup_le hLB hQtB
  have hPB : P≤B := by
    dsimp only [P]
    rw [localZSpan_eq_conjugates]
    apply iSup_le
    intro g
    rintro _ ⟨z,hz,rfl⟩
    exact (mem_normalizer_iff.mp (hGB ((stabilizer R (alpha R)).inv_mem g.property)) z).mp
      ((show Z R c≤B from le_sup_left) hz)
  have hBC : B≤centralizer (B:Set (FreeAmalgam R)) := by
    apply sup_le
    · apply le_centralizer_iff.mpr
      let := s.geometry.Z_elementary s.criticalDistance_pos c hc
      exact sup_le (le_centralizer_iff_isMulCommutative.mpr inferInstance)
        (hCC.trans (centralizer_le hZP))
    · exact hCC.trans (centralizer_le hBP)
  have hab : ⁅P,P⁆=⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((hPB.trans hBC).trans (centralizer_le hPB))
  have hcard := (s.forward_span_derived_eq_line h u hfull hb p).2.1
  change Nat.card (⁅P,P⁆:Subgroup (FreeAmalgam R))=2 at hcard
  rw [hab,card_bot] at hcard
  omega

/-- The terminal central quotient carries a faithful action of the source quotient. -/
theorem exists_forward_span_faithful_symmetric_central_action
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    ∃ ρ : Model.S →* MulAut ((localZSpan R (p.walk.getVert 2) (alpha R)) ⧸
        center (localZSpan R (p.walk.getVert 2) (alpha R))),
      Function.Injective ρ ∧
      ∀ m : M, ρ (s.projection m)=forwardSpanCentralAction R (p.walk.getVert 2) m := by
  obtain ⟨ρ,hρ⟩ := s.exists_forward_span_symmetric_central_action h u hfull hb p
  exact ⟨ρ,s.forward_span_symmetric_central_action_injective h u hfull hb p ρ hρ,hρ⟩
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The terminal central quotient carries a faithful action of the literal
marked symmetric-six quotient. -/
@[expose] def FaithfulForwardSpanActionData (c : Vertex R) : Prop :=
  let P := localZSpan R c (alpha R)
  IsElementaryAbelian 2 (P⧸center P) ∧
    (Q R c).relIndex P≤2 ∧
    ∃ ρ : Model.S →* MulAut (P⧸center P), Function.Injective ρ ∧
      ∀ m : M, ρ (s.projection m)=forwardSpanCentralAction R c m

theorem faithful_forward_span_action_data
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    s.FaithfulForwardSpanActionData (p.walk.getVert 2) :=
  ⟨(s.forward_span_central_quotient h u hfull hb p).1,
    s.forward_span_second_vertex_index_le_two h u hfull hb p,
    s.exists_forward_span_faithful_symmetric_central_action h u hfull hb p⟩
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B:Subgroup K)

theorem reducedSource_block_or_faithful_forward_span_action
    (r : CharacteristicReduction (L.subgroupOf J) (d.B.subgroupOf J)) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4) :
    IsAlternatingBlock L 6 ∨
      ((originalSource d hm).reduce r).FaithfulForwardSpanActionData (p.walk.getVert 2) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.faithful_forward_span_action_data (reduced_nativeCentralLayer d hm r) _ hf hb p
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData

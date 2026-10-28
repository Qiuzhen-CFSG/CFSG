module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.InitialSections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborFixedLine
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborCoreClosure
public import Theory.Representation.BinaryConjugationSection.FixedImage

/-!
# The actual alpha omega action after initial recognition

The full edge Sylow fixes the image of Z_alpha in the natural beta section.
Its displacement is therefore in the original residual centralizer. The
whole alpha quotient omega preimage lies in W, so that displacement lies
in Z_alpha intersect Z(W) and commutes with the actor. This proves its
quadratic action on the unchanged Z_alpha, together with the field-order
index in 9.4(i) and the full-preimage containment in 9.4(iii).

Initial recognition supplies the beta marking and section in both branches.
The original catalogues, Chapter 8 reorientation and source 6.5 remain
explicit. The odd-torus fixed-space comparison in 9.4(ii), alpha linear
recognition, equal fields and the 9.5--9.11 distance/field arguments remain
separate obligations; none is inferred from these preliminary assertions.
Source: DGS, Groups and Graphs (1985), 9.4, printed p.143.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Representation.NormalElementaryQuotient
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The whole quotient omega-center acts quadratically on the actual alpha
center. Its first displacement lies in the literal center of W. -/
theorem reduced_natural_residual_omega_quadratic (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (M : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hres : NaturalResidualSection h beta e n) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    let W := conjugateSpanBy (Q Γ a) (stabilizer Γ beta)
    let Z₀ := Z Γ a ⊓ (Subgroup.center W).map W.subtype
    ∃ R : Sylow 2 H,
      (R : Subgroup H).map H.subtype = (stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2 ∧
      let Y := ((omegaCenterIn ((R : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)))).comap
        (QuotientGroup.mk' (pCore 2 H))).map H.subtype
      Y ≤ W ∧ ⁅Z Γ a,Y⁆ ≤ Z₀ ∧ Z₀ ≤ centralizer (Y : Set (Reduction.G₀ L S₀)) ∧
        ⁅⁅Z Γ a,Y⁆,Y⁆ = ⊥ ∧ Z₀.relIndex (Z Γ a) = Nat.card F := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a
  let Hβ := graphLocalGroup Γ beta
  let Aβ := (V Γ beta 1).subgroupOf Hβ
  let W := conjugateSpanBy (Q Γ a) (stabilizer Γ beta)
  let Z₀ := Z Γ a ⊓ (Subgroup.center W).map W.subtype
  let q := QuotientGroup.mk' (pCore 2 H)
  let qβ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Hβ))
  let E := (stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta Hβ (sylowGenerated_le _)
  have hresSave := hres
  obtain ⟨hb2,σ,R₀,hσ,hfaith,hnat,_,_⟩ := hres
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 Hβ
  have hcomp : σ.comp qβ = fixedQuotientAction Aβ (pResidual 2 Hβ) := MonoidHom.ext hσ
  obtain ⟨_,_,⟨c₀⟩,_⟩ := reduced_critical_residual_section h hc hab hd hb hcomm
  let c := hcomp.symm ▸ c₀
  obtain ⟨T,hT,hline,_,_⟩ := residual_neighbor_fixed_line ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hab.symm (core_escape_of_intersection_obstruction Γ (hob a beta hab))
    (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
    e σ c hfaith R₀ hn hF hnat
  obtain ⟨R,hR,hYW⟩ := reduced_neighbor_core_closure_omega_preimage h hob hab M
  change (R : Subgroup H).map H.subtype = E at hR
  let Y := ((omegaCenterIn ((R : Subgroup H).map q)).comap q).map H.subtype
  have hYE : Y ≤ E := by
    rw [←hR]
    apply map_mono
    have hh : (omegaCenterIn ((R : Subgroup H).map q)).comap q ≤
        ((R : Subgroup H).map q).comap q := comap_mono (map_subtype_le _)
    have hk : q.ker ≤ (R : Subgroup H) := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal R
    rwa [comap_map_eq_self hk] at hh
  obtain ⟨Rβ,hRβ⟩ := CommutingNontrivial.source_edge_core_local_sylow ht
    (Reduction.reduced_borel_core_sylow h) d hab.symm
  change Sylow 2 Hβ at Rβ
  change (Rβ : Subgroup Hβ).map Hβ.subtype = (stabilizer Γ beta ⊓ stabilizer Γ a).pCoreIn 2 at hRβ
  rw [inf_comm] at hRβ
  change (Rβ : Subgroup Hβ).map Hβ.subtype = E at hRβ
  have hEH : E ≤ Hβ := hRβ ▸ map_subtype_le _
  have hQE : Q Γ a ≤ E := Noncommuting.graph_Q_le_edgeCore ht hab
  have hEq : (E.subgroupOf Hβ).map qβ ≤ T := by
    have hTE : (T : Subgroup SL(2,F)) ≤ (E.subgroupOf Hβ).map qβ := by
      rw [←hT]
      exact map_mono (comap_mono hQE)
    exact (T.is_maximal' (((isPGroup_pCoreIn 2 _).comap_subtype (K := Hβ)).map qβ) hTE).le
  have hfixed : c.imageSpace (Z Γ a) ≤ fixedSpace (σ.comp qβ) (E.subgroupOf Hβ) := by
    change c.imageSpace (Z Γ a) = fixedSpace σ T at hline
    rw [hline]
    intro z hz l
    exact hz ⟨qβ l.val,hEq (mem_map_of_mem qβ l.property)⟩
  have hdisp := c.commutator_le_of_imageSpace_fixed E (Z Γ a) hEH
    (CommutingNontrivial.Z_neighbor_le_V Γ hab.symm) hfixed
  have hcenter : Z₀ = Z Γ a ⊓ centralizer ((pResidual 2 Hβ).map Hβ.subtype : Set (Reduction.G₀ L S₀)) :=
    neighbor_core_closure_center_intersection ht (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) hab.symm
      (core_escape_of_intersection_obstruction Γ (hob a beta hab)) e
  have hYZ : ⁅Z Γ a,Y⁆ ≤ Z₀ := by
    rw [hcenter]
    apply le_inf
    · exact le_normalizer_iff_commutator_le_left.mp
        (hYE.trans ((pCoreIn_le 2 _).trans
          (inf_le_left.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a))))
    · rw [commutator_comm]
      exact (commutator_mono hYE le_rfl).trans (hdisp.trans inf_le_right)
  have hZY : Z₀ ≤ centralizer (Y : Set (Reduction.G₀ L S₀)) := by
    rintro z ⟨_,zW,hzW,rfl⟩ y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hzW) ⟨y,hYW hy⟩)
  refine ⟨R,hR,hYW,hYZ,hZY,?_,?_⟩
  · apply _root_.eq_bot_iff.mpr
    exact (commutator_mono hYZ le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr hZY).le
  · change Z₀.relIndex (Z Γ a) = Nat.card F
    rw [hcenter,inf_relIndex_left]
    exact reduced_natural_residual_neighbor_index h hc hab hd hb hcomm (hob a beta hab) hn hF e hresSave

/-- Both initial-recognition branches construct the actual alpha omega
action and the index in 9.4(i), with no supplied residual representation or
alpha linear marking. The earlier catalogue, Chapter 8 and 6.5 remain inputs. -/
theorem reduced_critical_initial_alpha_action (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z, Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓ Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃* SL(2,F)))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))
    (Mαsource : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))) :
    let Γ := Reduction.reducedFamily L S₀
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) = Nat.card F ∧
        (centralizer ((pResidual 2 (graphLocalGroup Γ beta)).map
          (graphLocalGroup Γ beta).subtype : Set (Reduction.G₀ L S₀))).relIndex (Z Γ a) = Nat.card F ∧
        NaturalResidualSection h beta eβ n ∧
        let H := graphLocalGroup Γ a
        let W := conjugateSpanBy (Q Γ a) (stabilizer Γ beta)
        let Z₀ := Z Γ a ⊓ (Subgroup.center W).map W.subtype
        ∃ R : Sylow 2 H,
          (R : Subgroup H).map H.subtype = (stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2 ∧
          let Y := ((omegaCenterIn ((R : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)))).comap
            (QuotientGroup.mk' (pCore 2 H))).map H.subtype
          Y ≤ W ∧ ⁅Z Γ a,Y⁆ ≤ Z₀ ∧ Z₀ ≤ centralizer (Y : Set (Reduction.G₀ L S₀)) ∧
            ⁅⁅Z Γ a,Y⁆,Y⁆ = ⊥ ∧ Z₀.relIndex (Z Γ a) = Nat.card F := by
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hC,hC',hres⟩ :=
    reduced_critical_recognized_initial_section h hc hab hd hb hcomm htriv h8 hob Mα Mβ Mα'
  let := instF
  let := finF
  let := charF
  exact ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hC,hC',
    reduced_natural_residual_neighbor_index h hc hab hd hb hcomm (hob a beta hab) hn hF eβ hres,hres,
    reduced_natural_residual_omega_quadratic h hob hc hab hd hb hcomm Mαsource hn hF eβ hres⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

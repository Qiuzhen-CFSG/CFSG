module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThree
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.ActionKernel
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The actual residual section at the end of DGS 8.4

The local two-residual is transitive on neighbors, since the full edge
Sylow supplements it. If it centralized W/V_beta for W = V_beta^(3),
then V_alpha^(2) would have transitive normalizers at both ends of the
original edge. Faithfulness forces that span to vanish, contrary to its
nonzero center seed. This proves residual movement without a callback.

The quotient action is constructed on the literal W/V_beta. Movement
survives on its Frattini quotient, whose action kernel cannot contain an
escaping two-subgroup. This does not assume that W/V_beta is elementary,
that its action is faithful, or that the full local kernel equals Q.

Source: DGS, *Groups and Graphs* (1985), 3.2(c) and the final paragraph of
8.4, printed pp.72,138. `RadiusThreeResidualApplication` supplies the
original 8.2 actor and the linear fixed-index lower bound. The intersection
commutator upper bound and nonlinear module comparisons remain separate.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The original local two-residual is transitive on the actual neighbors.
Factorization by the full edge Sylow supplies representatives fixing no
unmarked substitute for the original neighboring vertex. -/
theorem source_local_residual_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    ∀ z, (graph (family P)).Adj v z →
      ∃ g ∈ (pResidual 2 (d.localGroup v)).map (d.localGroup v).subtype,
        g • w = z := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hvw
  have hTw : (T : Subgroup L).map L.subtype ≤ stabilizer (family P) w :=
    hT ▸ (pCoreIn_le 2 _).trans inf_le_right
  intro z hz
  obtain ⟨g,hg,hgz⟩ := d.transitive v ⟨w,hvw⟩ ⟨z,hz⟩
  have hg' : (⟨g,hg⟩ : L) ∈ pResidual 2 L ⊔ (T : Subgroup L) := by
    rw [pResidual_sup_sylow_eq_top T]
    trivial
  obtain ⟨e,he,t,ht,het⟩ := mem_sup_of_normal_left.mp hg'
  refine ⟨e,mem_map_of_mem L.subtype he,?_⟩
  have htw : (t : G) • w = w := hTw (mem_map_of_mem L.subtype ht)
  have heq : (e : G) * (t : G) = g := congrArg Subtype.val het
  simpa only [←heq,mul_smul,htw] using hgz

private theorem span_le_of_distance
    (F : Bool → Subgroup G) (hgen : F false ⊔ F true = ⊤)
    (v w : Vertex F) (r s : ℕ) (hd : (graph F).dist w v + r ≤ s) :
    V F v r ≤ V F w s := by
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  have hz' := (mem_ball_iff F hgen v z r).mp hz
  have ht := (connected F hgen).dist_triangle (u := w) (v := v) (w := z)
  exact le_iSup_of_le z (le_iSup_of_le
    ((mem_ball_iff F hgen w z s).mpr (by omega)) le_rfl)

/-- The last graph step of 8.4: for b > 3 the radius-three quotient by V_beta
must be moved by O²(L_beta). Otherwise V_alpha^(2) has two transitive local
normalizers and faithfulness kills its nonzero center seed. -/
theorem source_radius_three_residual_moves
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hb : 3 < b (family P)) :
    ¬ ⁅V (family P) beta 3,
      (pResidual 2 (d.localGroup beta)).map (d.localGroup beta).subtype⁆ ≤
        V (family P) beta 1 := by
  let := finite_endpoints h
  let F := family P
  let K := V F a 2
  let E := (pResidual 2 (d.localGroup beta)).map (d.localGroup beta).subtype
  change 3 < b F at hb
  have hVK : V F beta 1 ≤ K := span_le_of_distance F h.generate beta a 1 2
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab])
  have hKW : K ≤ V F beta 3 := span_le_of_distance F h.generate a beta 2 3
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab.symm])
  intro hmove
  have hEN : E ≤ normalizer (K : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono hKW le_rfl).trans hmove).trans hVK)
  have hKN : stabilizer F a ≤ normalizer (K : Set G) := stabilizer_normalizes_V F a 2
  have hKQ : K ≤ Q F a := V_le_Q_of_dist_add_lt_b F h.generate
    (fun v => (source_Z_Q_U h v).1) a a 2
    (by simp only [SimpleGraph.dist_self,zero_add]; omega) (d.kernel_sylow a)
  have hKedge : K ≤ stabilizer F a ⊓ stabilizer F beta :=
    le_inf (hKQ.trans (Q_le_stabilizer F a))
      (hKQ.trans ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge F hab).trans inf_le_right)))
  have hbot : K = ⊥ := source_normalized_edge_eq_bot h hab K hKedge
    (by
      intro z hz
      obtain ⟨g,hg,hgz⟩ := d.transitive a ⟨beta,hab⟩ ⟨z,hz⟩
      exact ⟨g,hKN (d.local_le a hg),hgz⟩)
    (by
      intro z hz
      obtain ⟨g,hg,hgz⟩ := source_local_residual_transitive h hB d hab.symm z hz
      exact ⟨g,hEN hg,hgz⟩)
  have hZbot : Z F a = ⊥ := bot_unique ((Z_le_V F a 2).trans hbot.le)
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F a
  rw [←hg,Z_translate,map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at hZbot
  exact base_Z_ne_bot h _ hZbot

/-- Construct the literal action on W/V_beta and prove residual movement
on it and its Frattini quotient. The Frattini action kernel meets every
two-subgroup inside the intrinsic local two-core. -/
theorem source_radius_three_quotient_action
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hb : 3 < b (family P))
    (M : IsRankOneModel (d.localGroup beta ⧸ pCore 2 (d.localGroup beta))) :
    let F := family P
    let W := V F beta 3
    let V₀ := V F beta 1
    let L := d.localGroup beta
    ∃ (hnW : L ≤ normalizer (W : Set G)) (hN : (V₀.subgroupOf W).Normal),
      let _ := hN
      ∃ α : L →* MulAut (W ⧸ V₀.subgroupOf W),
        (∀ l : L, ∀ x : W,
          α l (QuotientGroup.mk' (V₀.subgroupOf W) x) =
            QuotientGroup.mk' (V₀.subgroupOf W)
              ⟨(l : G) * (x : G) * (l : G)⁻¹,
                (mem_normalizer_iff.mp (hnW l.property) x).mp x.property⟩) ∧
        ¬ pResidual 2 L ≤ α.ker ∧
        ¬ pResidual 2 L ≤ ((quotientAut (frattini (W ⧸ V₀.subgroupOf W))).comp α).ker ∧
        ∀ A : Subgroup L, IsPGroup 2 A →
          A ⊓ ((quotientAut (frattini (W ⧸ V₀.subgroupOf W))).comp α).ker ≤ pCore 2 L := by
  let := finite_endpoints h
  let F := family P
  let W := V F beta 3
  let V₀ := V F beta 1
  let L := d.localGroup beta
  let : Finite L := Finite.of_injective (inclusion (d.local_le beta)) (inclusion_injective _)
  have hWQ : W ≤ Q F beta := V_le_Q_of_dist_add_lt_b F h.generate
    (fun v => (source_Z_Q_U h v).1) beta beta 3
    (by simpa only [SimpleGraph.dist_self,zero_add] using hb) (d.kernel_sylow beta)
  have hWP : W ≤ stabilizer F beta := hWQ.trans (Q_le_stabilizer F beta)
  let : Finite W := Finite.of_injective (inclusion hWP) (inclusion_injective _)
  have hpW : IsPGroup 2 W := (isPGroup_pCoreIn 2 (stabilizer F beta)).to_le hWQ
  have hWL : W ≤ L := pGroup_le_localGroup F d beta W hpW hWP
  have hnW : L ≤ normalizer (W : Set G) := (d.local_le beta).trans (stabilizer_normalizes_V F beta 3)
  have hnV : L ≤ normalizer (V₀ : Set G) := (d.local_le beta).trans (stabilizer_normalizes_V F beta 1)
  let hN : (V₀.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer (hWL.trans hnV)
  let X := W ⧸ V₀.subgroupOf W
  let : Finite X := Finite.of_surjective _ (QuotientGroup.mk'_surjective (V₀.subgroupOf W))
  obtain ⟨α,hα⟩ := exists_quotient_conjugation_action L W V₀ hnW hnV hN
  have hr : ¬ pResidual 2 L ≤ α.ker := by
    intro hr
    apply source_radius_three_residual_moves h hB d hab hb
    rw [commutator_comm]
    apply commutator_le.mpr
    rintro _ ⟨r,hr',rfl⟩ x hx
    have he := hα r ⟨x,hx⟩
    rw [show α r = 1 from hr hr'] at he
    have he' : QuotientGroup.mk' (V₀.subgroupOf W)
        ⟨(r : G) * x * (r : G)⁻¹,
          (mem_normalizer_iff.mp (hnW r.property) x).mp hx⟩ =
        QuotientGroup.mk' (V₀.subgroupOf W) ⟨x,hx⟩ := he.symm
    have hm := (QuotientGroup.eq_iff_div_mem (N := V₀.subgroupOf W)).mp he'
    change (r : G) * x * (r : G)⁻¹ / x ∈ V₀ at hm
    simpa only [commutatorElement_def,div_eq_mul_inv,subtype_apply,V₀,F] using hm
  have hφ := MonoidHom.residual_not_le_frattini_action_kernel
    (hpW.to_quotient (V₀.subgroupOf W)) α hr
  refine ⟨hnW,hN,α,hα,hr,hφ,?_⟩
  intro A hA
  let S : Sylow 2 L := default
  exact pGroup_inf_kernel_le_pCore_of_residual_not_le S
    (fun Y hSY hY => (rankOneSylowFacts_of_quotient S (M.rankOneSylowFacts _)).unique_maximal
      Y hSY (lt_top_iff_ne_top.mpr hY)) _ hφ A hA

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

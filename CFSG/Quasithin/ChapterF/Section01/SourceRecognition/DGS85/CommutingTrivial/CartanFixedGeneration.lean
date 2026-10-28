module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeCoreSection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedPropagation
public import Theory.Representation.BinaryConjugationSection.SL2NaturalGeneration
public import Theory.GroupTheory.Commutator.PointCentralizers

/-!
# Generation in the original natural core quotient

The original core section retains its actual quotient map and natural
coordinates. A supplement to the beta core maps onto the entire local
linear quotient, hence its commutator covers the natural core section.
This supplies the generation used by the second Hall--Witt step of
DGS 9.10(5), printed p.149. The final application kills the literal full
Cartan fixed subgroup; the earlier path products remain explicit inputs.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Two-path transitivity transfers the reciprocal terminal index to the
preceding span. The two literal outer spans then generate the beta local
group modulo its core, as used at the end of 9.10(5). -/
theorem graph_outer_spans_generate_local_group
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {l a beta x a' : Vertex (family P)}
    (hab : (graph (family P)).Adj a beta) (hal : (graph (family P)).Adj a l) (hlb : l ≠ beta)
    (hbx : (graph (family P)).Adj beta x) (hxa' : (graph (family P)).Adj x a')
    (hdb : a' ≠ beta) (hax : a ≠ x) (hb3 : b (family P) = 3)
    (ht : RootPathTransitive (graph (family P)) G beta 2)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eb : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hi : (Q (family P) beta).relIndex (V (family P) a' 1) = Nat.card F) :
    graphLocalGroup (family P) beta = Q (family P) beta ⊔
      (V (family P) l 1 ⊔ V (family P) a' 1) := by
  let := finite_endpoints h
  let Γ := family P
  let p : BasedWalk (graph Γ) 2 beta := ⟨⟨x,hbx⟩,⟨⟨a',hxa'⟩,PUnit.unit⟩⟩
  let q : BasedWalk (graph Γ) 2 beta := ⟨⟨a,hab.symm⟩,⟨⟨l,hal⟩,PUnit.unit⟩⟩
  obtain ⟨g,hgb,hpath⟩ := ht p q ⟨hdb,trivial⟩ ⟨hlb,trivial⟩
  have hgd : g • a' = l := by
    have hh : g • beta = beta ∧ g • x = a ∧ g • a' = l := by
      simpa only [p,q,BasedWalk.vertices,List.map_cons,List.map_nil,List.cons.injEq,and_true] using hpath
    exact hh.2.2
  have hil : (Q Γ beta).relIndex (V Γ l 1) = Nat.card F := by
    rw [←hgd,V_translate,←hgb,Q_translate]
    exact (relIndex_map_map_of_injective _ _ (MulAut.conj g).injective).trans hi
  have hb : 1 < b Γ := by rw [hb3]; decide
  have hdist {u v : Vertex Γ} (huv : (graph Γ).Adj u v) (hvb : (graph Γ).Adj v beta) :
      (graph Γ).dist u beta + 1 ≤ b Γ := by
    have hh := (connected Γ h.generate).dist_triangle (u := u) (v := v) (w := beta)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr huv,SimpleGraph.dist_eq_one_iff_adj.mpr hvb] at hh
    rw [hb3]
    omega
  have hp (v : Vertex Γ) : IsPGroup 2 (V Γ v 1) :=
    (isPGroup_pCoreIn 2 _).to_le
      (V_le_Q Γ h.generate (fun z => (source_Z_Q_U h z).1) (source_kernel_sylow h hB hS) v hb)
  have hlH := neighbor_le_graphLocalGroup h (source_kernel_sylow h hB hS) l beta hb
    (hdist hal.symm hab)
  have hdH := neighbor_le_graphLocalGroup h (source_kernel_sylow h hB hS) a' beta hb
    (hdist hxa'.symm hbx.symm)
  have hlA : V Γ l 1 ≤ stabilizer Γ a := V_le_stabilizer Γ h.generate l a
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hal.symm,hb3]; decide)
  have hdX : V Γ a' 1 ≤ stabilizer Γ x := V_le_stabilizer Γ h.generate a' x
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hxa'.symm,hb3]; decide)
  simpa only [sup_assoc] using linear_local_two_actor_generation h hB hS hab.symm hbx hax eb
    (V Γ l 1) (V Γ a' 1) hlH hdH (hp l) (hp a') hil hi hlA hdX

/-- The original kernel exclusions at alpha and alpha-plus-two force the
fixed part of the beta core into their core intersection. Coprime action
then gives the generation used in the first Hall--Witt step of 9.10(5). -/
theorem graph_cartan_core_commutator_generation
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {l a beta x a' : Vertex (family P)}
    (hab : (graph (family P)).Adj a beta) (hal : (graph (family P)).Adj a l) (hlb : l ≠ beta)
    (hbx : (graph (family P)).Adj beta x) (hxa' : (graph (family P)).Adj x a') (hdb : a' ≠ beta)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (ea : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,K))
    (ex : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,K))
    (C T : Subgroup G) [IsMulCommutative C]
    (hCE : C ≤ stabilizer (family P) a ⊓ stabilizer (family P) beta)
    (hCl : C ≤ stabilizer (family P) l) (hCx : C ≤ stabilizer (family P) x)
    (hCd : C ≤ stabilizer (family P) a')
    (hoC : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer (family P) a ⊓ stabilizer (family P) beta : Subgroup G).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) a ⊓ stabilizer (family P) beta : Subgroup G).pCoreIn 2 =
      stabilizer (family P) a ⊓ stabilizer (family P) beta)
    (hTC : T ≤ C) (ho : Odd (Nat.card T)) (hne : T ≠ ⊥)
    (hTa : Disjoint T (ballKernel (family P) a 1))
    (hTx : Disjoint T (ballKernel (family P) x 1))
    (hNQ : Q (family P) a ⊓ Q (family P) x ≤ Q (family P) beta) :
    Q (family P) beta = (Q (family P) a ⊓ Q (family P) x) ⊔ ⁅Q (family P) beta,T⁆ := by
  let := finite_endpoints h
  let Γ := family P
  let A := Q Γ beta ⊓ centralizer (T : Set G)
  have hCb : C ≤ stabilizer Γ beta := hCE.trans inf_le_right
  have hCnT : C ≤ normalizer (T : Set G) :=
    ((le_centralizer C).trans (centralizer_le hTC)).trans (Subgroup.centralizer_le_normalizer _)
  have hCnA : C ≤ normalizer (A : Set G) :=
    (le_inf (hCb.trans (stabilizer_normalizes_Q Γ beta))
      (hCnT.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hp : IsPGroup 2 A := (isPGroup_pCoreIn 2 _).to_le inf_le_left
  have hTA : T ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mp (show A ≤ centralizer (T : Set G) from inf_le_right)
  have hedge {v : Vertex Γ} (hbv : (graph Γ).Adj beta v) :
      A ≤ stabilizer Γ v ⊓ stabilizer Γ beta :=
    le_inf (inf_le_left.trans ((source_Z_Q_U h beta).2.trans
      ((ballKernel_one_le_edge Γ hbv).trans inf_le_right)))
      (inf_le_left.trans (Q_le_stabilizer Γ beta))
  have hAa : A ≤ Q Γ a := cartan_normalized_centralizing_two_subgroup_le_core h hB hS
    hab hal hlb ea C A T hCE hd hg (hedge hab.symm) hp hCnA hTC
    (hTC.trans hCl) hTA hne hTa
  have hCxb := le_inf hCx hCb
  obtain ⟨hdx,hgx⟩ := path_cartan_complement_at_edge h hab hbx.symm C hCE hCxb hoC hd hg
  have hAx : A ≤ Q Γ x := cartan_normalized_centralizing_two_subgroup_le_core h hB hS
    hbx.symm hxa' hdb ex C A T hCxb hdx hgx (hedge hbx) hp hCnA hTC
    (hTC.trans hCd) hTA hne hTx
  let : Finite (Q Γ beta) := Finite.of_injective (inclusion (Q_le_stabilizer Γ beta))
    (inclusion_injective _)
  let : Finite T := Finite.of_injective (inclusion (hTC.trans hCb)) (inclusion_injective _)
  have he := sup_eq_commutator_sup_of_fixed_le (Q Γ beta) (Q Γ a ⊓ Q Γ x) T
    (isPGroup_pCoreIn 2 _) ho (hTC.trans (hCb.trans (stabilizer_normalizes_Q Γ beta)))
    (le_inf hAa hAx)
  rwa [sup_eq_left.mpr hNQ,sup_comm] at he

/-- Naturality proves the required commutator supplement, using the literal
core-section coordinates and the full image of the original actor. -/
theorem core_section_commutator_generation
    (h : LocallyRankOneTriple P B) {a beta x : Vertex (family P)}
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hsec : CoreQuotientSection (family P) a beta x F eβ)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (W : Subgroup G)
    (hL : graphLocalGroup (family P) beta = Q (family P) beta ⊔ W) :
    Q (family P) beta = (Q (family P) a ⊓ Q (family P) x) ⊔ ⁅Q (family P) beta,W⁆ := by
  obtain ⟨hN,hcard,hElem,σ,d,hd,hnat⟩ := hsec
  let := hN
  let := hElem
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨E,hE⟩ := hnat n hn hF
  let H := graphLocalGroup (family P) beta
  let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := eβ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = (Q (family P) beta).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ eβ.injective,QuotientGroup.ker_mk']
    rw [←graphLocalGroup_core h beta]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hWH : W ≤ H := le_sup_right.trans hL.ge
  have hcore : ((Q (family P) beta).subgroupOf H).map q = ⊥ := by
    rw [←hk]
    exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
  have hW : (W.subgroupOf H).map q = ⊤ := by
    have hh := congrArg (fun U : Subgroup G => (U.subgroupOf H).map q) hL
    rw [subgroupOf_self,map_top_of_surjective _ hq,
      subgroupOf_sup (core_le_graphLocalGroup h beta) hWH,Subgroup.map_sup,hcore,bot_sup_eq] at hh
    exact hh.symm
  exact BinaryConjugationSection.natural_eq_kernel_sup_commutator H _ _ q σ d E hE W hWH hW

/-- The natural source section discharges the core-generation premise in
(5) for the two actual outer neighborhood modules and the full Cartan. -/
theorem graph_cartan_fixed_eq_bot_of_core_section
    (h : LocallyRankOneTriple P B) (a beta x l a' : Vertex (family P))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hsec : CoreQuotientSection (family P) a beta x F eβ)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) (C : Subgroup G)
    (hNQ : Q (family P) a ⊓ Q (family P) x ≤ Q (family P) beta)
    (hQN : Q (family P) a' ⊓ centralizer (C : Set G) ≤ Q (family P) a ⊓ Q (family P) x)
    (hL : graphLocalGroup (family P) beta = Q (family P) beta ⊔
      (V (family P) l 1 ⊔ V (family P) a' 1))
    (hcommN : ⁅Q (family P) a' ⊓ centralizer (C : Set G),Q (family P) a ⊓ Q (family P) x⁆ = ⊥)
    (hcommW : ⁅Q (family P) a' ⊓ centralizer (C : Set G),V (family P) l 1 ⊔ V (family P) a' 1⁆ = ⊥)
    (hBQ : ⁅Q (family P) beta,Q (family P) a' ⊓ centralizer (C : Set G)⁆ ≤ Z (family P) beta)
    (hZW : ⁅Z (family P) beta,V (family P) l 1 ⊔ V (family P) a' 1⁆ = ⊥)
    (hdis : Disjoint (Q (family P) a' ⊓ centralizer (C : Set G)) (Z (family P) beta)) :
    Q (family P) a' ⊓ centralizer (C : Set G) = ⊥ := by
  exact graph_cartan_fixed_eq_bot h beta _ _ _ hNQ hQN
    (core_section_commutator_generation h eβ hsec hn hF _ hL)
    hL hcommN hcommW hBQ hZW hdis

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

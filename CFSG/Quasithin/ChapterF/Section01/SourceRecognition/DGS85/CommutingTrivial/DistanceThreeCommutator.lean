module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CommutatorDichotomy
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThree

/-!
# The middle module in the distance-three branch of DGS 9.8

For the actual path (alpha,beta,x,alpha-prime), set
R = [V_beta,V_alpha-prime] and N = R Z_x. The sharp opposite index
saturates Q_x by V_beta and Q_x intersect Q_alpha-prime. Since R lies
in both elementary neighborhood spans, this bounds [N,Q_x] by the
central omega at alpha-prime. The two neighboring cores generate L_x
modulo Q_x and give [N,L_x] <= Z_x. Thus [N,Q_x] is normalized by L_x
and centralized by L_alpha-prime. Faithful edge propagation kills it.
Consequently N is a genuine L_x-submodule centralizing Q_x.

The original F1.11 application constructs the middle vertex and transports
both endpoint markings and the whole core-commutator identity along one
common edge conjugator. Both natural actions, the original quotient maps,
and the genuine catalogue, Chapter 8 and 6.5 inputs are retained. This
proves the opening b=3 reduction of 9.8; its subsequent torus argument,
5.17 splitting and the terminal 9.10--9.11 conclusions remain separate.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
9.8, printed p.145, using 9.3(b), 9.4(c), 9.6 and 3.2(c).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem neighbor_core_index
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hw : (graph (family P)).Adj v w)
    (he : ¬ Q (family P) w ≤ Q (family P) v)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    (Q (family P) v).relIndex (Q (family P) w) = Nat.card F := by
  let := finite_endpoints h
  let H := graphLocalGroup (family P) v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkmap : q.ker.map H.subtype = Q (family P) v := hk ▸ graphLocalGroup_core h v
  obtain ⟨T,hT,_⟩ := linear_neighbor_core_sylow_image h hB hS hw he e
  change ((Q (family P) w).subgroupOf H).map q = T at hT
  have hh := relIndex_ker ((Q (family P) w).subgroupOf H) q
  rw [←relIndex_map_map_of_injective _ _ H.subtype_injective,hkmap,
    map_subgroupOf_eq_of_le (neighbor_core_le_localGroup h hB hS hw),hT] at hh
  exact hh.trans (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv)

/-- The distance-three commutator, enlarged by the middle center, is an
actual local submodule centralizing the middle core. -/
theorem distance_three_commutator_middle_reduction
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {beta x a' : Vertex (family P)}
    (hbx : (graph (family P)).Adj beta x) (hxa' : (graph (family P)).Adj x a')
    (hd : (graph (family P)).dist beta a' = 2)
    (hb : b (family P) = 3)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (e' : (graphLocalGroup (family P) a' ⧸ pCore 2 (graphLocalGroup (family P) a')) ≃* SL(2,F))
    (ex : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,K))
    (hi : (Q (family P) a').relIndex (V (family P) beta 1) = Nat.card F)
    (hcβ : ⁅Q (family P) beta,V (family P) beta 1⁆ = Z (family P) beta)
    (hc' : ⁅Q (family P) a',V (family P) a' 1⁆ = Z (family P) a')
    (hωβ : Z (family P) beta = omegaCenterIn (graphLocalGroup (family P) beta))
    (hω' : Z (family P) a' = omegaCenterIn (graphLocalGroup (family P) a')) :
    let Γ := family P
    let R := ⁅V Γ beta 1,V Γ a' 1⁆
    let N := R ⊔ Z Γ x
    Q Γ x = V Γ beta 1 ⊔ (Q Γ x ⊓ Q Γ a') ∧
      N ≤ Q Γ x ∧ graphLocalGroup Γ x ≤ normalizer (N : Set G) ∧
      ⁅N,graphLocalGroup Γ x⁆ ≤ Z Γ x ∧ N ≤ centralizer (Q Γ x : Set G) := by
  let := finite_endpoints h
  let Γ := family P
  let R := ⁅V Γ beta 1,V Γ a' 1⁆
  let N := R ⊔ Z Γ x
  change b Γ = 3 at hb
  change (graph Γ).dist beta a' = 2 at hd
  have hZ := fun v => (source_Z_Q_U h v).1
  have hSyl := source_kernel_sylow h hB hS
  have hcorefix {v w : Vertex Γ} (hadj : (graph Γ).Adj v w) :
      Q Γ v ≤ stabilizer Γ w :=
    (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge Γ hadj).trans inf_le_right)
  have hspanQ {v w : Vertex Γ} (hadj : (graph Γ).Adj v w) : V Γ v 1 ≤ Q Γ w := by
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    apply Z_le_Q_of_dist_lt_b Γ hZ hSyl z w
    have hh := (connected Γ h.generate).dist_triangle (u := z) (v := v) (w := w)
    have hdist := (mem_ball_iff Γ h.generate v z 1).mp hz
    rw [SimpleGraph.dist_comm (u := z) (v := v),(SimpleGraph.dist_eq_one_iff_adj.mpr hadj)] at hh
    omega
  have hVQ : V Γ beta 1 ≤ Q Γ x := hspanQ hbx
  have hV'Q : V Γ a' 1 ≤ Q Γ x := hspanQ hxa'.symm
  have hVb : V Γ beta 1 ≤ stabilizer Γ a' := V_le_stabilizer Γ h.generate beta a' (by omega)
  have hVa' : V Γ a' 1 ≤ stabilizer Γ beta := V_le_stabilizer Γ h.generate a' beta (by
    rw [SimpleGraph.dist_comm]; omega)
  have hRβ : R ≤ V Γ beta 1 := le_normalizer_iff_commutator_le_left.mp
    (hVa'.trans (stabilizer_normalizes_V Γ beta 1))
  have hR' : R ≤ V Γ a' 1 := le_normalizer_iff_commutator_le_right.mp
    (hVb.trans (stabilizer_normalizes_V Γ a' 1))
  have hZxQ : Z Γ x ≤ Q Γ x := (hZ x).trans (fun _ hz => (mem_omegaCenterIn_iff _ _).mp hz |>.1)
  have hNQ : N ≤ Q Γ x := sup_le (hRβ.trans hVQ) hZxQ
  have hZxC := CommutingNontrivial.Z_centralizes_Q Γ x (hZ x)
  have hZβx : Z Γ beta ≤ Z Γ x := hωβ ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hbx
  have hZ'x : Z Γ a' ≤ Z Γ x := hω' ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hxa'.symm
  have hprod : Q Γ x = V Γ beta 1 ⊔ (Q Γ x ⊓ Q Γ a') :=
    linear_local_pgroup_saturation h a' e' _ _ hVQ
      (neighbor_core_le_localGroup h hB hS hxa'.symm) (isPGroup_pCoreIn 2 _) hi
  let := V_elementary Γ h.generate hZ hSyl beta (r := 1) (by omega : 2*1 < b Γ)
  have hQnZ' : Q Γ x ≤ normalizer (Z Γ a' : Set G) :=
    (hcorefix hxa').trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a')
  have hRQ : ⁅R,Q Γ x⁆ ≤ Z Γ a' := by
    rw [commutator_comm,hprod]
    apply commutator_sup_le_of_relative_normal (Q Γ x) _ _ R _ hQnZ' hVQ inf_le_left
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (hRβ.trans (le_centralizer _)))).le.trans bot_le
    · exact (commutator_mono inf_le_right hR').trans hc'.le
  have hNQbound : ⁅N,Q Γ x⁆ ≤ Z Γ a' := by
    apply commutator_sup_le_of_relative_normal (Q Γ x) R (Z Γ x) (Q Γ x) (Z Γ a')
      hQnZ' (hRβ.trans hVQ) hZxQ hRQ
    exact (commutator_eq_bot_iff_le_centralizer.mpr hZxC).le.trans bot_le
  have hQβZ : Q Γ beta ≤ normalizer (Z Γ x : Set G) :=
    (hcorefix hbx).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ x)
  have hQ'Z : Q Γ a' ≤ normalizer (Z Γ x : Set G) :=
    (hcorefix hxa'.symm).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ x)
  have hNZβ : ⁅N,Q Γ beta⁆ ≤ Z Γ x := by
    apply commutator_sup_le_of_relative_normal (V Γ beta 1) R (Z Γ x) (Q Γ beta) (Z Γ x)
      ?_ hRβ (CommutingNontrivial.Z_neighbor_le_V Γ hbx)
    · rw [commutator_comm]
      exact ((commutator_mono le_rfl hRβ).trans hcβ.le).trans hZβx
    · exact le_normalizer_iff_commutator_le_left.mp hQβZ
    · exact (hVQ.trans (Q_le_stabilizer Γ x)).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ x)
  have hNZ' : ⁅N,Q Γ a'⁆ ≤ Z Γ x := by
    apply commutator_sup_le_of_relative_normal (V Γ a' 1) R (Z Γ x) (Q Γ a') (Z Γ x)
      ?_ hR' (CommutingNontrivial.Z_neighbor_le_V Γ hxa'.symm)
    · rw [commutator_comm]
      exact ((commutator_mono le_rfl hR').trans hc'.le).trans hZ'x
    · exact le_normalizer_iff_commutator_le_left.mp hQ'Z
    · exact (hV'Q.trans (Q_le_stabilizer Γ x)).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ x)
  have hne : beta ≠ a' := by intro he; rw [he,SimpleGraph.dist_self] at hd; omega
  have hgen := linear_local_two_actor_generation h hB hS hbx.symm hxa' hne ex
    (Q Γ beta) (Q Γ a') (neighbor_core_le_localGroup h hB hS hbx.symm)
    (neighbor_core_le_localGroup h hB hS hxa')
    (isPGroup_pCoreIn 2 _) (isPGroup_pCoreIn 2 _)
    (neighbor_core_index h hB hS hbx.symm (core_escape_of_intersection_obstruction Γ (hob beta x hbx)) ex)
    (neighbor_core_index h hB hS hxa' (core_escape_of_intersection_obstruction Γ (hob a' x hxa'.symm)) ex)
    (Q_le_stabilizer Γ beta) (Q_le_stabilizer Γ a')
  have hLnZ : graphLocalGroup Γ x ≤ normalizer (Z Γ x : Set G) :=
    (sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ x)
  have hNL : ⁅N,graphLocalGroup Γ x⁆ ≤ Z Γ x := by
    rw [commutator_comm,hgen]
    apply commutator_sup_le_of_relative_normal (graphLocalGroup Γ x) _ _ N _ hLnZ
      (sup_le (core_le_graphLocalGroup h x) (neighbor_core_le_localGroup h hB hS hbx.symm))
      (neighbor_core_le_localGroup h hB hS hxa')
    · apply commutator_sup_le_of_relative_normal (graphLocalGroup Γ x) _ _ N _ hLnZ
        (core_le_graphLocalGroup h x) (neighbor_core_le_localGroup h hB hS hbx.symm)
      · rw [commutator_comm]; exact hNQbound.trans hZ'x
      · rwa [commutator_comm]
    · rwa [commutator_comm]
  have hLnN : graphLocalGroup Γ x ≤ normalizer (N : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hNL.trans le_sup_right)
  have hLnD : graphLocalGroup Γ x ≤ normalizer (⁅N,Q Γ x⁆ : Subgroup G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hLnN hg),
      mem_normalizer_iff_map_conj_eq.mp (stabilizer_normalizes_Q Γ x (sylowGenerated_le _ hg))]
  have hDzero : ⁅N,Q Γ x⁆ = ⊥ := by
    apply CommutingNontrivial.source_normalized_edge_eq_bot h hxa' _
      (hNQbound.trans (le_inf (hZ'x.trans (Z_le_stabilizer Γ x)) (Z_le_stabilizer Γ a')))
    · intro z hz
      obtain ⟨g,hg,he⟩ := graphLocalGroup_transitive h hB hS x ⟨a',hxa'⟩ ⟨z,hz⟩
      exact ⟨g,hLnD hg,he⟩
    · intro z hz
      obtain ⟨g,hg,he⟩ := graphLocalGroup_transitive h hB hS a' ⟨x,hxa'.symm⟩ ⟨z,hz⟩
      refine ⟨g,Subgroup.centralizer_le_normalizer _ ?_,he⟩
      apply centralizer_le hNQbound
      apply le_centralizer_iff.mp (show Z Γ a' ≤ centralizer (graphLocalGroup Γ a' : Set G) from ?_) hg
      rw [hω']
      exact fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).2.1
  exact ⟨hprod,hNQ,hLnN,hNL,commutator_eq_bot_iff_le_centralizer.mp hDzero⟩

universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The opening distance-three reduction in DGS 9.8 on the original F1.11
configuration, with both markings and natural actions constructed from the
genuine preceding source inputs. -/
theorem reduced_critical_distance_three_commutator
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb3 : b (Reduction.reducedFamily L S₀) = 3)
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z,
        Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓
        Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃*
              SL(2,F)))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓
          Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))
    (Mαsource : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
 :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸
        pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) = Nat.card F ∧
        NaturalResidualSection h beta eβ n ∧
        ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
          0 < m ∧ Nat.card K = 2^m ∧
          ∃ eα : (H ⧸ pCore 2 H) ≃* SL(2,K),
            Nat.card K = Nat.card F ∧
            ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅Q Γ beta,V Γ beta 1⁆ = Z Γ beta ∧
            (let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
            letI : Algebra (ZMod 2) K := ZMod.algebra K 2
            ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)))
              (T : Sylow 2 SL(2,K)),
              (∀ (l : H) (z : Additive (Z Γ a)),
                ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
                  (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
              Function.Injective ρ ∧ IsSourceNatural ρ T m ∧
              ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → K),
                ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) ∧
            ∃ x : Vertex Γ, (graph Γ).Adj beta x ∧ (graph Γ).Adj x a' ∧
              (Q Γ x = V Γ beta 1 ⊔ (Q Γ x ⊓ Q Γ a')) ∧
              (let N := ⁅V Γ beta 1,V Γ a' 1⁆ ⊔ Z Γ x
               N ≤ Q Γ x ∧ graphLocalGroup Γ x ≤ normalizer (N : Set (Reduction.G₀ L S₀)) ∧
                 ⁅N,graphLocalGroup Γ x⁆ ≤ Z Γ x ∧
                 N ≤ centralizer (Q Γ x : Set (Reduction.G₀ L S₀))) := by
  have hb : 1 < b (Reduction.reducedFamily L S₀) := by omega
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat⟩ :=
    reduced_critical_recognized_sections h hc hab hd hb hcomm htriv h8 hob Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hdist : (graph (Reduction.reducedFamily L S₀)).dist beta a' = 2 := by omega
  obtain ⟨x,hbx,hxa',t,htb,hta',ht2⟩ :=
    linear_distance_two_exchange ht hB hS hab hdist eα
  have htypes : beta.type = a'.type := by
    apply (even_dist_iff Γ ht.generate beta a').mp
    exact ⟨1,hdist⟩
  obtain ⟨g,hgb,hga⟩ := same_type_edge_transport Γ hab hxa' htypes
  obtain ⟨_,f',_,_,_⟩ := local_quotient_parameter_transport ht g hgb
  obtain ⟨_,fx,_,_,_⟩ := local_quotient_parameter_transport ht g hga
  have hω := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  have hω' : Z Γ a' = omegaCenterIn (graphLocalGroup Γ a') := by
    have hh := graphLocalGroup_conjugate ht g beta
    change graphLocalGroup Γ (g • beta) = (graphLocalGroup Γ beta).map (MulAut.conj g).toMonoidHom at hh
    change Z Γ beta = omegaCenterIn (graphLocalGroup Γ beta) at hω
    rw [←hgb,Z_translate,hh,
      ←NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g).injective,hω]
  have hcV' : ⁅Q Γ a',V Γ a' 1⁆ = Z Γ a' := by
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hcV
    rwa [map_commutator,←Q_translate,←V_translate,←Z_translate,hgb] at hh
  obtain ⟨hprod,hNQ,hLnN,hNL,hNC⟩ :=
    distance_three_commutator_middle_reduction ht hB hS hob hbx hxa' hdist hb3
      (f'.symm.trans eβ) (fx.symm.trans eα) hi hcV hcV' hω hω'
  exact ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
    K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,x,hbx,hxa',hprod,hNQ,hLnN,hNL,hNC⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

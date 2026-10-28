module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NaturalPair
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CommutatorBound

/-!
# The large-distance commutator dichotomy in DGS 9.8

Write R = [V_beta,V_alpha-prime] and w = alpha-prime-2. Apply the actual
shifted natural section to the already proved normal subgroup [R,Q_w].
It either equals V_w = Z_(alpha-prime-1) Z_(alpha-prime-3), or lies in Z_w.
In the central case, the single-intersection bound meets two disjoint
neighboring central omegas. The displacement therefore vanishes on one
core intersection, and the centralizer supplement and the 6.5 core product
make it vanish on Q_w. Since R is elementary, this gives R <= Z_w.

The F1.11 application constructs both original quotient markings, their
natural actions and the shifted natural section before using this dichotomy.
Catalogue, Chapter 8 and source 6.5 remain genuine earlier inputs. WholeSpan
carries both alternatives through the large-distance conclusion of 9.8.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
9.8, printed p.146, using 9.3--9.4 and 6.5.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- At a centerless linear vertex, central omegas of distinct neighbors
have trivial intersection. Local generation retains the actual two-cores. -/
theorem linear_central_neighbor_centers_disjoint
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w z : Vertex (family P)} (hw : (graph (family P)).Adj v w)
    (hz : (graph (family P)).Adj v z) (hne : w ≠ z)
    (hwe : ¬ Q (family P) w ≤ Q (family P) v)
    (hze : ¬ Q (family P) z ≤ Q (family P) v)
    (hωw : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    Z (family P) w ⊓ Z (family P) z = ⊥ := by
  let := finite_endpoints h
  let Γ := family P
  let I := Z Γ w ⊓ Z Γ z
  have hIZ : I ≤ Z Γ v := inf_le_left.trans (hωw ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hw.symm)
  have hIC : I ≤ centralizer (graphLocalGroup Γ v : Set G) := by
    apply le_centralizer_iff.mpr
    rw [linear_neighbor_core_generation h hB hS hw hz hne hwe hze e]
    apply sup_le (sup_le ?_ ?_) ?_
    · exact (le_centralizer_iff.mp (CommutingNontrivial.Z_centralizes_Q Γ v (source_Z_Q_U h v).1)).trans (centralizer_le hIZ)
    · exact (le_centralizer_iff.mp (CommutingNontrivial.Z_centralizes_Q Γ w (source_Z_Q_U h w).1)).trans (centralizer_le inf_le_left)
    · exact (le_centralizer_iff.mp (CommutingNontrivial.Z_centralizes_Q Γ z (source_Z_Q_U h z).1)).trans (centralizer_le inf_le_right)
  have hIω : I ≤ omegaCenterIn (graphLocalGroup Γ v) := by
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨core_le_graphLocalGroup h v (map_subtype_le _ ((source_Z_Q_U h v).1 (hIZ hx))),
        hIC hx,((mem_omegaCenterIn_iff _ _).mp (hωw ▸ hx.1)).2.2⟩
  exact bot_unique (hIω.trans_eq (intrinsic_local_omega_eq_bot_of_neighbor_central h hB hS hw hωw))

private theorem centralizes_neighbor_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {w v : Vertex (family P)} (hv : (graph (family P)).Adj w v)
    (R : Subgroup G)
    (hsupp : graphLocalGroup (family P) w =
      (graphLocalGroup (family P) w ⊓ centralizer (R : Set G)) ⊔ Q (family P) w)
    (hzero : ⁅R,Q (family P) w ⊓ Q (family P) v⁆ = ⊥) :
    ∀ r : Vertex (family P), (graph (family P)).Adj w r →
      ⁅R,Q (family P) w ⊓ Q (family P) r⁆ = ⊥ := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ w
  let C := H ⊓ centralizer (R : Set G)
  have hn : C ≤ normalizer (Q Γ w : Set G) :=
    (inf_le_left.trans (sylowGenerated_le _)).trans (stabilizer_normalizes_Q Γ w)
  intro r hr
  obtain ⟨g,hg,hgv⟩ := graphLocalGroup_transitive h hB hS w ⟨v,hv⟩ ⟨r,hr⟩
  change g • v = r at hgv
  have hg' : g ∈ C ⊔ Q Γ w := hsupp ▸ hg
  change g ∈ (↑(C ⊔ Q Γ w) : Set G) at hg'
  rw [coe_mul_of_left_le_normalizer_right C (Q Γ w) hn] at hg'
  obtain ⟨c,hc,q,hq,rfl⟩ := hg'
  have hqv : q • v = v := (source_Z_Q_U h w).2.trans
    ((ballKernel_one_le_edge Γ hv).trans inf_le_right) hq
  rw [mul_smul,hqv] at hgv
  have hcw : c • w = w := sylowGenerated_le _ hc.1
  have hRc : R.map (MulAut.conj c).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer (R : Set G) hc.2)
  have hh := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) hzero
  rw [map_commutator,hRc,Subgroup.map_inf _ _ _ (MulAut.conj c).injective,
    ←Q_translate,←Q_translate,hcw,hgv,Subgroup.map_bot] at hh
  exact hh

/-- The central alternative for the normal commutator forces R itself
into the local central omega. The single-intersection geometric bound and
6.5 core product rule out a nonzero central displacement. -/
theorem linear_commutator_central_alternative
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {w v r z : Vertex (family P)} (hv : (graph (family P)).Adj w v)
    (hr : (graph (family P)).Adj w r) (hz : (graph (family P)).Adj v z)
    (hne : v ≠ r) (hwz : w ≠ z)
    (hωw : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w))
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (ew : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F))
    (ev : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,K))
    (R : Subgroup G) [IsElementaryAbelian 2 R] (hRQ : R ≤ Q (family P) w)
    (hsupp : graphLocalGroup (family P) w =
      (graphLocalGroup (family P) w ⊓ centralizer (R : Set G)) ⊔ Q (family P) w)
    (hbound : ⁅R,Q (family P) w ⊓ Q (family P) v⁆ ≤ Z (family P) z)
    (hcentral : ⁅R,Q (family P) w⁆ ≤ Z (family P) w) : R ≤ Z (family P) w := by
  let := finite_endpoints h
  let Γ := family P
  have hi := linear_central_neighbor_centers_disjoint h hB hS hv.symm hz hwz
    (core_escape_of_intersection_obstruction Γ (hob w v hv))
    (core_escape_of_intersection_obstruction Γ (hob z v hz.symm)) hωw ev
  have hzero : ⁅R,Q Γ w ⊓ Q Γ v⁆ = ⊥ := bot_unique
    ((le_inf ((commutator_mono le_rfl inf_le_left).trans hcentral) hbound).trans_eq hi)
  have hzero' := centralizes_neighbor_intersection h hB hS hv R hsupp hzero r hr
  have hRC : R ≤ centralizer (Q Γ w : Set G) := by
    apply le_centralizer_iff.mpr
    rw [linear_middle_core_product h hB hS hob hv hr hne ew ev]
    apply sup_le
    · rw [inf_comm]
      exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
    · rw [inf_comm]
      exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero')
  have hRH : R ≤ centralizer (graphLocalGroup Γ w : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hsupp]
    exact sup_le inf_le_right (le_centralizer_iff.mp hRC)
  intro x hx
  rw [hωw]
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨core_le_graphLocalGroup h w (hRQ hx),hRH hx,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx⟩

/-- Ordered edges with the same types have a common transporter. -/
theorem same_type_edge_transport
    (Γ : Bool → Subgroup G) {a beta v w : Vertex Γ}
    (hab : (graph Γ).Adj a beta) (hvw : (graph Γ).Adj v w)
    (ht : beta.type = w.type) : ∃ g : G, g • beta = w ∧ g • a = v := by
  have ht' : a.type = v.type := by
    have ha := hab.1
    have hv := hvw.1
    cases ha' : a.type <;> cases hb' : beta.type <;>
      cases hv' : v.type <;> cases hw' : w.type <;> simp_all
  obtain ⟨g,ha,hb⟩ := incident_common_translate Γ hab.2
  obtain ⟨k,hv,hw⟩ := incident_common_translate Γ hvw.2
  refine ⟨k*g⁻¹,?_,?_⟩
  · rw [mul_smul,←hb,inv_smul_smul,ht,hw]
  · rw [mul_smul,←ha,inv_smul_smul,ht',hv]

universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}
/-- The actual large-distance alternative at the end of DGS 9.8. Both
original natural actions and the shifted natural section are constructed
before the normal-section dichotomy is applied. Earlier catalogue, Chapter 8
and 6.5 inputs remain explicit. -/
theorem reduced_critical_commutator_dichotomy
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 3 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (h8 : ChapterEightDistance (Reduction.reducedFamily L S₀))
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
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧ NaturalResidualSection h beta eβ n ∧
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
            ∃ v w r : Vertex Γ,
              (graph Γ).Adj a' v ∧ (graph Γ).Adj v w ∧ (graph Γ).Adj w r ∧ v ≠ r ∧
              (graph Γ).dist a v + 1 = b Γ ∧ (graph Γ).dist a w + 2 = b Γ ∧
              (graph Γ).dist beta v + 2 = b Γ ∧ (graph Γ).dist beta w + 3 = b Γ ∧
              (graph Γ).dist beta r + 4 = b Γ ∧
            ∃ ew : (graphLocalGroup Γ w ⧸ pCore 2 (graphLocalGroup Γ w)) ≃* SL(2,F),
              NaturalResidualSection h w ew n ∧
              (Q Γ w).relIndex (V Γ a 2) = Nat.card F ∧
              (∃ g : Reduction.G₀ L S₀, g • w = w ∧
                ⁅V Γ a' 1,(V Γ a 2).map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
                graphLocalGroup Γ w = Q Γ w ⊔ V Γ a 2 ⊔
                  (V Γ a 2).map (MulAut.conj g).toMonoidHom) ∧
              graphLocalGroup Γ w = (graphLocalGroup Γ w ⊓
                centralizer ((⁅V Γ beta 1,V Γ a' 1⁆ : Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀))) ⊔ Q Γ w ∧
              graphLocalGroup Γ w ≤ normalizer
                (⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w⁆ : Subgroup (Reduction.G₀ L S₀)) ∧
              ⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w⁆ ≤ Q Γ w ∧
              ⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w ⊓ Q Γ v⁆ ≤ Z Γ a' ∧
              ⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w⁆ ≤ Z Γ v ⊔ Z Γ r ∧
              ⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w⁆ ≤ V Γ w 1 ∧
              ((⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w⁆ = V Γ w 1 ∧
                V Γ w 1 = Z Γ v ⊔ Z Γ r) ∨
                ⁅V Γ beta 1,V Γ a' 1⁆ ≤ Z Γ w) := by
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
      v,w,r,hv,hw,hr,hne,hdav,hdaw,hdbv,hdbw,hdbr,
      ew,hresw,hiW,hgen,hsupp,hnorm,hDQ,hbound,hpair,hDV⟩ :=
    reduced_critical_commutator_geometric_bound h hc hab hd hb hcomm h8 hob Mα Mβ Mα' Mαsource
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
  have hZ := fun x => (source_Z_Q_U ht x).1
  have hSyl := Reduction.reduced_kernel_sylow h
  have hb1 : 1 < b Γ := by change 3 < b Γ at hb; omega
  have hb2 : 2 < b Γ := by change 3 < b Γ at hb; omega
  obtain ⟨hodd,_,hω,_⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb1 hcomm
  change (graph Γ).dist beta w + 3 = b Γ at hdbw
  change (graph Γ).dist beta a' + 1 = b Γ at hd
  have hbw : beta.type = w.type := by
    apply (even_dist_iff Γ ht.generate beta w).mp
    obtain ⟨k,hk⟩ := hodd
    change b Γ = 2*k+1 at hk
    change (graph Γ).dist beta w + 3 = b Γ at hdbw
    exact ⟨k-1,by omega⟩
  obtain ⟨g,hgw,hgv⟩ := same_type_edge_transport Γ hab hw hbw
  have hωw : Z Γ w = omegaCenterIn (graphLocalGroup Γ w) := by
    have hh := graphLocalGroup_conjugate ht g beta
    change graphLocalGroup Γ (g • beta) = (graphLocalGroup Γ beta).map (MulAut.conj g).toMonoidHom at hh
    change Z Γ beta = omegaCenterIn (graphLocalGroup Γ beta) at hω
    rw [←hgw,Z_translate,hh,
      ←NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g).injective,hω]
  have hcwv : ⁅Q Γ w,Z Γ v⁆ = Z Γ w := by
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hcQ
    rw [map_commutator,←Q_translate,←Z_translate,←Z_translate,hgw,hgv] at hh
    exact hh
  let := Z_elementary Γ hZ a
  obtain ⟨ρ,T,hact,hfaith,hna,E,hE⟩ := hnat
  obtain ⟨hca,hcb⟩ := linear_natural_neighbor_center_orders ht hB hS hab
    (core_escape_of_intersection_obstruction Γ (hob beta a hab.symm)) hω hm hK eα
    ρ hact hfaith ⟨T,hna⟩
  rw [heq] at hca hcb
  have hcv : Nat.card (Z Γ v) = Nat.card F ^ 2 := by
    have hh := card_map_of_injective (K := Z Γ a)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [←Z_translate,hgv] at hh
    exact hh.trans hca
  have hcw : Nat.card (Z Γ w) = Nat.card F := by
    have hh := card_map_of_injective (K := Z Γ beta)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [←Z_translate,hgw] at hh
    exact hh.trans hcb
  have hresw₀ := hresw
  let H := graphLocalGroup Γ w
  let A := (V Γ w 1).subgroupOf H
  let q := ew.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let := neighborhoodIn_normal Γ w H (sylowGenerated_le _)
  obtain ⟨hb2w,σ,Tw,hσ,hfaithw,hnatw,Ew,hEw⟩ := hresw
  let := neighborhoodIn_elementary Γ ht.generate hZ hSyl w hb2w H
  have hcomp : σ.comp q = Representation.NormalElementaryQuotient.fixedQuotientAction A (pResidual 2 H) := MonoidHom.ext hσ
  obtain ⟨⟨c⟩,_,_⟩ := neighborhood_residual_section ht hSyl w hb2w H
    (core_le_graphLocalGroup ht w) (sylowGenerated_le _)
  let : IsMulCommutative (V (family (fun i => (Reduction.P₀ L S₀ i).subgroupOf (Reduction.G₀ L S₀))) w 1) :=
    (V_elementary Γ ht.generate hZ hSyl w (r := 1) (by simpa using hb2)).toIsMulCommutative
  have hdich := natural_residual_normal_pair_dichotomy ht hB hS hw.symm hr hne
    (core_escape_of_intersection_obstruction Γ (hob v w hw))
    (core_escape_of_intersection_obstruction Γ (hob r w hr.symm)) hωw ew σ
    (hcomp.symm ▸ c) hfaithw Tw hn hF hnatw hcv hcw hcwv
    ⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w⁆ hpair hnorm
  refine ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hres,K,instK,finK,charK,m,hm,hK,eα,
    heq,hcQ,hcV,⟨ρ,T,hact,hfaith,hna,E,hE⟩,
    v,w,r,hv,hw,hr,hne,hdav,hdaw,hdbv,hdbw,hdbr,
    ew,hresw₀,hiW,hgen,hsupp,hnorm,hDQ,hbound,hpair,hDV,?_⟩
  rcases hdich with hcentral | hfull
  · right
    let R := ⁅V Γ beta 1,V Γ a' 1⁆
    have hRA : R ≤ V Γ beta 1 := le_normalizer_iff_commutator_le_left.mp
      ((V_le_stabilizer Γ ht.generate a' beta (by rw [SimpleGraph.dist_comm]; exact hd.le)).trans
        (stabilizer_normalizes_V Γ beta 1))
    let := V_elementary Γ ht.generate hZ hSyl beta (r := 1) (by simpa using hb2)
    let : IsElementaryAbelian 2 R := IsElementaryAbelian.of_injective
      (inclusion hRA) (inclusion_injective _)
    have hRQ : R ≤ Q Γ w := hRA.trans (by
      apply iSup_le
      intro x
      apply iSup_le
      intro hx
      apply Z_le_Q_of_dist_lt_b Γ hZ hSyl x w
      have hx' := (mem_ball_iff Γ ht.generate beta x 1).mp hx
      have hh := (connected Γ ht.generate).dist_triangle (u := x) (v := beta) (w := w)
      rw [SimpleGraph.dist_comm (u := x) (v := beta)] at hh
      omega)
    obtain ⟨_,fv,_,_,_⟩ := local_quotient_parameter_transport ht g hgv
    have hwz : w ≠ a' := by intro he; rw [he] at hdbw; omega
    exact linear_commutator_central_alternative ht hB hS hob hw.symm hr hv.symm hne hwz
      hωw ew (fv.symm.trans eα) R hRQ hsupp hbound hcentral
  · exact Or.inl hfull


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

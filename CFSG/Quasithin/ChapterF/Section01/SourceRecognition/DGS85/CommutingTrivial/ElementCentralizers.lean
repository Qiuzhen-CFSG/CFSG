module
public import Theory.Representation.BinaryConjugationSection.SL2ElementCentralizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.WholeSpan

/-!
# Element centralizers in both critical neighborhood sections

The sharp original indices in 9.3 and the faithful natural sections identify
the centralizer of every opposing element outside the local two-core. The
whole-span theorem then identifies these fixed subgroups with the literal
forward and backward path centers. The reverse application constructs its
markings by a common edge transporter and uses the same field and quotient
maps. Both natural actions and every earlier-source premise are retained.

This supplies the single-element fixed-subgroup step in the characteristic-two
argument of DGS 9.11, printed p.151. It does not yet prove the distance-five
contradiction or the terminal field-two conclusions.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative Pointwise

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- Every element outside the original two-core has the full actor centralizer. -/
theorem reduced_natural_residual_element_centralizer
    (h : HypothesisF11 L S₀) (beta : Vertex (Reduction.reducedFamily L S₀))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hres : NaturalResidualSection h beta e n)
    (A : Subgroup (Reduction.G₀ L S₀)) (hp : IsPGroup 2 A)
    (hAH : A ≤ graphLocalGroup (Reduction.reducedFamily L S₀) beta)
    (hi : (centralizer (A : Set (Reduction.G₀ L S₀))).relIndex
      (V (Reduction.reducedFamily L S₀) beta 1) = Nat.card F)
    {t : Reduction.G₀ L S₀} (ht : t ∈ A) (htQ : t ∉ Q (Reduction.reducedFamily L S₀) beta) :
    let Γ := Reduction.reducedFamily L S₀
    V Γ beta 1 ⊓ centralizer (zpowers t : Set (Reduction.G₀ L S₀)) =
      V Γ beta 1 ⊓ centralizer (A : Set (Reduction.G₀ L S₀)) := by
  let hl := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let W := (V Γ beta 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : ∀ i, Finite (Γ i) := finite_endpoints hl
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,σ,T,hσ,hfaith,hnat,E,hE⟩ := hres
  let := neighborhoodIn_elementary Γ hl.generate (fun v => (source_Z_Q_U hl v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  have hcomp : σ.comp q = Representation.NormalElementaryQuotient.fixedQuotientAction W (pResidual 2 H) :=
    MonoidHom.ext hσ
  obtain ⟨⟨c⟩,_,_⟩ := neighborhood_residual_section hl (Reduction.reduced_kernel_sylow h)
    beta hb2 H (core_le_graphLocalGroup hl beta) (sylowGenerated_le _)
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (V Γ beta 1) := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  obtain ⟨T',hT'⟩ := (hp.comap_subtype.map q).exists_le_sylow
  apply Representation.BinaryConjugationSection.element_centralizer_eq_of_sharp_linear_index
    q σ (hcomp.symm ▸ c) hfaith T' hF A hAH hT' hi ht
  intro he
  have hker : (⟨t,hAH ht⟩ : H) ∈ pCore 2 H := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact e.injective (he.trans e.map_one.symm)
  apply htQ
  exact (graphLocalGroup_core hl beta).le (mem_map_of_mem H.subtype hker)


/-- Both exact element centralizers on the original reduced critical path,
with the recognized fields and both natural sections retained. -/
theorem reduced_critical_large_distance_element_centralizers
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
            ∃ x v : Vertex Γ,
              (graph Γ).Adj beta x ∧ (graph Γ).dist x a' + 2 = b Γ ∧
              (graph Γ).Adj a' v ∧ (graph Γ).dist beta v + 2 = b Γ ∧
              V Γ beta 1 = Z Γ a ⊔ Z Γ x ∧ Nat.card (V Γ beta 1) = Nat.card F ^ 3 ∧
              V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) = Z Γ x ∧
              V Γ a' 1 ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) = Z Γ v ∧
              ⁅V Γ beta 1,V Γ a' 1⁆ ≤ Z Γ v ⊓ Z Γ x ∧
              (∀ t ∈ V Γ a' 1, t ∉ Q Γ beta →
                V Γ beta 1 ⊓ centralizer (zpowers t : Set (Reduction.G₀ L S₀)) = Z Γ x) ∧
              (∀ t ∈ V Γ beta 1, t ∉ Q Γ a' →
                V Γ a' 1 ⊓ centralizer (zpowers t : Set (Reduction.G₀ L S₀)) = Z Γ v) := by
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
      x,v,hx,hdx,hv,hdv,hwhole,hcard,hcent,hcent',hR⟩ :=
    reduced_critical_large_distance_whole_span h hc hab hd hb hcomm h8 hob Mα Mβ Mα' Mαsource
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
  have hZ := fun y => (source_Z_Q_U ht y).1
  have hSyl := Reduction.reduced_kernel_sylow h
  have hb1 : 1 < b Γ := by change 3 < b Γ at hb; omega
  have hb2 : 2 < b Γ := by change 3 < b Γ at hb; omega
  obtain ⟨hodd,_,hω,_⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb1 hcomm
  obtain ⟨htriv,hrev,_,hi',_⟩ := reduced_large_distance_natural_section h h8 hob
    hc hab hd hb hcomm hn hF eα eβ
  have hescape := linear_critical_reciprocal_escape ht hB hS hc hab hd hb2 hodd eα eβ
  obtain ⟨z,hz,hzc,_⟩ := reduced_reverse_criticalPair h hSyl hd hescape
  have hzcomm := reverse_critical_centers_commute ht hzc hω
  have hd' : (graph Γ).dist a' beta + 1 = b Γ := by rwa [SimpleGraph.dist_comm]
  have hbt : beta.type = a'.type := by
    apply (even_dist_iff Γ ht.generate beta a').mp
    obtain ⟨k,hk⟩ := hodd
    change b Γ = 2*k+1 at hk
    change (graph Γ).dist beta a' + 1 = b Γ at hd
    exact ⟨k,by omega⟩
  obtain ⟨g,hgb,hga⟩ := same_type_edge_transport Γ hab hz.symm hbt
  obtain ⟨_,fa,_,_,_⟩ := local_quotient_parameter_transport ht g hga
  obtain ⟨_,fb,_,_,_⟩ := local_quotient_parameter_transport ht g hgb
  let ez := fa.symm.trans eα
  let e' := fb.symm.trans eβ
  obtain ⟨_,_,_,_,hres'⟩ := reduced_large_distance_natural_section h h8 hob
    hzc hz.symm hd' hb hzcomm hn hF ez e'
  have hC := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ beta 1))
    (reduced_neighbor_centralizer_eq_core_inter h beta a' hb1 hd htriv)
  change (V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) =
    (V Γ beta 1 ⊓ Q Γ a').relIndex (V Γ beta 1) at hC
  simp only [inf_relIndex_left] at hC
  have hC' := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ a' 1))
    (reduced_neighbor_centralizer_eq_core_inter h a' beta hb1 hd' hrev)
  change (V Γ a' 1 ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) =
    (V Γ a' 1 ⊓ Q Γ beta).relIndex (V Γ a' 1) at hC'
  simp only [inf_relIndex_left] at hC'
  let := V_elementary Γ ht.generate hZ hSyl beta (r := 1) (by simpa using hb2)
  let := V_elementary Γ ht.generate hZ hSyl a' (r := 1) (by simpa using hb2)
  refine ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hres,K,instK,finK,charK,m,hm,hK,eα,
    heq,hcQ,hcV,hnat,x,v,hx,hdx,hv,hdv,hwhole,hcard,hcent,hcent',hR,?_,?_⟩
  · intro t htV htQ
    exact (reduced_natural_residual_element_centralizer h beta hF eβ hres (V Γ a' 1)
      (IsElementaryAbelian.isPGroup 2 _) (neighbor_le_graphLocalGroup ht hSyl a' beta hb1 hd'.le)
      (hC.trans hi) htV htQ).trans hcent
  · intro t htV htQ
    exact (reduced_natural_residual_element_centralizer h a' hF e' hres' (V Γ beta 1)
      (IsElementaryAbelian.isPGroup 2 _) (neighbor_le_graphLocalGroup ht hSyl beta a' hb1 hd.le)
      (hC'.trans hi') htV htQ).trans hcent'
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

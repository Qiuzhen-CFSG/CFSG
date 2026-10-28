module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.PathReciprocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AlphaRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ConstituentIndices

/-!
# Reciprocal escape and the first nonregular path on the recognized source graph

The two quotient markings constructed in 9.3--9.4 feed the unrestricted
path argument. It supplies 9.5's endpoint-orbit implication and 9.6's reverse
escape, reverse zero commutator, and exact index. Both original recognition
branches retain their natural sections, literal actions and equal fields.
The genuine earlier catalogue, Chapter 8 and 6.5 premises remain explicit.

The radius-two containment below is the first clause of 9.7 at the actual
second predecessor; its escape and the subsequent 9.8--9.11 argument are
still separate obligations. No distance-three or field-two premise is used.
Source: DGS, Groups and Graphs (1985), 9.5--9.7, printed pp.143--145.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Source 9.5--9.6 with both quotient markings and natural sections constructed
from the earlier-source inputs. The first nonregular path is also constructed. -/
theorem reduced_critical_reciprocal_sections
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
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
            (¬ V Γ a' 1 ≤ Q Γ beta) ∧
            ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ = ⊥ ∧
            (Q Γ beta).relIndex (V Γ a' 1) = Nat.card F ∧
            CriticalPathOrbit Γ a' ∧
            ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅Q Γ beta,V Γ beta 1⁆ = Z Γ beta ∧
            let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
            letI : Algebra (ZMod 2) K := ZMod.algebra K 2
            ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)))
              (T : Sylow 2 SL(2,K)),
              (∀ (l : H) (z : Additive (Z Γ a)),
                ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
                  (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
              Function.Injective ρ ∧ IsSourceNatural ρ T m ∧
              ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → K),
                ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z) := by
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hC,hC',hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat⟩ :=
    reduced_critical_recognized_sections h hc hab hd hb hcomm htriv h8 hob Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  have ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  obtain ⟨hodd,hb3,_⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm
  have hb2 : 2 < b (Reduction.reducedFamily L S₀) := Nat.lt_of_lt_of_le (by decide) hb3
  have he := linear_critical_reciprocal_escape ht hB hS hc hab hd hb2 hodd eα eβ
  have hrev := reduced_reverse_displacement_of_chapterEight h hc hab hd hb hcomm htriv he h8
  have hi := (reduced_large_neighbor_linear_indices h hc hab hd hb hcomm htriv he h8 hn hF eβ).2.1
  have hpath := critical_first_path_orbit ht hB hS hc hab hd hb2 hodd eα eβ
  exact ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hC,hC',hres,
    K,instK,finK,charK,m,hm,hK,eα,heq,he,hrev,hi,hpath,hcQ,hcV,hnat⟩

/-- The actual second predecessor carries the radius-two span W of 9.7.
Only the original critical path and b > 2 are required for this containment. -/
theorem reduced_radius_two_predecessor_containment
    (h : HypothesisF11 L S₀)
    {a a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hb : 2 < b (Reduction.reducedFamily L S₀)) :
    let Γ := Reduction.reducedFamily L S₀
    ∃ v w : Vertex Γ, (graph Γ).Adj v a' ∧ (graph Γ).Adj w v ∧
      (graph Γ).dist a v + 1 = b Γ ∧
      (graph Γ).dist a w + 2 = b Γ ∧
      V Γ a 2 ≤ graphLocalGroup Γ w := by
  let Γ := Reduction.reducedFamily L S₀
  change 2 < b Γ at hb
  have ht := Reduction.reduced_triple h
  have hne : a ≠ a' := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self] at hh
    change 0 = b Γ at hh
    omega
  obtain ⟨v,hv,hvd⟩ := exists_predecessor Γ ht.generate a a' hne
  have hdv : (graph Γ).dist a v + 1 = b Γ := hvd.trans hc.1
  have hne' : a ≠ v := by
    intro he
    rw [he,SimpleGraph.dist_self] at hdv
    omega
  obtain ⟨w,hw,hwd⟩ := exists_predecessor Γ ht.generate a v hne'
  have hdw : (graph Γ).dist a w + 2 = b Γ := by omega
  exact ⟨v,w,hv.symm,hw.symm,hdv,hdw,
    span_le_localGroup_of_distance ht a w hdw.le⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

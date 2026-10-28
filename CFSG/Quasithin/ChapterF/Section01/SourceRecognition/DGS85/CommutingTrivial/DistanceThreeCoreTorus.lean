module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeCoreFixed

/-!
# The actual torus and its distance-three core factors

The unrestricted distance-three reduction supplies both local markings,
both original natural sections, and the natural core quotient. Short-path
transitivity places a beta torus isomorphic to the units of the same field
in the fixer of the entire critical path. In the nonbinary case its fixed
subgroup lies in the radius-two kernel, and the middle-core intersection
splits into this fixed subgroup and the torus displacement of V_beta.

The odd-centralizer radius bound is also retained on the entire beta vertex
orbit for the reorientation in §9.10(3). Catalogue, Chapter 8 and genuine
6.5 inputs remain explicit. The two field-two conclusions and §5.17's larger
Q/Z splitting are subsequent source obligations.

Source: DGS, *Groups and Graphs* (1985), §9.10, printed pp.147--148.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The actual critical path carries its beta torus, radius-two fixed
subgroup, and direct product decomposition of the middle-core intersection.
Both natural sections and quotient markings remain attached to their original
actors; the field degree is not asserted to be one. -/
theorem reduced_critical_distance_three_core_fixed
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (h8distance : ChapterEightDistance (Reduction.reducedFamily L S₀))
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
    b Γ = 3 ∧
    let H := graphLocalGroup Γ a
    let := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
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
            let : Algebra (ZMod 2) K := ZMod.algebra K 2
            ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)))
              (T : Sylow 2 SL(2,K)),
              (∀ (l : H) (z : Additive (Z Γ a)),
                ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
                  (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
              Function.Injective ρ ∧ IsSourceNatural ρ T m ∧
              ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → K),
                ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) ∧
            ∃ x : Vertex Γ, (graph Γ).Adj beta x ∧ (graph Γ).Adj x a' ∧
              ⁅V Γ beta 1,V Γ a' 1⁆ ≤ Z Γ x ∧
              V Γ beta 1 = Z Γ a ⊔ Z Γ x ∧ Nat.card (V Γ beta 1) = Nat.card F ^ 3 ∧
              V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) = Z Γ x ∧
              (let N := Q Γ a ⊓ Q Γ x
               N = Q Γ beta ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) ∧
               N ≤ Q Γ beta ∧ V Γ beta 1 ≤ N ∧
               stabilizer Γ beta ≤ normalizer (N : Set (Reduction.G₀ L S₀)) ∧
               ⁅Q Γ beta ⊓ Q Γ x,V Γ a' 1⁆ ≤ Z Γ x ∧
               ⁅N,(pResidual 2 (graphLocalGroup Γ beta)).map (graphLocalGroup Γ beta).subtype⁆ ≤ V Γ beta 1 ∧
               CoreQuotientSection Γ a beta x F eβ ∧
               N = Q Γ beta ⊓ ballKernel Γ beta 2 ∧
               (∀ z : Vertex Γ, (graph Γ).Adj beta z → N ≤ Q Γ z) ∧
               ∃ D : Subgroup (Reduction.G₀ L S₀),
                 D ≤ graphLocalGroup Γ beta ⊓ stabilizer Γ a ⊓ stabilizer Γ x ⊓ stabilizer Γ a' ∧
                 Nonempty (D ≃* Fˣ) ∧ Nat.card D = Nat.card F - 1 ∧ Odd (Nat.card D) ∧
                 (1 < n → D ≠ ⊥ ∧
                   Q Γ beta ⊓ centralizer (D : Set (Reduction.G₀ L S₀)) =
                     N ⊓ centralizer (D : Set (Reduction.G₀ L S₀)) ∧
                   Q Γ beta ⊓ centralizer (D : Set (Reduction.G₀ L S₀)) ≤ ballKernel Γ beta 2 ∧
                   let C := Q Γ beta ⊓ centralizer (D : Set (Reduction.G₀ L S₀))
                   N = V Γ beta 1 ⊔ C ∧ ⁅N,D⁆ = ⁅V Γ beta 1,D⁆ ∧
                     N = ⁅V Γ beta 1,D⁆ ⊔ C ∧ Disjoint ⁅V Γ beta 1,D⁆ C ∧
                     ⁅⁅V Γ beta 1,D⁆,C⁆ = ⊥) ∧
                 (1 < n → ∀ v : Vertex Γ, beta.type = v.type →
                   ∀ T : Subgroup (Reduction.G₀ L S₀), T ≤ graphLocalGroup Γ v →
                     Odd (Nat.card T) → T ≠ ⊥ →
                     Q Γ v ⊓ centralizer (T : Set (Reduction.G₀ L S₀)) ≤ ballKernel Γ v 2)) := by
  obtain ⟨hb3,F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
      x,hbx,hxa',hR,hspan,hcard,hcentral,hN,hNQ,hVN,hNN,hD,hresN,hsec⟩ :=
    reduced_critical_distance_three_core_section h hc hab hd hb h8distance hcomm htriv h8 hob
      Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let hB := Reduction.reduced_borel_core_sylow h
  let hS := Reduction.reduced_vertex_sylow h
  have hsecond := core_intersection_eq_second_kernel ht hB hS hab hbx hNQ hNN
  have hneighbors (z : Vertex Γ) (hz : (graph Γ).Adj beta z) :=
    core_intersection_le_neighbor_core ht hB hS hab hbx hNQ hNN hz
  let p : BasedWalk (graph Γ) 3 a := ⟨⟨beta,hab⟩,⟨⟨x,hbx⟩,⟨⟨a',hxa'⟩,PUnit.unit⟩⟩⟩
  have hgeo : (graph Γ).dist a a' = 3 := hc.1.trans hb3
  have hp : p.Nonbacktracking := nonbacktracking_of_geodesic p hgeo
  have htrans := adjacent_linear_short_path_transitive ht hB hS hob hab eα eβ a 3 (by omega)
  obtain ⟨D,hDpath,⟨eD⟩⟩ := linear_path_torus ht hB hS p hp htrans hbx
    (by exact List.Mem.tail _ (List.Mem.head _))
    (by exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) eβ
  have hDH : D ≤ graphLocalGroup Γ beta := hDpath.trans inf_le_left
  have hDa : D ≤ stabilizer Γ a := fun d hd => hDpath hd |>.2 a (by exact List.Mem.head _)
  have hDx : D ≤ stabilizer Γ x := fun d hd => hDpath hd |>.2 x (by exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hDa' : D ≤ stabilizer Γ a' := fun d hd => hDpath hd |>.2 a' (by exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hDcard : Nat.card D = Nat.card F - 1 := by
    rw [Nat.card_congr eD.toEquiv,Nat.card_units]
  have hDodd : Odd (Nat.card D) := by
    rw [hDcard,hF]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (by omega : n ≠ 0)) odd_one
  have hfixed (hn' : 1 < n) (T : Subgroup (Reduction.G₀ L S₀))
      (hTH : T ≤ graphLocalGroup Γ beta) (ho : Odd (Nat.card T)) (hne : T ≠ ⊥) :=
    core_section_odd_centralizer eβ hsec hn' hF T hTH ho hne
  refine ⟨hb3,F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
    K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
    x,hbx,hxa',hR,hspan,hcard,hcentral,hN,hNQ,hVN,hNN,hD,hresN,hsec,
    hsecond,hneighbors,D,le_inf (le_inf (le_inf hDH hDa) hDx) hDa',
    ⟨eD⟩,hDcard,hDodd,?_,?_⟩
  · intro hn'
    have hne : D ≠ ⊥ := by
      intro he
      have hh : 2 < 2^n := by
        have hpow := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn'
        simpa using hpow
      rw [he,card_bot,hF] at hDcard
      omega
    have hf := hfixed hn' D hDH hDodd hne
    exact ⟨hne,hf,(hf.le.trans inf_le_left).trans (hsecond.le.trans inf_le_right),
      middle_core_torus_decomposition ht hN hVN hNN hresN eβ hsec hn' hF D hDH hDodd hne⟩
  · intro hn'
    apply odd_core_centralizer_radius_transport ht
    intro T hTH ho hne
    exact ((hfixed hn' T hTH ho hne).le.trans inf_le_left).trans (hsecond.le.trans inf_le_right)


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

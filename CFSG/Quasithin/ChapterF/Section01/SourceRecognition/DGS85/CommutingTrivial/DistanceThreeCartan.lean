module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.TorusKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeCoreFixed

/-!
# The full Cartan on the original distance-three critical path

The unrestricted distance reduction and core-section construction provide
both original local markings and natural actions. A single full edge
complement fixes the entire critical path. Its two intrinsic local factors
are the unit groups of those same fields and form an internal direct product.
In the nonbinary case each factor avoids its own full permutation kernel.

The consumer retains the second-kernel identification of the middle-core
intersection and the odd-centralizer radius bound on the entire beta orbit.
Catalogue, Chapter 8 and genuine source 6.5 premises remain explicit. The
neighboring-vertex kernel exclusions, 5.17 splitting and field-two
contradiction are subsequent source obligations.

Source: DGS, *Groups and Graphs* (1985), 9.9--9.10(3), printed pp.147--148.
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

/-- A single full Cartan fixes the actual critical path, splits into its two
marked local tori, and has the intrinsic kernel exclusions in the nonbinary
case. Both original natural sections and the core quotient are retained. -/
theorem reduced_critical_distance_three_cartan
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
               ∃ C : Subgroup (Reduction.G₀ L S₀),
                 C ≤ stabilizer Γ a ⊓ stabilizer Γ beta ⊓ stabilizer Γ x ⊓ stabilizer Γ a' ∧
                 Disjoint C ((stabilizer Γ a ⊓ stabilizer Γ beta : Subgroup (Reduction.G₀ L S₀)).pCoreIn 2) ∧
                 C ⊔ (stabilizer Γ a ⊓ stabilizer Γ beta : Subgroup (Reduction.G₀ L S₀)).pCoreIn 2 =
                   stabilizer Γ a ⊓ stabilizer Γ beta ∧
                 Odd (Nat.card C) ∧ IsMulCommutative C ∧
                 Nonempty ((C ⊓ graphLocalGroup Γ a : Subgroup (Reduction.G₀ L S₀)) ≃* Kˣ) ∧
                 Nonempty ((C ⊓ graphLocalGroup Γ beta : Subgroup (Reduction.G₀ L S₀)) ≃* Fˣ) ∧
                 C = (C ⊓ graphLocalGroup Γ a) ⊔ (C ⊓ graphLocalGroup Γ beta) ∧
                 Disjoint (C ⊓ graphLocalGroup Γ a) (C ⊓ graphLocalGroup Γ beta) ∧
                 ⁅C ⊓ graphLocalGroup Γ a,C ⊓ graphLocalGroup Γ beta⁆ = ⊥ ∧
                 (1 < n → Disjoint (C ⊓ graphLocalGroup Γ a) (ballKernel Γ a 1) ∧
                   Disjoint (C ⊓ graphLocalGroup Γ beta) (ballKernel Γ beta 1)) ∧
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
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let hB := Reduction.reduced_borel_core_sylow h
  let hS := Reduction.reduced_vertex_sylow h
  have hsecond := core_intersection_eq_second_kernel ht hB hS hab hbx hNQ hNN
  have hneighbors (z : Vertex Γ) (hz : (graph Γ).Adj beta z) :=
    core_intersection_le_neighbor_core ht hB hS hab hbx hNQ hNN hz
  let p : BasedWalk (graph Γ) 3 a := ⟨⟨beta,hab⟩,⟨⟨x,hbx⟩,⟨⟨a',hxa'⟩,PUnit.unit⟩⟩⟩
  have hgeo : (graph Γ).dist a a' = 3 := hc.1.trans hb3
  have hp : p.Nonbacktracking := nonbacktracking_of_geodesic p hgeo
  have htrans := adjacent_linear_short_path_transitive ht hB hS hob hab eα eβ a 3 (by omega)
  obtain ⟨C,hCp,hCS,hCE,hCo,hCa,ea,eb,hCprod⟩ :=
    reduced_linear_path_cartan h p hp htrans hab
      (by exact List.Mem.head _)
      (by exact List.Mem.tail _ (List.Mem.head _)) eα eβ
  have hCa' : C ≤ stabilizer Γ a := fun c hc => hCp hc a (by exact List.Mem.head _)
  have hCb : C ≤ stabilizer Γ beta := fun c hc => hCp hc beta (by exact List.Mem.tail _ (List.Mem.head _))
  have hCx : C ≤ stabilizer Γ x := fun c hc => hCp hc x (by exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hCap : C ≤ stabilizer Γ a' := fun c hc => hCp hc a' (by exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hω := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  have hZba : Z Γ beta ≤ Z Γ a := by
    rw [←hcQ]
    exact le_normalizer_iff_commutator_le_right.mp
      ((neighbor_core_le_localGroup ht hB hS hab).trans (sylowGenerated_le _) |>.trans
        (CommutingNontrivial.stabilizer_normalizes_Z Γ a))
  have hZb : Z Γ beta ≠ ⊥ := by
    intro he
    obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base Γ beta
    rw [←hg,Z_translate,map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at he
    exact base_Z_ne_bot ht _ he
  obtain ⟨ρ,T,hact,hfaith,hnatural,E,hE⟩ := hnat
  have hdis := odd_local_tori_disjoint ht hZba hZb hω eα ρ hact E hE C hCo
  have hcom : ⁅C ⊓ graphLocalGroup Γ a,C ⊓ graphLocalGroup Γ beta⁆ = ⊥ := by
    let := hCa
    exact commutator_eq_bot_iff_le_centralizer.mpr
      ((show C ⊓ graphLocalGroup Γ a ≤ C from inf_le_left).trans
        (C.le_centralizer.trans (centralizer_le inf_le_left)))
  refine ⟨hb3,F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
    K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,
    ⟨ρ,T,hact,hfaith,hnatural,E,hE⟩,
    x,hbx,hxa',hR,hspan,hcard,hcentral,hN,hNQ,hVN,hNN,hD,hresN,hsec,
    hsecond,hneighbors,C,le_inf (le_inf (le_inf hCa' hCb) hCx) hCap,
    hCS,hCE,hCo,hCa,ea,eb,hCprod,hdis,hcom,?_,?_⟩
  · intro hn'
    have hlarge : 4 ≤ Nat.card F := by
      rw [hF]; exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
    exact ⟨nonbinary_odd_torus_disjoint_kernel ht hB hS hab eα (heq.symm ▸ hlarge) C hCo,
      nonbinary_odd_torus_disjoint_kernel ht hB hS hab.symm eβ hlarge C hCo⟩
  · intro hn'
    apply odd_core_centralizer_radius_transport ht
    intro T hTH ho hne
    exact ((core_section_odd_centralizer eβ hsec hn' hF T hTH ho hne).le.trans inf_le_left).trans
      (hsecond.le.trans inf_le_right)


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

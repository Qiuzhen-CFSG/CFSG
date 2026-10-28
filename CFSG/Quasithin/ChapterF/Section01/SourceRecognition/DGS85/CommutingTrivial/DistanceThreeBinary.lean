module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeCommutator
public import Theory.GroupTheory.PResidual.CenterlessCore
public import Theory.GroupTheory.PResidual.TwiceOddPrime
public import Theory.SpecificGroups.SL2.FieldCardinality

/-!
# The binary middle-field subcase of DGS 9.8

The preceding distance-three reduction gives N = [V_beta,V_alpha-prime] Z_x
inside Q_x, centralizing Q_x, with [N,L_x] <= Z_x. If the actual middle
field has two elements, L_x/Q_x has order six and its two-residual has
order three. The residual-generation lemma for a centerless core centralizer
therefore yields N <= [N,L_x] <= Z_x. Centerlessness follows from the
neighboring intrinsic omega-center; no representation splitting is assumed.

The original F1.11 application uses the recognized alpha and beta fields,
their proved equality, both natural actions and the literal critical-path
conjugations. It discharges the geometric commutator premise of the prior
whole-span reduction in this binary subcase, proving V_beta = Z_alpha Z_x,
the exact cube order and the original centralizer. This does not assert
that the fields are binary: the nonbinary distance-three torus argument
and the terminal distance and field conclusions remain with Chapter 9.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
9.8, printed p.145. The final field-two conclusion is 9.10, pp.147--150.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A central middle module with displacement in Z_x is exactly Z_x
when the literal middle field has two elements. -/
theorem binary_middle_module_eq_center
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {x w : Vertex (family P)} (hxw : (graph (family P)).Adj x w)
    (hω : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,F))
    (hF : Nat.card F = 2)
    (N : Subgroup G) (hZN : Z (family P) x ≤ N) (hNQ : N ≤ Q (family P) x)
    (hLN : graphLocalGroup (family P) x ≤ normalizer (N : Set G))
    (hNL : ⁅N,graphLocalGroup (family P) x⁆ ≤ Z (family P) x)
    (hNC : N ≤ centralizer (Q (family P) x : Set G)) : N = Z (family P) x := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ x
  let A := N.subgroupOf H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hNH : N ≤ H := hNQ.trans (core_le_graphLocalGroup h x)
  let : A.Normal := normal_subgroupOf_of_le_normalizer hLN
  have hcore : (pCore 2 H).map H.subtype = Q Γ x := graphLocalGroup_core h x
  have hAQ : A ≤ pCore 2 H := by
    intro a ha
    have hm : (a : G) ∈ (pCore 2 H).map H.subtype := hcore.symm ▸ hNQ ha
    obtain ⟨b,hb,he⟩ := hm
    exact (H.subtype_injective he) ▸ hb
  have hAC : A ≤ centralizer (pCore 2 H : Set H) := by
    intro a ha b hb
    apply Subtype.ext
    exact hNC ha b (hcore ▸ mem_map_of_mem H.subtype hb)
  let : IsMulCommutative A := le_centralizer_iff_isMulCommutative.mp (hAC.trans (centralizer_le hAQ))
  have horder : Nat.card (H ⧸ pCore 2 H) = 2*3 := by
    rw [Nat.card_congr e.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
    norm_num
  have hodd : Odd (Nat.card (pResidual 2 (H ⧸ pCore 2 H))) := by
    rw [card_twoResidual_of_card_twice_odd_prime (by decide : Odd 3) horder]
    decide
  have he := core_central_subgroup_eq_residual_commutator A hAQ hAC
    (intrinsic_local_center_eq_bot_of_neighbor_central h hB hS hxw hω) hodd
  have hm := congrArg (Subgroup.map H.subtype) he
  rw [map_commutator,map_subgroupOf_eq_of_le hNH] at hm
  exact le_antisymm (hm.le.trans ((commutator_mono le_rfl (map_subtype_le _)).trans hNL)) hZN

universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The binary-field subcase of DGS 9.8 at b=3, with the actual marked
fields and natural actions. The remaining alternative is the nonbinary
field, not an assumed commutator containment. -/
theorem reduced_critical_distance_three_binary_span
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
            (¬ V Γ a' 1 ≤ Q Γ beta) ∧
            ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ = ⊥ ∧
            (Q Γ beta).relIndex (V Γ a' 1) = Nat.card F ∧
            CriticalPathOrbit Γ a' ∧
            ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅Q Γ beta,V Γ beta 1⁆ = Z Γ beta ∧
            Nat.card (Z Γ a) = Nat.card F ^ 2 ∧ Nat.card (Z Γ beta) = Nat.card F ∧
            (∃ x : Vertex Γ, (graph Γ).Adj beta x ∧ (graph Γ).dist x a' + 2 = b Γ ∧
              ∃ g : graphLocalGroup Γ beta, (g : Reduction.G₀ L S₀) • x = a ∧
                let R := ⁅V Γ beta 1,V Γ a' 1⁆
                V Γ beta 1 = R ⊔ R.map (MulAut.conj (g : Reduction.G₀ L S₀)).toMonoidHom ⊔ Z Γ x ∧
                (Nat.card F = 2 → R ≤ Z Γ x ∧ V Γ beta 1 = Z Γ a ⊔ Z Γ x ∧
                  Nat.card (V Γ beta 1) = Nat.card F ^ 3 ∧
                  V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) = Z Γ x)) ∧
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
  have hb : 1 < b (Reduction.reducedFamily L S₀) := by omega
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,he,hrev,hi',hpath,hcQ,hcV,hca,hcb,
      ⟨x,hbx,hdx,k,hk,hspan,hwhole⟩,hnat⟩ :=
    reduced_critical_commutator_span h hc hab hd hb hcomm htriv h8 hob Mα Mβ Mα' Mαsource
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
  have hdist : (graph Γ).dist beta a' = 2 := by change (graph Γ).dist beta a' + 1 = b Γ at hd; change b Γ = 3 at hb3; omega
  have hxa' : (graph Γ).Adj x a' := SimpleGraph.dist_eq_one_iff_adj.mp (by
    change (graph Γ).dist x a' + 2 = b Γ at hdx
    change b Γ = 3 at hb3
    omega)
  have htypes : beta.type = a'.type := (even_dist_iff Γ ht.generate beta a').mp ⟨1,hdist⟩
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
  obtain ⟨_,hNQ,hLnN,hNL,hNC⟩ :=
    distance_three_commutator_middle_reduction ht hB hS hob hbx hxa' hdist hb3
      (f'.symm.trans eβ) (fx.symm.trans eα) hi hcV hcV' hω hω'
  refine ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
    K,instK,finK,charK,m,hm,hK,eα,heq,he,hrev,hi',hpath,hcQ,hcV,hca,hcb,
    ⟨x,hbx,hdx,k,hk,hspan,?_⟩,hnat⟩
  intro htwo
  have hN := binary_middle_module_eq_center ht hB hS hxa' hω' (fx.symm.trans eα)
    (heq.trans htwo) _ le_sup_right hNQ hLnN hNL hNC
  have hR : ⁅V Γ beta 1,V Γ a' 1⁆ ≤ Z Γ x := hN ▸ le_sup_left
  exact ⟨hR,hwhole hR⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

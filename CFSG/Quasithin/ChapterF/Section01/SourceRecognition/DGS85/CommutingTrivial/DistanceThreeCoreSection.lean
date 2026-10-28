module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeCoreNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeReduction
public import Theory.Representation.BinaryConjugationSection.Canonical

/-!
# The core quotient on the distance-three critical path

For the actual reduced F1.11 graph, this constructs the centralizer
`N = Q_alpha ∩ Q_(alpha+2) = C_(Q_beta)(V_beta)`, proves that the beta
residual acts trivially modulo `V_beta`, and gives the elementary quotient
`Q_beta / N` of order `q^2` with its literal conjugation coordinates. The two
previously constructed natural sections and both local quotient markings are
retained. In the nonbinary branch the whole new core quotient is also
recognized as the natural module, with the same quotient coordinates.

The proof combines the core-intersection calculation with the unrestricted
critical-distance reduction, transporting the actual markings along common
edge conjugators. Source: DGS, *Groups and Graphs* (1985), §9.10, printed
page 147, the definition of `N` and assertions (1a)--(1b) in the nonbinary branch.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

variable {G : Type*} [Group G]

private theorem centralizer_map_equiv (e : MulAut G) (A : Subgroup G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- The actual elementary core quotient, with original quotient coordinates
and naturality whenever the defining field has degree greater than one. -/
def CoreQuotientSection (Γ : Bool → Subgroup G) (a beta x : Vertex Γ)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F)) : Prop :=
  let N := Q Γ a ⊓ Q Γ x
  ∃ hN : (N.subgroupOf (Q Γ beta)).Normal,
    letI := hN
    Nat.card (Q Γ beta ⧸ N.subgroupOf (Q Γ beta)) = Nat.card F ^ 2 ∧
    ∃ hE : IsElementaryAbelian 2 (Q Γ beta ⧸ N.subgroupOf (Q Γ beta)),
      letI := hE
      ∃ (σ : Representation (ZMod 2) SL(2,F) (Additive (Q Γ beta ⧸ N.subgroupOf (Q Γ beta))))
        (d : BinaryConjugationSection (graphLocalGroup Γ beta) (Q Γ beta) N
          (σ.comp (eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta)))))),
        (∀ s : Q Γ beta, (d.coordinates s).toAdd =
          Additive.ofMul (QuotientGroup.mk' (N.subgroupOf (Q Γ beta)) s)) ∧
        ∀ n : ℕ, 1 < n → Nat.card F = 2^n →
          letI : Algebra (ZMod 2) F := ZMod.algebra F 2
          ∃ E : Additive (Q Γ beta ⧸ N.subgroupOf (Q Γ beta)) ≃ₗ[ZMod 2] (Fin 2 → F),
            ∀ g v, E (σ g v) = Matrix.mulVec g.val (E v)

universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The literal reduced critical path has the centralizer core quotient and
residual bound of §9.10(1a), with its canonical action, nonbinary naturality
from (1b), and both earlier natural sections. Only the genuine earlier-source premises remain explicit. -/
theorem reduced_critical_distance_three_core_section
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
               CoreQuotientSection Γ a beta x F eβ) := by
  obtain ⟨hb3,F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
      x,hbx,hxa',hR,hspan,hcard,hcentral⟩ :=
    reduced_critical_distance_three_sections h hc hab hd hb h8distance hcomm htriv h8 hob
      Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  change b Γ = 3 at hb3
  change (graph Γ).dist beta a' + 1 = b Γ at hd
  have hlocal (s : Reduction.G₀ L S₀) (v : Vertex Γ) :
      graphLocalGroup Γ (s • v) = (graphLocalGroup Γ v).map (MulAut.conj s).toMonoidHom :=
    graphLocalGroup_conjugate ht s v
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite (Q Γ beta) := Finite.of_injective
    (inclusion (Q_le_stabilizer Γ beta)) (inclusion_injective _)
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hca : graphLocalGroup Γ a ⊓ centralizer (Z Γ a : Set (Reduction.G₀ L S₀)) = Q Γ a := by
    obtain ⟨ρ,T,hact,hfaith,_⟩ := hnat
    exact faithful_center_local_centralizer ht a eα ρ hact hfaith
  obtain ⟨g,hg,hgx⟩ := graphLocalGroup_transitive ht hB hS beta ⟨a,hab.symm⟩ ⟨x,hbx⟩
  change g • a = x at hgx
  obtain ⟨_,fx,_,_,_⟩ := local_quotient_parameter_transport ht g hgx
  have hcx : graphLocalGroup Γ x ⊓ centralizer (Z Γ x : Set (Reduction.G₀ L S₀)) = Q Γ x := by
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hca
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,centralizer_map_equiv,
      ←hlocal,←Z_translate,←Q_translate,hgx] at hh
    exact hh
  obtain ⟨hN,hNQ,hNN⟩ := middle_core_intersection_centralizer ht hB hS hab hbx hspan hca hcx
  have hax : a ≠ x := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_eq_one_iff_adj.mpr hxa',hb3] at hh
    omega
  obtain ⟨hNorm,hElem,horder⟩ := middle_core_quotient_elementary_order ht hB hS hob hab hbx hax
    eβ eα (fx.symm.trans eα)
  let : ((Q Γ a ⊓ Q Γ x).subgroupOf (Q Γ beta)).Normal := hNorm
  let : IsElementaryAbelian 2 (Q Γ beta ⧸ (Q Γ a ⊓ Q Γ x).subgroupOf (Q Γ beta)) := hElem
  have hdist : (graph Γ).dist beta a' = 2 := by omega
  have htypes : beta.type = a'.type := (even_dist_iff Γ ht.generate beta a').mp ⟨1,hdist⟩
  obtain ⟨t,htb,hta⟩ := same_type_edge_transport Γ hab hxa' htypes
  obtain ⟨_,f',_,_,_⟩ := local_quotient_parameter_transport ht t htb
  have hgeom := Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm
  have hω' : Z Γ a' = omegaCenterIn (graphLocalGroup Γ a') := by
    have hω : Z Γ beta = omegaCenterIn (graphLocalGroup Γ beta) := hgeom.2.2.1
    rw [←htb,Z_translate,hlocal,
      ←NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj t).injective,hω]
  have hcV' : ⁅Q Γ a',V Γ a' 1⁆ = Z Γ a' := by
    have hh := congrArg (Subgroup.map (MulAut.conj t).toMonoidHom) hcV
    rwa [map_commutator,←Q_translate,←V_translate,←Z_translate,htb] at hh
  have he := linear_critical_reciprocal_escape ht hB hS hc hab hd
    (by omega : 2 < b Γ) hgeom.1 eα eβ
  obtain ⟨_,hi',_⟩ := reduced_large_neighbor_linear_indices h hc hab hd hb hcomm htriv he h8 hn hF eβ
  obtain ⟨hVN,hD,hresN⟩ := distance_three_core_intersection_residual_bound ht hB hS hab hbx hxa' hb3
    hNN hNQ eβ (f'.symm.trans eβ) hi hi' hcV' hω' hR
  let H := graphLocalGroup Γ beta
  let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hker : q.ker = (Q Γ beta).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ eβ.injective,QuotientGroup.ker_mk']
    have hcore : (pCore 2 H).map H.subtype = Q Γ beta := graphLocalGroup_core ht beta
    rw [←hcore]
    exact (comap_map_eq_self_of_injective H.subtype_injective (pCore 2 H)).symm
  obtain ⟨σ,d,hd⟩ := BinaryConjugationSection.exists_canonical H (Q Γ beta) (Q Γ a ⊓ Q Γ x)
    (core_le_graphLocalGroup ht beta) hNQ
    ((sylowGenerated_le _).trans (stabilizer_normalizes_Q Γ beta))
    ((sylowGenerated_le _).trans hNN) q
    (eβ.surjective.comp (QuotientGroup.mk'_surjective _)) hker
  refine ⟨hb3,F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
    K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,
    x,hbx,hxa',hR,hspan,hcard,hcentral,hN,hNQ,hVN,hNN,hD,hresN,
    hNorm,?_,hElem,σ,d,hd,?_⟩
  · exact horder.trans (congrArg (fun k : ℕ => k ^ 2) heq)
  · intro n hn' hF'
    have hA : V Γ a' 1 ≤ graphLocalGroup Γ beta :=
      (distance_three_neighbor_span_le_core ht hB hS hb3 hxa'.symm).trans
        (neighbor_core_le_localGroup ht hB hS hbx)
    have hp : IsPGroup 2 (V Γ a' 1) := (isPGroup_pCoreIn 2 _).to_le
      (distance_three_neighbor_span_le_core ht hB hS hb3 hxa'.symm)
    have hiD : (Q Γ beta ⊓ Q Γ x).relIndex (Q Γ beta) = Nat.card F := by
      rw [inf_relIndex_left]
      exact (linear_adjacent_core_index ht hB hS hbx.symm
        (core_escape_of_intersection_obstruction Γ (hob beta x hbx))
        (fx.symm.trans eα)).trans heq
    have hcD : ⁅V Γ a' 1,Q Γ beta ⊓ Q Γ x⁆ ≤ Q Γ a ⊓ Q Γ x := by
      rw [commutator_comm]
      exact hD.trans ((CommutingNontrivial.Z_neighbor_le_V Γ hbx).trans hVN)
    exact middle_core_section_natural ht hB hS hbx (hob beta x hbx) eβ σ d hn' hF'
      (horder.trans (congrArg (fun k : ℕ => k ^ 2) heq)) (V Γ a' 1) hp hA hi' hiD hcD

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

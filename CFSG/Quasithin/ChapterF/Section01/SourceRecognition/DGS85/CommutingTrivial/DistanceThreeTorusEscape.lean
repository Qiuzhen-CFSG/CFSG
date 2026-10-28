module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeTorus
public import Theory.GroupTheory.Commutator.IrreducibleCentralizer
public import Theory.Representation.SL2.NaturalConjugation

/-!
# Nonbinary torus displacement at the middle vertex

If the path torus D commuted with L_x modulo Q_x, the three-subgroup lemma
would make its fixed subgroup in Z_x invariant under L_x. The neighboring
central omega Z_beta is nonzero and fixed by D; natural irreducibility
therefore makes D centralize Z_x. A second application of the same lemma,
and centerlessness of L_x, makes D centralize R Z_x. This contradicts the
proved torus fixed kernel and the nonzero natural image of Z_x.

The original F1.11 application constructs D on the same critical path and
retains both actual markings, their equal field orders, both natural
sections, and the middle-module reduction. This proves the first exclusion
in the nonbinary b=3 part of 9.8. The ensuing Sylow product and residual
fixed-subgroup argument, 5.17 splitting, and 9.10--9.11 remain separate
mathematical obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
9.8, printed pp.145--146.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A torus acting nontrivially on the neighboring natural section cannot
commute modulo the middle core with the middle local actor. -/
theorem middle_torus_escapes_core
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {beta x : Vertex (family P)} (hbx : (graph (family P)).Adj beta x)
    (hω : Z (family P) beta = omegaCenterIn (graphLocalGroup (family P) beta))
    (hZne : Z (family P) beta ≠ ⊥)
    (hirr : ∀ A : Subgroup G, A ≤ Z (family P) x →
      graphLocalGroup (family P) x ≤ normalizer (A : Set G) →
        A = ⊥ ∨ A = Z (family P) x)
    (N D : Subgroup G) (hZN : Z (family P) x ≤ N)
    (hNQ : N ≤ Q (family P) x)
    (hNL : ⁅N,graphLocalGroup (family P) x⁆ ≤ Z (family P) x)
    (hNC : N ≤ centralizer (Q (family P) x : Set G))
    (hDb : D ≤ graphLocalGroup (family P) beta)
    (hDN : D ≤ normalizer (N : Set G))
    (hfixed : V (family P) beta 1 ⊓ centralizer (D : Set G) =
      V (family P) beta 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup (family P) beta)).map
        (graphLocalGroup (family P) beta).subtype : Set G))
    (hindex : 1 < (centralizer ((pResidual 2 (graphLocalGroup (family P) beta)).map
      (graphLocalGroup (family P) beta).subtype : Set G)).relIndex (Z (family P) x)) :
    ¬ ⁅D,graphLocalGroup (family P) x⁆ ≤ Q (family P) x := by
  let Γ := family P
  let : ∀ i, Finite (Γ i) := finite_endpoints h
  intro hsmall
  have hseed : Z Γ beta ≤ Z Γ x ⊓ centralizer (D : Set G) := by
    apply le_inf
    · exact hω ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hbx
    · intro z hz
      exact centralizer_le hDb ((mem_omegaCenterIn_iff _ _).mp (hω ▸ hz)).2.1
  have hnz : Z Γ x ⊓ centralizer (D : Set G) ≠ ⊥ := by
    intro he
    exact hZne (bot_unique (he ▸ hseed))
  have hNfix := centralizes_layer_of_fixed_irreducible
    (graphLocalGroup Γ x) N (Z Γ x) D
    (hNQ.trans (core_le_graphLocalGroup h x)) hZN hDN
    ((sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ x))
    hNL (hsmall.trans (le_centralizer_iff.mp hNC))
    (intrinsic_local_center_eq_bot_of_neighbor_central h hB hS hbx.symm hω) hirr hnz
  have hZfix : Z Γ x ≤ centralizer ((pResidual 2 (graphLocalGroup Γ beta)).map
      (graphLocalGroup Γ beta).subtype : Set G) := by
    intro z hz
    exact (hfixed ▸ (show z ∈ V Γ beta 1 ⊓ centralizer (D : Set G) from
      ⟨CommutingNontrivial.Z_neighbor_le_V Γ hbx hz,hNfix (hZN hz)⟩)).2
  exact (ne_of_gt hindex) (relIndex_eq_one.mpr hZfix)

open Representation.NormalElementaryQuotient
universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- In the original distance-three configuration, the constructed nonbinary
path torus has a commutator with the middle local actor escaping its core.
Both original natural sections and the middle reduction are retained. -/
theorem reduced_critical_distance_three_torus_escape
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
              (Q Γ x = V Γ beta 1 ⊔ (Q Γ x ⊓ Q Γ a')) ∧
              (let N := ⁅V Γ beta 1,V Γ a' 1⁆ ⊔ Z Γ x
               N ≤ Q Γ x ∧ graphLocalGroup Γ x ≤ normalizer (N : Set (Reduction.G₀ L S₀)) ∧
                 ⁅N,graphLocalGroup Γ x⁆ ≤ Z Γ x ∧
                 N ≤ centralizer (Q Γ x : Set (Reduction.G₀ L S₀))) ∧
              ∃ k : graphLocalGroup Γ beta,
                (k : Reduction.G₀ L S₀) • x = a ∧
                V Γ beta 1 = ⁅V Γ beta 1,V Γ a' 1⁆ ⊔
                  (⁅V Γ beta 1,V Γ a' 1⁆ : Subgroup (Reduction.G₀ L S₀)).map
                    (MulAut.conj (k : Reduction.G₀ L S₀)).toMonoidHom ⊔ Z Γ x ∧
                (⁅V Γ beta 1,V Γ a' 1⁆ ≤ Z Γ x →
                  V Γ beta 1 = Z Γ a ⊔ Z Γ x ∧ Nat.card (V Γ beta 1) = Nat.card F ^ 3 ∧
                  V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) = Z Γ x) ∧
              ∃ D : Subgroup (Reduction.G₀ L S₀),
                D ≤ graphLocalGroup Γ beta ⊓ stabilizer Γ x ⊓ stabilizer Γ a' ∧
                Nonempty (D ≃* Fˣ) ∧ Nat.card D = Nat.card F-1 ∧ Odd (Nat.card D) ∧
                D ≤ (pResidual 2 (graphLocalGroup Γ beta)).map (graphLocalGroup Γ beta).subtype ∧
                D ≤ normalizer ((⁅V Γ beta 1,V Γ a' 1⁆ : Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)) ∧
                D ≤ normalizer (Z Γ x : Set (Reduction.G₀ L S₀)) ∧
                (2 < Nat.card F → D ≠ ⊥ ∧
                  V Γ beta 1 ⊓ centralizer (D : Set (Reduction.G₀ L S₀)) =
                    V Γ beta 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup Γ beta)).map
                      (graphLocalGroup Γ beta).subtype : Set (Reduction.G₀ L S₀)) ∧
                  ¬ ⁅D,graphLocalGroup Γ x⁆ ≤ Q Γ x) := by
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
  have hdist : (graph (Reduction.reducedFamily L S₀)).dist beta a' = 2 := by omega
  have hxa' : (graph Γ).Adj x a' := SimpleGraph.dist_eq_one_iff_adj.mp (by
    change (graph Γ).dist x a' + 2 = b Γ at hdx
    change b Γ = 3 at hb3
    omega)
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
  obtain ⟨D,hD,eD,hcard,hodd,hDR,hDnR,hDnZ,hDne⟩ :=
    distance_three_torus ht hB hS hob hbx hxa' hdist hn hF eβ (fx.symm.trans eα)
  refine ⟨F,instF,finF,charF,n,hn,hF,eβ,hi,hC,hC',hres,
    K,instK,finK,charK,m,hm,hK,eα,heq,hcQ,hcV,hnat,x,hbx,hxa',hprod,
    ⟨hNQ,hLnN,hNL,hNC⟩,k,hk,hspan,hwhole,D,hD,eD,hcard,hodd,hDR,hDnR,hDnZ,?_⟩
  intro hlarge
  refine ⟨hDne hlarge,?_⟩
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,σ,T,hσ,hfaith,hnatβ,E,hE⟩ := hres
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hcomp : σ.comp q = fixedQuotientAction A (pResidual 2 H) := MonoidHom.ext hσ
  obtain ⟨_,_,⟨c⟩,_⟩ := reduced_critical_residual_section h hc hab hd hb hcomm
  have hkq : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ eβ.injective,QuotientGroup.ker_mk']
  have hfix := BinaryConjugationSection.natural_odd_fixed_eq_kernel H (V Γ beta 1) _ q
    (hkq ▸ pCore_isPGroup) σ (hcomp.symm ▸ c) E hE D
    (hD.trans (inf_le_left.trans inf_le_left)) hodd (hDne hlarge)
    (inf_le_right.trans (centralizer_le hDR))

  refine ⟨hfix,?_⟩
  have hnonzero : Z Γ beta ≠ ⊥ := by
    intro hz
    rw [hz,card_bot] at hcb
    omega
  have hidx : 1 < (centralizer ((pResidual 2 H).map H.subtype : Set (Reduction.G₀ L S₀))).relIndex (Z Γ x) := by
    obtain ⟨_,_,_,hidx,_⟩ := residual_neighbor_fixed_line ht hB hS hbx
      (core_escape_of_intersection_obstruction Γ (hob x beta hbx.symm)) hω eβ σ
      (hcomp.symm ▸ c) hfaith T hn hF hnatβ
    have hi : (centralizer ((pResidual 2 H).map H.subtype : Set (Reduction.G₀ L S₀))).relIndex (Z Γ x) = Nat.card F := hidx
    rw [hi]
    omega
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨ρ,Tα,hρ,hfaithα,hnatα,Eα,hEα⟩ := hnat
  have hirr : ∀ A : Subgroup (Reduction.G₀ L S₀), A ≤ Z Γ x →
      graphLocalGroup Γ x ≤ normalizer (A : Set (Reduction.G₀ L S₀)) →
        A = ⊥ ∨ A = Z Γ x := by
    intro A hAZ hLA
    let f := (MulAut.conj (k : Reduction.G₀ L S₀)).toMonoidHom
    have hZZ : (Z Γ x).map f = Z Γ a := by
      rw [←Z_translate,hk]
    have hLL : (graphLocalGroup Γ x).map f = graphLocalGroup Γ a := by
      have hh := graphLocalGroup_conjugate ht (k : Reduction.G₀ L S₀) x
      change graphLocalGroup Γ ((k : Reduction.G₀ L S₀) • x) =
        (graphLocalGroup Γ x).map f at hh
      exact hh.symm.trans (congrArg (graphLocalGroup Γ) hk)
    have hAZ' : A.map f ≤ Z Γ a := hZZ ▸ map_mono hAZ
    have hLA' : graphLocalGroup Γ a ≤ normalizer (A.map f : Set (Reduction.G₀ L S₀)) :=
      hLL ▸ (map_mono hLA).trans (A.le_normalizer_map f)
    rcases natural_conjugation_minimal (graphLocalGroup Γ a) (Z Γ a)
      (eα.toMonoidHom.comp (QuotientGroup.mk' _))
      (eα.surjective.comp (QuotientGroup.mk'_surjective _)) ρ hρ Eα hEα
      (A.map f) hAZ' hLA' with hzero | hfull
    · left
      exact map_injective (MulAut.conj (k : Reduction.G₀ L S₀)).injective
        (hzero.trans (map_bot f).symm)
    · right
      exact map_injective (MulAut.conj (k : Reduction.G₀ L S₀)).injective
        (hfull.trans hZZ.symm)
  exact middle_torus_escapes_core ht hB hS hbx hω hnonzero hirr
    (⁅V Γ beta 1,V Γ a' 1⁆ ⊔ Z Γ x) D le_sup_right hNQ hNL hNC
    (hD.trans (inf_le_left.trans inf_le_left))
    ((le_inf hDnR hDnZ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
    hfix hidx

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

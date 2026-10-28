module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.Graph
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.Dihedral
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.OrbitAction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.VertexExtension
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order

/-!
# The concrete target of J₂ graph recognition

The target uses the actual ATLAS carrier, its conjugate-subgroup orbit, and
the literal A₄-join adjacency. The marked dihedral ten lies in the pointwise
edge fixer, and its full centralizer contains a checked edge reversal.
The order-three seed centralizes the existing first-parabolic involution;
that centralizer has odd index 315, as required for the source 3A marking.

The conditional constructor below is retained as a small interface for
alternative certificate producers. The checked orbit and local-A₅ modules
also discharge all five inputs on the actual carrier, so `system` below is
the unconditional target system. The marked vertex extension and all local
equivalences remain attached to the literal subgroups used by that system.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3, 47.5 and 47.10,
pp.261–267. No comparison with an icosian carrier and no order-based
recognition is used.
-/

public section
namespace CFSG.Quasithin.Janko23.J2Recognition.ConcreteSystem
open Subgroup Theory.GroupTheory.GraphUniquenessSystem
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.RecognitionGeometry
open scoped Pointwise

/-- The chosen seed is in the actual distinguished involution centralizer. -/
theorem X_le_firstCentralizer : X ≤ ExceptionalParabolics.Seed.l₁ := by
  apply zpowers_le.mpr
  apply mem_centralizer_singleton_iff.mpr
  exact ((Commute.refl (GeneratorPair.a * GeneratorPair.b * GeneratorPair.a *
    GeneratorPair.b⁻¹)).pow_pow 4 6).eq

/-- The marked involution centralizer has odd index in the actual carrier. -/
theorem firstCentralizer_index : ExceptionalParabolics.Seed.l₁.index = 315 :=
  GeneratorPair.FirstFusion.centralizer_index

/-- The chosen orbit is exactly the source's conjugates of order-three subgroups
of the distinguished involution centralizer, not an unrelated family label. -/
theorem source_vertex_iff (A : Subgroup Carrier) :
    A ∈ MulAction.orbit (ConjAct Carrier) X ↔
      ∃ U : Subgroup Carrier, Nat.card U = 3 ∧ U ≤ ExceptionalParabolics.Seed.l₁ ∧
        ∃ g : Carrier, ConjAct.toConjAct g • U = A := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨X, card_X, X_le_firstCentralizer, ConjAct.ofConjAct g, hg⟩
  · rintro ⟨U, hU, hUH, g, rfl⟩
    apply MulAction.mem_orbit_of_mem_orbit
    let H := ExceptionalParabolics.Seed.l₁
    have hc (V : Subgroup Carrier) (hV : Nat.card V = 3) (hVH : V ≤ H) :
        Nat.card (V.subgroupOf H) = 3 ^ (Nat.card H).factorization 3 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv, hV,
        ExceptionalParabolics.FirstParabolic.card_l₁]
      decide +kernel
    let P : Sylow 3 H := Sylow.ofCard (X.subgroupOf H) (hc X card_X X_le_firstCentralizer)
    let Q : Sylow 3 H := Sylow.ofCard (U.subgroupOf H) (hc U hU hUH)
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H P Q
    have he := congrArg (fun S : Sylow 3 H => (S : Subgroup H)) hh
    change MulAut.conj h • X.subgroupOf H = U.subgroupOf H at he
    rw [conj_smul_subgroupOf X_le_firstCentralizer h] at he
    have hm := congrArg (fun V : Subgroup H => V.map H.subtype) he
    rw [map_subgroupOf_eq_of_le (conj_smul_le_of_le X_le_firstCentralizer h),
      map_subgroupOf_eq_of_le hUH] at hm
    exact ⟨ConjAct.toConjAct (h : Carrier), hm⟩

/-- Condition (U), parametrized by the five concrete calculations. -/
def ofCalculations
    (faithful : ∀ g : Carrier, (∀ A : Vertex, g • A = A) → g = 1)
    (neighbors : ∀ A : Vertex, graph.Adj base A →
      ∃ m : M, (m : Carrier) • neighbor = A)
    (generate : K ⊔ M = ⊤)
    (vertex_generate : E ⊔ (K ⊓ M) = M)
    (local_generate : (K ⊓ edgeStabilizer Carrier base neighbor) ⊔ (K ⊓ M) = K) :
    System Carrier Vertex where
  graph := graph
  H := K
  x := base
  y := neighbor
  adjacent := adjacent
  preserves := preserves
  faithful := faithful
  vertex_transitive := transitive
  edge_transitive A B hAB := by
    obtain ⟨g, hg⟩ := transitive A
    have hnear := preserves g⁻¹ hAB
    have hx : g⁻¹ • A = base := by rw [← hg, inv_smul_smul]
    rw [hx] at hnear
    obtain ⟨m, hm⟩ := neighbors _ hnear
    have hmx : (m : Carrier) • base = base := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [base_stabilizer]
      exact m.property
    refine ⟨g * m, Or.inl ⟨?_, ?_⟩⟩
    · rw [mul_smul, hmx, hg]
    · rw [mul_smul, hm, smul_inv_smul]
  local_orbit := ⟨⟨t, t_mem_K⟩, t_smul_base⟩
  generate := by rw [base_stabilizer]; exact generate
  vertex_generate := by rw [base_stabilizer, edgeFixer_eq]; exact vertex_generate
  local_generate := by rw [base_stabilizer]; exact local_generate

/-! ### The checked target system and its marked local structure -/

open Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
open Sporadic.LeechRelated.J2.RecognitionGeometry.OrbitAction
open Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension

/-- The normalizer order supplied by the exhaustive concrete orbit. -/
theorem card_M : Nat.card M = 2160 := OrbitAction.card_M

/-- The actual uniqueness system on the ATLAS degree-100 carrier. -/
noncomputable def system : System Carrier Vertex :=
  ofCalculations OrbitAction.faithful OrbitAction.neighbors K_sup_M
    (E_sup_K_inf_M card_M) local_generate

@[simp] theorem system_graph : system.graph = graph := by rfl

@[simp] theorem system_local : system.H = K := by rfl

@[simp] theorem system_base : system.x = base := by rfl

@[simp] theorem system_neighbor : system.y = neighbor := by rfl

/-- Adjacency in the completed system is the literal A₄-join condition. -/
theorem system_adj_iff (A B : Vertex) :
    system.graph.Adj A B ↔ Nonempty (↥(A.val ⊔ B.val) ≃* alternatingGroup (Fin 4)) := by
  rw [system_graph]
  exact graph_adj_iff A B

/-- The system vertex stabilizer is the chosen full normalizer. -/
@[simp] theorem system_vertexGroup : system.vertexGroup = M := by
  change MulAction.stabilizer Carrier system.x = M
  rw [system_base, base_stabilizer]

/-- The system edge fixer is the literal intersection of endpoint normalizers. -/
@[simp] theorem system_edgeGroup : system.edgeGroup = E := by
  change edgeFixer Carrier system.x system.y = E
  rw [system_base, system_neighbor, edgeFixer_eq]

/-- The local setwise edge overlap is generated by the fixed reversing involution. -/
theorem system_local_edge : system.H ⊓ system.edgeSetGroup = zpowers t := by
  change system.H ⊓ edgeStabilizer Carrier system.x system.y = zpowers t
  rw [system_local, system_base, system_neighbor, K_inf_edgeStabilizer_eq_zpowers]

/-- The fixed reversal used in the source equivalence condition, with the
left-conjugation identity on the actual system edge fixer. -/
theorem system_reversal :
    t ∈ system.H ∧ t ^ 2 = 1 ∧ t • system.x = system.y ∧ t • system.y = system.x ∧
      ∀ b : system.edgeGroup, t * (b : Carrier) * t⁻¹ = b := by
  refine ⟨?_, t_square, ?_, ?_, ?_⟩
  · rw [system_local]; exact t_mem_K
  · rw [system_base, system_neighbor]; exact t_smul_base
  · rw [system_base, system_neighbor]; exact t_smul_neighbor
  · intro b
    apply t_conj_of_mem_E
    simpa only [system_edgeGroup] using b.property

/-
The following theorem is the comparison payload used by the source-side
similarity assembly. Every component is a map or equality for the literal
subgroups `C`, `M`, `E`, `K`, `K ⊓ M` and the fixed reversal `t`; no group
family label or order-only surrogate occurs in the contract.
-/
theorem marked_local_structure :
    Nat.card M = 2160 ∧
      Nonempty (E ≃* alternatingGroup (Fin 5)) ∧
      Nonempty (K ≃* alternatingGroup (Fin 5)) ∧
      Nonempty (↥(K ⊓ M) ≃* Equiv.Perm (Fin 3)) ∧
      Theory.GroupTheory.IsQuasisimple C ∧
      center C = XC ∧
      (center C).map C.subtype = X ∧
      CM.IsComplement' S ∧ Nat.card S = 2 ∧
      ∃ eC : CentralQuotient ≃* alternatingGroup (Fin 6),
        ∃ eM : VertexQuotient ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F,
          (∀ q, eM (quotientInclusion q) =
            Matrix.ProjectiveSpecialLinearGroup.toPGL
              (Atlas.Comparisons.Exceptional.psl2NineCoordinatesEquivAlt6.symm (eC q))) ∧
          (∀ c : C, eM (vertexQuotientMap splitterM) *
              Matrix.ProjectiveSpecialLinearGroup.toPGL
                (Atlas.Comparisons.Exceptional.psl2NineCoordinatesEquivAlt6.symm
                  (eC (centralQuotientMap c))) *
              (eM (vertexQuotientMap splitterM))⁻¹ =
            Matrix.ProjectiveSpecialLinearGroup.toPGL
              (Atlas.Comparisons.Exceptional.psl2NineCoordinatesEquivAlt6.symm
                (eC (centralQuotientMap (splitterAction c))))) ∧
      (∀ p : alternatingGroup (Fin 5),
        t * (edgeIntoM p : Carrier) * t⁻¹ = (edgeIntoM p : Carrier)) := by
  rcases marked_vertex_extension card_M with ⟨hC, hcenter, hmap, hsplit, hS, eC, eM, hq, hc⟩
  exact ⟨card_M, ⟨LocalA5.edgeEquiv⟩, ⟨LocalA5.localEquiv⟩, ⟨LocalA5.vertexEquiv⟩,
    hC, hcenter, hmap, hsplit, hS, eC, eM, hq, hc, t_conj_edge_model⟩

end CFSG.Quasithin.Janko23.J2Recognition.ConcreteSystem

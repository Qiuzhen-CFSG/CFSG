module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceMarkings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.BOneProfileSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalProfileCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoLinearModule
public import Theory.SpecificGroups.SL2.FieldCardinality

/-!
# Parameters of a noncommuting mixed A₅/S₃ critical pair

The literal quotient maps identify the natural-action field at a quintic
vertex with the field of order four, and at a cubic vertex with the binary
field. The paired distance-one actions have equal field orders, excluding
that branch. At distance two the middle field is a positive power of the
starting field. Thus the starting vertex is cubic and its middle vertex is
quintic. These are the parameters needed by the exceptional core-order
calculation and the remaining strict mixed branch.

Source: DGS, *Groups and Graphs* (1985), 10.5 and 10.7, pp.156,158--159.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.MixedDGS
open CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
variable {G : Type*} [Group G] {K U S : Subgroup G}
local notation "F" => Reduction.reducedFamily ![K,U] S

/-- A natural action with the literal graph core as kernel has the field
order of the marked quotient at that vertex. -/
theorem source_action_field_card (h : HypothesisF11 ![K,U] S)
    {v : Vertex F} {A : Subgroup (Reduction.G₀ ![K,U] S)}
    (hA : A = graphLocalGroup F v)
    {k k' : Type*} [Field k] [Finite k] [CharP k 2]
    [Field k'] [Finite k'] [CharP k' 2]
    (q : A →* SL(2,k)) (hq : Function.Surjective q)
    (hker : q.ker = (Q F v).subgroupOf A)
    (e : (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,k')) :
    Nat.card k = Nat.card k' := by
  have hcore : A.pCoreIn 2 = Q F v := by
    rw [hA]
    exact CommutingTrivial.graphLocalGroup_core (Reduction.reduced_triple h) v
  have hk : q.ker = pCore 2 A := by
    rw [hker,←hcore]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  let ea := MulEquiv.subgroupCongr hA
  let eq := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let ef := (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans (eq.trans e))
  exact Matrix.SL2.field_card_eq_of_equiv ef

/-- Equal paired natural fields exclude the noncommuting distance-one
branch of the actual mixed pair. -/
theorem noncommuting_distance_one_false (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {v w : Vertex F} (hc : IsCriticalPair F v w)
    (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) (hb : b F = 1) : False := by
  obtain ⟨_,_,k₀,f₀,n₀,ch₀,a₀,k₁,f₁,n₁,ch₁,a₁,c₀,c₁,ha₀,ha₁,hfields,_⟩ :=
    Noncommuting.Reduction.original_bOne_natural_cores_of_actor_models h
      (graph_models h eK eU) hc hne hb
  let := f₀
  let := n₀
  let := ch₀
  let := f₁
  let := n₁
  let := ch₁
  have hfour := source_action_field_card h ha₀ c₀.quotient c₀.onto c₀.kernel
    (graph_linear_four h eK (base F false) rfl).some
  have htwo := source_action_field_card h ha₁ c₁.quotient c₁.onto c₁.kernel
    (graph_linear_two h eU (base F true) rfl).some
  rw [hfour,htwo] at hfields
  norm_num [GaloisField.card 2 2 (by decide),Nat.card_zmod] at hfields

/-- The actual distance-two critical pair starts at the cubic vertex type;
the field-power relation rules out the reverse orientation. -/
theorem noncommuting_two_cubic_orientation (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {v m w : Vertex F} (hc : IsCriticalPair F v w)
    (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) (hb : b F = 2)
    (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    v.type = true ∧ m.type = false := by
  have ht := Reduction.reduced_triple h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hcentral := Reduction.reduced_bTwo_middle_central h hc hne hb hvm hmw
  have hcomm := (Reduction.reduced_bTwo_center_identities h hc hne hb hvm hmw).2.2.2
  obtain ⟨k,f,n,ch,a,c,hactor⟩ :=
    Reduction.reduced_bTwo_center_action_exists h hc hne hb hvm hmw
  let := f
  let := n
  let := ch
  have hv : v.type = true := by
    by_contra hv
    have hv' : v.type = false := Bool.eq_false_iff.mpr hv
    have hm : m.type = true := by
      have hh := hvm.1
      rw [hv'] at hh
      cases he : m.type <;> simp_all
    have hk := source_action_field_card h hactor c.quotient c.onto c.kernel
      (graph_linear_four h eK v hv').some
    have hval : 3 ≤ Nat.card ((graph F).neighborSet v) := by
      rw [card_neighbors_of_indices F
        (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
      exact source_valence_ge_three ht (Reduction.reduced_vertex_sylow h) v.type
    obtain ⟨t,htm,htne⟩ := Set.exists_ne_of_one_lt_ncard
      (s := (graph F).neighborSet v) (by rw [←Nat.card_coe_set_eq]; omega) m
    obtain ⟨r,hr,hpow⟩ := c.linear_core_field_power ht
      (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
      hb hactor hcentral htm htne hcomm.le
      (Reduction.reduced_graph_core_obstruction h v m hvm)
      (graph_linear_two h eU m hm).some
    rw [hk,GaloisField.card 2 2 (by decide),Nat.card_zmod] at hpow
    have hh : 4 ≤ 4^r := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 4) (show 1 ≤ r by omega)
    norm_num at hpow
    omega
  refine ⟨hv,?_⟩
  have hh := hvm.1
  rw [hv] at hh
  cases he : m.type <;> simp_all

end CFSG.Quasithin.ChapterF.Source.MixedDGS

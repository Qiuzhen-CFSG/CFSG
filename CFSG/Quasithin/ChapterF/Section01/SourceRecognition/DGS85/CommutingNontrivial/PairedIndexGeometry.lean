module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryComparison

/-!
# The original paired indices in DGS 8.3

Distinct neighbors give distinct edge Sylows. An elementary subgroup in
both edge cores therefore lies in the vertex core. Applied at beta this
identifies the denominator in the printed b₂, and hence the exact product
a₂ b₂. Binary rank at the moving vertex bounds both b₁ and b₂, transporting
through the original graph action rather than identifying model carriers.

Source: DGS, Groups and Graphs (1985), 8.3(2), pp.135--136. The remaining
residual-action square estimates are separate mathematical obligations.
-/

@[expose] public noncomputable section
open Subgroup Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- An elementary subgroup common to distinct marked edge cores lies in
O₂ of their common vertex. This uses the actual local Sylows. -/
theorem source_elementary_distinct_edges_le_core (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w z : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hvz : (graph (family P)).Adj v z) (hwz : w ≠ z)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAw : A ≤ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (hAz : A ≤ (stabilizer (family P) v ⊓ stabilizer (family P) z).pCoreIn 2) :
    A ≤ Q (family P) v := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hvw
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hvz
  have hAR : A ≤ (R : Subgroup L).map L.subtype := hR.symm ▸ hAw
  have hAT : A ≤ (T : Subgroup L).map L.subtype := hT.symm ▸ hAz
  have hAL : A ≤ L := hAR.trans (map_subtype_le _)
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  by_contra hn
  have hn' : ¬ A.subgroupOf L ≤ pCore 2 L := by
    intro he
    apply hn
    rw [←localGroup_core_eq (family P) d v]
    intro x hx
    exact ⟨⟨x,hAL hx⟩,he hx,rfl⟩
  have he := local_sylow_eq_of_elementary_escape M R T (A.subgroupOf L)
    (by intro x hx; obtain ⟨y,hy,he⟩ := hAR hx; exact (Subtype.ext he : y=x) ▸ hy)
    (by intro x hx; obtain ⟨y,hy,he⟩ := hAT hx; exact (Subtype.ext he : y=x) ▸ hy) hn'
  apply hwz
  exact source_edge_sylow_unique_neighbor h d hvz hvw M T hT (by
    rw [←he,hR]
    exact (pCoreIn_le 2 _).trans inf_le_right)

/-- The original b₂ denominator is contained in its numerator, before any
module recognition: V_alpha' ∩ Q_alpha ≤ Q_beta. -/
theorem source_reverse_core_intersection (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (M : IsRankOneModel (d.localGroup beta ⧸ pCore 2 (d.localGroup beta))) :
    V (family P) a' 1 ⊓ Q (family P) a ≤ Q (family P) beta := by
  let := finite_endpoints h
  let F := family P
  have hb3 : 3 ≤ b F := (source_critical_geometry h d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V F a' 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) a'
  let : IsElementaryAbelian 2 ↥(V F a' 1 ⊓ Q F a : Subgroup G) := IsElementaryAbelian.of_le inf_le_left
  have hne : a' ≠ beta := by
    intro he
    have hd' := hd
    rw [←he,SimpleGraph.dist_self] at hd'
    omega
  obtain ⟨next,hn,hnD⟩ := exists_predecessor F h.generate a' beta hne
  have hd' : (graph F).dist a' beta + 1 = b F := by
    rw [SimpleGraph.dist_comm]
    exact hd
  have hVA : V F a' 1 ≤ Q F next := V_le_Q_of_dist_add_lt_b F h.generate
    (fun v => (source_Z_Q_U h v).1) a' next 1 (by omega) (d.kernel_sylow next)
  have hna : next ≠ a := by
    intro he
    rw [he,SimpleGraph.dist_comm (u := a') (v := a),hc.1] at hnD
    change b F + 1 = (graph F).dist a' beta at hnD
    omega
  apply source_elementary_distinct_edges_le_core h hB d hn hab.symm hna M
  · exact inf_le_left.trans (hVA.trans (by
      simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hn.symm))
  · exact inf_le_right.trans (by
      simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab)

private theorem index_product (U Q K : Subgroup G) (h : U ⊓ Q ≤ K) :
    K.relIndex U * Q.relIndex (U ⊓ K) = Q.relIndex U := by
  rw [Nat.mul_comm,inf_comm U K,relIndex_inf_mul_relIndex]
  rw [←inf_relIndex_right (Q ⊓ K) U,←inf_relIndex_right Q U]
  congr 1
  ext x
  exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨⟨hx.1,h ⟨hx.2,hx.1⟩⟩,hx.2⟩⟩

private theorem elementary_index_of_rank (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup v)
    (n : ℕ) (hr : primeRank 2 (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≤ n) :
    (Q (family P) v).relIndex A ≤ 2^n := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 L)
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hi := Representation.BinaryConjugationSection.actor_image_card_eq_relIndex L
    (Q (family P) v) A q (local_quotient_kernel (family P) d v (MulEquiv.refl _)) hAL
  exact hi ▸ (primeRank_le_iff_elementary_card_le _).mp hr _ inferInstance

private theorem elementary_index_at_same_type (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) {v w : Vertex (family P)}
    (ht : v.type = w.type) (n : ℕ)
    (hr : primeRank 2 (d.localGroup w ⧸ pCore 2 (d.localGroup w)) ≤ n)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup v) :
    (Q (family P) v).relIndex A ≤ 2^n := by
  let := finite_endpoints h
  obtain ⟨g,rfl⟩ := (same_orbit_iff (family P) v w).mpr ht
  let e := MulAut.conj g
  let E := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hEL : E ≤ d.localGroup (g • v) := by rw [d.conjugate]; exact map_mono hAL
  have hh := elementary_index_of_rank h d (g • v) E hEL n hr
  rw [Q_translate,relIndex_map_map_of_injective _ _ e.injective] at hh
  exact hh

/-- Both literal products and both secondary-index bounds in 8.3(2).
The same n bounds the quotient rank at the moving vertex; the reverse
bound is transported to alpha by the actual graph action. -/
theorem source_paired_core_indices (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (n : ℕ) (hr : primeRank 2 (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≤ n) :
    let F := family P
    (Q F a').relIndex (V F beta 1) * (Q F w.val).relIndex (V F beta 1 ⊓ Q F a') =
      (Q F w.val).relIndex (V F beta 1) ∧
    (Q F beta).relIndex (V F a' 1) * (Q F a).relIndex (V F a' 1 ⊓ Q F beta) =
      (Q F a).relIndex (V F a' 1) ∧
    (Q F w.val).relIndex (V F beta 1 ⊓ Q F a') ≤ 2^n ∧
    (Q F a).relIndex (V F a' 1 ⊓ Q F beta) ≤ 2^n := by
  let := finite_endpoints h
  let F := family P
  have hb3 : 3 ≤ b F := (source_critical_geometry h d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V F beta 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) beta
  let : IsElementaryAbelian 2 (V F a' 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) a'
  let : IsElementaryAbelian 2 ↥(V F beta 1 ⊓ Q F a' : Subgroup G) := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 ↥(V F a' 1 ⊓ Q F beta : Subgroup G) := IsElementaryAbelian.of_le inf_le_left
  refine ⟨index_product _ _ _ (source_moving_core_intersection h hB d hc hab hd hb hcomm w hm (models a')),
    index_product _ _ _ (source_reverse_core_intersection h hB d hc hab hd hb hcomm (models beta)),
    elementary_index_of_rank h d w.val _ (source_moving_actor h d hc hab hd hb hcomm w hm).2.1 n hr,?_⟩
  have heven : Even ((graph F).dist beta a') := by
    obtain ⟨k,hk⟩ := (source_critical_geometry h d hc hab hd hb hcomm).1
    refine ⟨k,?_⟩
    change (graph (family P)).dist beta a' = k+k
    omega
  have hbt := (even_dist_iff F h.generate beta a').mp heven
  have ht : a.type = w.val.type := by
    have ha := hab.1
    have hw := w.property.1
    cases hat : a.type <;> cases hwt : w.val.type <;>
      cases hbt' : beta.type <;> cases het : a'.type <;> simp_all
  apply elementary_index_at_same_type h d ht n hr
  apply pGroup_le_localGroup F d a _ (IsElementaryAbelian.isPGroup 2 _)
  exact inf_le_right.trans ((source_Z_Q_U h beta).2.trans
    ((ballKernel_one_le_edge F hab.symm).trans inf_le_right))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

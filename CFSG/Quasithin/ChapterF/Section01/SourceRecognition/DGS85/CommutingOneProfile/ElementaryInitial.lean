module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CoreProductIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedElementaryProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PathBorelDihedral

/-!
# Eliminating the dihedral beta candidate without an alpha marking

At a dihedral beta endpoint, fourth powers of edge actors fix the whole
star. The edge two-core is Sylow, so fourth powers cover its odd quotient.
This gives the three-vertex supplement used in the source pair-core span,
without assigning a doubly transitive action to D₁₀. The beta Sylow is
elementary, so the independent core-product index bound is one. These two
core identities select a linear alpha quotient, and the proved arbitrary
linear-alpha dihedral exclusion finishes the contradiction.

The reduced elementary branch therefore selects a linear beta quotient
without an alpha marking or a chosen path. Both local quotient catalogues
are retained. Source: DGS, Groups and Graphs (1985), (11.3)(h)--(11.7),
pp.170--175; the dihedral edge action is the literal D₁₀ action.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Fourth powers supply the exact three-vertex supplement at a dihedral
beta vertex. No two-edge transitivity is needed or asserted. -/
theorem source_dihedral_beta_seed_supplement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 ⊔
      ((stabilizer (family P) a ⊓ stabilizer (family P) b) ⊓ stabilizer (family P) c) =
        stabilizer (family P) a ⊓ stabilizer (family P) b := by
  let := finite_endpoints h
  let E := stabilizer (family P) a ⊓ stabilizer (family P) b
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer (family P) a from inf_le_left))
    (inclusion_injective _)
  let R := pCore 2 E
  let q := QuotientGroup.mk' R
  obtain ⟨T,hT⟩ := source_edge_core_sylow h hB hab
  have ho : Odd (Nat.card (E ⧸ R)) := by
    change Odd R.index
    rw [show R = (T : Subgroup E) from hT.symm]
    exact Nat.not_even_iff_odd.mp (fun he => T.not_dvd_index he.two_dvd)
  have hcop : (Nat.card (E ⧸ R)).Coprime 4 := by
    simpa using ho.coprime_two_right.pow_right 2
  apply le_antisymm (sup_le (pCoreIn_le 2 _) inf_le_left)
  intro x hx
  obtain ⟨u,hu⟩ := hcop.pow_left_bijective.surjective (q ⟨x,hx⟩)
  change u^4 = q ⟨x,hx⟩ at hu
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective R u
  have hdiff : (⟨x,hx⟩ : E) * (y^4)⁻¹ ∈ R := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (⟨x,hx⟩ * (y^4)⁻¹) = 1
    rw [map_mul,map_inv,map_pow,hu,mul_inv_cancel]
  have h4 : (y:G)^4 ∈ E ⊓ stabilizer (family P) c :=
    ⟨E.pow_mem y.property 4, source_dihedral_edge_fourth_fixes_neighbors h hB d hab.symm hbc eb
      y ⟨y.property.2,y.property.1⟩⟩
  have hh := (E.pCoreIn 2 ⊔ (E ⊓ stabilizer (family P) c)).mul_mem
    (mem_sup_left (mem_map_of_mem E.subtype hdiff)) (mem_sup_right h4)
  change (x * ((y:G)^4)⁻¹) * (y:G)^4 ∈ E.pCoreIn 2 ⊔ (E ⊓ stabilizer (family P) c) at hh
  simpa only [inv_mul_cancel_right] using hh

/-- The elementary beta Sylow makes the actual adjacent-core product the
whole edge two-core, without a path or an alpha marking. -/
theorem source_dihedral_beta_core_product
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b := by
  let := finite_endpoints h
  have hab := source_critical_one_adjacent hc hb
  let L := d.localGroup b
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
  let q := QuotientGroup.mk' (pCore 2 L)
  let U := T.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let := dihedral_model_sylow_elementary eb U
  have hω : omegaCenterIn (U : Subgroup (L ⧸ pCore 2 L)) = U := by
    apply le_antisymm (map_subtype_le _)
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨hx,
      fun y hy => congrArg Subtype.val (mul_comm (⟨y,hy⟩ : U) (⟨x,hx⟩ : U)),
      elemPow_eq_one_of_isElementaryAbelian x hx⟩
  have hi := source_core_product_index_le_beta_omega h hB d hc hb (.dihedral ⟨eb⟩) T hT
  change (Q (family P) a ⊔ Q (family P) b).relIndex
    ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ≤
      (omegaCenterIn (U : Subgroup (L ⧸ pCore 2 L))).relIndex U at hi
  rw [hω,relIndex_self] at hi
  let E := stabilizer (family P) a ⊓ stabilizer (family P) b
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer (family P) a from inf_le_left))
    (inclusion_injective _)
  let : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E)) (inclusion_injective _)
  have hpos := ((Q (family P) a ⊔ Q (family P) b).subgroupOf
    ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).index_ne_zero_of_finite
  have heq : (Q (family P) a ⊔ Q (family P) b).relIndex
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) = 1 := by
    change (Q (family P) a ⊔ Q (family P) b).relIndex
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ≠ 0 at hpos
    omega
  apply le_antisymm (relIndex_eq_one.mp heq)
  exact sup_le (Noncommuting.graph_Q_le_edgeCore h hab)
    (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm)

section Reduced
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀

/-- All dihedral beta quotients are excluded from the commuting critical
edge. The alpha marking is derived from the actual source core identities. -/
theorem reduced_dihedral_beta_exclusion
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) : False := by
  have ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  let := finite_endpoints ht
  have hv := card_neighbors_of_indices F₀
    (fun i => ((F₀ (!i)).subgroupOf (F₀ i)).index) (fun _ => rfl) b
  have hcard : 1 < ((graph F₀).neighborSet b).ncard := by
    rw [←Nat.card_coe_set_eq,hv]
    have hh : 3 ≤ ((F₀ (!b.type)).subgroupOf (F₀ b.type)).index :=
      source_valence_ge_three ht (Reduction.reduced_vertex_sylow h) b.type
    omega
  obtain ⟨c,hbc,hca⟩ := Set.exists_ne_of_one_lt_ncard hcard a
  have hab := source_critical_one_adjacent hc hb
  have hcover := source_dihedral_beta_seed_supplement ht hB d hab hbc eb
  have hcore := source_rankOne_pair_core_span_of_supplement ht hB d hc hb hbc hca.symm
    Ma (.dihedral ⟨eb⟩) hcover
  have hprod := source_dihedral_beta_core_product ht hB d hc hb eb
  obtain ⟨n,hn,ha⟩ := source_alpha_linear_of_core_identities ht hB d hc hb hcomm
    hbc hca.symm Ma (.dihedral ⟨eb⟩) hprod hcore
  exact reduced_linear_dihedral_exclusion h d hc hb hcomm n (by omega) ha eb

/-- The literal elementary S/Q_beta branch selects beta as linear, without
preselecting alpha. The dihedral alternative is discharged internally. -/
theorem reduced_elementary_beta_selection
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (helem : ∃ hN : ((Q F₀ b).subgroupOf
        ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) ⧸
        (Q F₀ b).subgroupOf ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2))) :
    ∃ m, 0 < m ∧ ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2^m) := by
  rcases source_linear_or_dihedral_of_elementary_edge (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d (source_critical_one_adjacent hc hb).symm Mb
    (by
      change ∃ hN : ((Q F₀ b).subgroupOf
        ((stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2)).Normal,
        letI := hN
        IsElementaryAbelian 2 (((stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2) ⧸
          (Q F₀ b).subgroupOf ((stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2))
      rw [inf_comm (stabilizer F₀ b) (stabilizer F₀ a)]
      exact helem) with hm | eb
  · exact hm
  · exact (reduced_dihedral_beta_exclusion h d hc hb hcomm Ma eb.some).elim

end Reduced
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

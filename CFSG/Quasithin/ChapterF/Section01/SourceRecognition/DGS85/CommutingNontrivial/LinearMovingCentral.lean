module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalLinear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction

/-!
# Moving elementary Sylow rows make the critical commutator central

For a moving neighbor λ with local quotient SL₂ in characteristic two, the
quotient Sylow omega-center is the entire Sylow. Original 8.1(h) therefore
makes H centralize the common edge Sylow. The residual-fixed conclusion of
8.1(i), obtained from the original adjacent-core obstruction, makes H
centralize O²(L_alpha'). These two subgroups generate L_alpha', so H lies
in its elementary center Z_alpha'.

The retained D₁₀ row has Sylow order two and gives the same argument.
This supplies 8.6(a) directly in both rows, including the binary linear
parameter. It requires neither a marking at beta nor the natural
residual exclusion in 8.5. Source: DGS, *Groups and Graphs* (1985), 8.1 and
8.6--8.7, printed pp.132--140.
-/

@[expose] public noncomputable section
open Subgroup Representation BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem linear_quotient_omega_preimage {D : Type*} [Group D]
    (M : Subgroup D) [Finite M] {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (M ⧸ pCore 2 M) ≃* SL(2,K)) (T : Sylow 2 M) :
    quotientSylowOmegaPreimage M T = (T : Subgroup M).map M.subtype := by
  let q := QuotientGroup.mk' (pCore 2 M)
  let R := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 M))
  let S := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hω : omegaCenterIn (R : Subgroup (M ⧸ pCore 2 M)) = R := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [NilesRankOneKernel.omegaCenterIn_map_injective _ e.injective]
    change omegaCenterIn (S : Subgroup SL(2,K)) = S
    rw [omegaCenterIn_eq_omegaOneAmbient,Representation.RankOne.QuadraticRecognition.sl2_omega_center_eq]
  unfold quotientSylowOmegaPreimage
  change ((omegaCenterIn (R : Subgroup (M ⧸ pCore 2 M))).comap q).map M.subtype = _
  rw [hω]
  change (((T : Subgroup M).map q).comap q).map M.subtype = _
  rw [comap_map_eq_self]
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup.le_sylow_of_normal T

private theorem dihedral_quotient_omega_preimage {D : Type*} [Group D]
    (M : Subgroup D) [Finite M]
    (e : (M ⧸ pCore 2 M) ≃* DihedralGroup 5) (T : Sylow 2 M) :
    quotientSylowOmegaPreimage M T = (T : Subgroup M).map M.subtype := by
  let q := QuotientGroup.mk' (pCore 2 M)
  let R := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 M))
  have hc : Nat.card (M ⧸ pCore 2 M) = 10 := by
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  have hR : Nat.card R = 2 := by
    rw [R.card_eq_multiplicity,hc]
    decide +kernel
  let : IsCyclic R := isCyclic_of_prime_card hR
  have hω : omegaCenterIn (R : Subgroup (M ⧸ pCore 2 M)) = R := by
    apply le_antisymm (map_subtype_le _)
    intro r hr
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hr,?_,?_⟩
    · intro s hs
      exact congrArg Subtype.val (mul_comm' (⟨s,hs⟩ : (R : Subgroup _)) ⟨r,hr⟩)
    · have he := pow_card_eq_one' (x := (⟨r,hr⟩ : (R : Subgroup (M ⧸ pCore 2 M))))
      rw [hR] at he
      exact congrArg Subtype.val he
  unfold quotientSylowOmegaPreimage
  change ((omegaCenterIn (R : Subgroup (M ⧸ pCore 2 M))).comap q).map M.subtype = _
  rw [hω]
  change (((T : Subgroup M).map q).comap q).map M.subtype = _
  rw [comap_map_eq_self]
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup.le_sylow_of_normal T

private theorem moving_commutator_central_of_full_omega
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily L S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      Z (Reduction.reducedFamily L S₀) w.val⁆ ≠ ⊥)
    (hfull : ∀ R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val),
      quotientSylowOmegaPreimage (graphLocalGroup (Reduction.reducedFamily L S₀) w.val) R =
        (R : Subgroup (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)).map
          (graphLocalGroup (Reduction.reducedFamily L S₀) w.val).subtype) :
    let Γ := Reduction.reducedFamily L S₀
    ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≤ Z Γ a' := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let H := ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆
  let M := d.localGroup a'
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite M := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  let : Finite (d.localGroup w.val) := Finite.of_injective
    (inclusion (d.local_le w.val)) (inclusion_injective _)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d w.property.symm
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d w.property
  have hΩ := (source_critical_quotient_omega_action ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hm R hR).1
  change H ≤ Z Γ w.val ⊓ centralizer (quotientSylowOmegaPreimage (d.localGroup w.val) R : Set (Reduction.G₀ L S₀)) at hΩ
  have hY := hfull R
  change quotientSylowOmegaPreimage (d.localGroup w.val) R =
    (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype at hY
  have hHT : H ≤ centralizer (((T : Subgroup M).map M.subtype) : Set (Reduction.G₀ L S₀)) := by
    rw [hY,hR] at hΩ
    rw [hT,inf_comm]
    exact hΩ.trans inf_le_right
  have hescape : ¬ Q Γ w.val ≤ Q Γ a' := core_escape_of_intersection_obstruction Γ
    (Reduction.reduced_graph_core_obstruction h w.val a' w.property.symm)
  have hres := (source_critical_displacement_residual_fixed ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hescape).trans inf_le_right
  have hM : (pResidual 2 M).map M.subtype ⊔ (T : Subgroup M).map M.subtype = M := by
    rw [←Subgroup.map_sup,pResidual_sup_sylow_eq_top]
    exact (MonoidHom.range_eq_map M.subtype).symm.trans M.range_subtype
  have hHC : H ≤ centralizer (M : Set (Reduction.G₀ L S₀)) := by
    apply le_centralizer_iff.mp
    rw [←hM]
    exact sup_le (le_centralizer_iff.mp hres) (le_centralizer_iff.mp hHT)
  have hHZ := hΩ.trans inf_le_left
  have hself : (graph Γ).dist a' a' + 1 ≤ b Γ := by
    simpa only [SimpleGraph.dist_self,zero_add] using hb.le
  have hHL : H ≤ M := (source_critical_displacement_residual_fixed ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models w hescape).trans
    (inf_le_left.trans (neighbor_le_graphLocalGroup ht (Reduction.reduced_kernel_sylow h) a' a' hb
      hself))
  have hz := critical_end_center_of_commuting Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (fun v => (source_Z_Q_U ht v).2) hc hcomm M (d.sylow_or_center a')
  change H ≤ Z Γ a'
  rw [hz]
  let : IsElementaryAbelian 2 (Z Γ w.val) := CommutingOneProfile.source_center_elementary ht w.val
  intro x hx
  exact (mem_omegaCenterIn_iff M x).mpr ⟨hHL hx,hHC hx,
    elemPow_eq_one_of_isElementaryAbelian x (hHZ hx)⟩

/-- A moving SL₂ neighbor forces the literal critical commutator into the
original terminal center. -/
theorem reduced_linear_moving_commutator_central
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily L S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      Z (Reduction.reducedFamily L S₀) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)) ≃* SL(2,K)) :
    let Γ := Reduction.reducedFamily L S₀
    ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≤ Z Γ a' := by
  apply moving_commutator_central_of_full_omega h models hc hab hd hb hcomm w hm
  let ht := Reduction.reduced_triple h
  let : ∀ i, Finite (Reduction.reducedFamily L S₀ i) := finite_endpoints ht
  let : Finite (graphLocalGroup (Reduction.reducedFamily L S₀) w.val) := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  exact fun R => linear_quotient_omega_preimage _ e R

/-- The same centrality conclusion holds for the retained D₁₀ moving row. -/
theorem reduced_dihedral_moving_commutator_central
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily L S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      Z (Reduction.reducedFamily L S₀) w.val⁆ ≠ ⊥)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)) ≃* DihedralGroup 5) :
    let Γ := Reduction.reducedFamily L S₀
    ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≤ Z Γ a' := by
  apply moving_commutator_central_of_full_omega h models hc hab hd hb hcomm w hm
  let ht := Reduction.reduced_triple h
  let : ∀ i, Finite (Reduction.reducedFamily L S₀ i) := finite_endpoints ht
  let : Finite (graphLocalGroup (Reduction.reducedFamily L S₀) w.val) := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  exact fun R => dihedral_quotient_omega_preimage _ e R

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

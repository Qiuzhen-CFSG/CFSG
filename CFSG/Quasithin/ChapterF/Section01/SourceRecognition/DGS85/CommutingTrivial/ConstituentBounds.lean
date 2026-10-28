module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ResidualConstituent
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.QuotientFaithfulness

/-!
# Initial rank-one bounds without whole-section descent

Apply the proved model estimates to the constructed irreducible constituent
of the literal residual section. Suzuki, including Sz(2), gives the square
bound in the original core and centralizer indices. The special and projective
unitary groups give the same bound at degrees at least two, allowing scalar
kernels. A supplied linear quotient bounds those indices by its actual field.

No quotient action on the whole residual section or neighboring naturality
is assumed. ConstituentExclusions and ConstituentIndices apply the bounds
to both actual orientations of the source graph.
Source: DGS, *Groups and Graphs* (1985), 9.3, p.142, and 5.12, pp.113--115.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

open BenderSuzuki.MatrixGroups

/-- Suzuki quotients impose the square bound on the original two core
indices, via a constructed constituent. This includes Sz(2) and does not
assume that the whole residual section descends through O₂. -/
theorem reduced_critical_suzuki_constituent_bound (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (m : ℕ)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SuzukiMatrixGroup m) :
    let Γ := Reduction.reducedFamily L S₀
    ((Q Γ beta).relIndex (V Γ a' 1)) ^ 2 ≤
      (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((V Γ a' 1).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_residual_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite d.space.toSubmodule := d.finiteSpace
  let : d.action.IsIrreducible := d.irreducible
  let : Nontrivial d.space.toSubmodule := Subrepresentation.irreducible_module_nontrivial d.action
  have hf := CommutingNontrivial.suzuki_quotient_action_faithful m e d.action d.residualFixed
  obtain ⟨T,hT⟩ := d.elementary.isPGroup.exists_le_sylow
  have hlo := suzuki_all_square_bound m d.action hf T Aq hT d.quadratic
  rw [d.actorCard] at hlo
  exact hlo.trans d.fixedIndex

/-- At a supplied linear quotient, the same constructed constituent gives
the source actor bound without a whole-section descent assumption. -/
theorem reduced_critical_linear_constituent_bound (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    (Q Γ beta).relIndex (V Γ a' 1) ≤
      (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((V Γ a' 1).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_residual_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite d.space.toSubmodule := d.finiteSpace
  let : d.action.IsIrreducible := d.irreducible
  let : Nontrivial d.space.toSubmodule := Subrepresentation.irreducible_module_nontrivial d.action
  have hf := CommutingNontrivial.linear_quotient_action_faithful hn hF e d.action d.residualFixed
  obtain ⟨T,hT⟩ := d.elementary.isPGroup.exists_le_sylow
  have hlo := sl2_actor_bound d.action hf T Aq hT hF
  rw [d.actorCard] at hlo
  exact hlo.trans d.fixedIndex
/-- Every unitary parameter of degree at least two gives the original
square inequality on the constructed irreducible section. Special-unitary
scalar kernels are permitted. -/
theorem reduced_critical_special_unitary_constituent_bound (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* J.specialSubgroup) :
    let Γ := Reduction.reducedFamily L S₀
    ((Q Γ beta).relIndex (V Γ a' 1)) ^ 2 ≤
      (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((V Γ a' 1).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_residual_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite d.space.toSubmodule := d.finiteSpace
  let : d.action.IsIrreducible := d.irreducible
  let : Nontrivial d.space.toSubmodule := Subrepresentation.irreducible_module_nontrivial d.action
  have hx : fixedSpace d.action ⊤ = ⊥ :=
    bot_unique ((fixedSpace_antitone d.action le_top).trans d.residualFixed.le)
  have hnt : ∃ g, d.action g ≠ 1 := by
    by_contra! hh
    obtain ⟨w,hw⟩ := exists_ne (0 : d.space.toSubmodule)
    have hfixed : w ∈ fixedSpace d.action ⊤ := by
      intro g
      change d.action g w = w
      rw [hh]
      rfl
    exact hw (hx.le hfixed)
  let : IsElementaryAbelian 2 Aq := d.elementary
  have hlo := su3_elementary_square_bound J hn hF hconj d.action hnt hx Aq
  rw [d.actorCard] at hlo
  exact hlo.trans d.fixedIndex

/-- Every unitary parameter of degree at least two gives the original
square inequality on the constructed irreducible section. Special-unitary
scalar kernels are permitted. -/
theorem reduced_critical_projective_unitary_constituent_bound (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    let Γ := Reduction.reducedFamily L S₀
    ((Q Γ beta).relIndex (V Γ a' 1)) ^ 2 ≤
      (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((V Γ a' 1).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_residual_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite d.space.toSubmodule := d.finiteSpace
  let : d.action.IsIrreducible := d.irreducible
  let : Nontrivial d.space.toSubmodule := Subrepresentation.irreducible_module_nontrivial d.action
  have hx : fixedSpace d.action ⊤ = ⊥ :=
    bot_unique ((fixedSpace_antitone d.action le_top).trans d.residualFixed.le)
  have hnt : ∃ g, d.action g ≠ 1 := by
    by_contra! hh
    obtain ⟨w,hw⟩ := exists_ne (0 : d.space.toSubmodule)
    have hfixed : w ∈ fixedSpace d.action ⊤ := by
      intro g
      change d.action g w = w
      rw [hh]
      rfl
    exact hw (hx.le hfixed)
  let : IsElementaryAbelian 2 Aq := d.elementary
  have hlo := psu3_elementary_square_bound J hn hF hconj d.action hnt hx Aq
  rw [d.actorCard] at hlo
  exact hlo.trans d.fixedIndex


/-- The constructed linear constituent bounds the original actor index
above and the original centralizer index below by the actual field order. -/
theorem reduced_critical_linear_constituent_field_bounds (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (he : ¬ V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    (Q Γ beta).relIndex (V Γ a' 1) ≤ Nat.card F ∧ Nat.card F ≤
      (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((V Γ a' 1).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_residual_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite d.space.toSubmodule := d.finiteSpace
  let : d.action.IsIrreducible := d.irreducible
  let : Nontrivial d.space.toSubmodule := Subrepresentation.irreducible_module_nontrivial d.action
  have hf := CommutingNontrivial.linear_quotient_action_faithful hn hF e d.action d.residualFixed
  obtain ⟨T,hT⟩ := d.elementary.isPGroup.exists_le_sylow
  have hcard : Nat.card Aq = (Q Γ beta).relIndex (V Γ a' 1) := d.actorCard
  have hne : Aq ≠ ⊥ := by
    intro hbot
    rw [hbot,card_bot] at hcard
    exact he (relIndex_eq_one.mp hcard.symm)
  have hlo := sl2_actor_field_bound d.action hf T Aq hT hne hF
  refine ⟨?_,hlo.trans d.fixedIndex⟩
  change (Q Γ beta).relIndex (V Γ a' 1) ≤ Nat.card F
  rw [←hcard]
  exact (Nat.card_le_card_of_injective _ (inclusion_injective hT)).trans_eq
    (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv)


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FactorModule
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.QuotientFaithfulness
public import Theory.Representation.RankOne.QuadraticRecognition.TwoRankOne

/-!
# The ending-factor inequalities in DGS 8.2

Apply the actual linear, dihedral, Suzuki and unitary estimates to the constructed
irreducible factor of V_alpha'. The image of Z_alpha has order exactly
[Z_alpha : Z_alpha intersect Q_alpha']; the factor's fixed-space index
is bounded above by the centralizer index on the whole original span.
Linear quotients give the actor bound. Suzuki (including Sz(2)), D₁₀ and
unitary field order at least four give its square, allowing scalar kernels.

`FactorComparison` combines these with original core and centralizer
comparisons. All actions and fixed-space generation are constructed on
the literal reduced F1.11 graph in either critical orientation.
This is the suitable-factor step of 8.2, not full reciprocal escape.
Source: DGS, Groups and Graphs (1985), 8.2, printed p.135; corrected 5.12(a).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}
open BenderSuzuki.MatrixGroups

/-- Suzuki quotients impose the square bound on the original two core
indices, via a constructed constituent. This includes Sz(2) and does not
assume that the whole residual section descends through O₂. -/
theorem reduced_ending_suzuki_constituent_bound (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (m : ℕ)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* SuzukiMatrixGroup m) :
    let Γ := Reduction.reducedFamily L S₀
    ((Q Γ a').relIndex (Z Γ a)) ^ 2 ≤
      (centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a'
  let A := (V Γ a' 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((Z Γ a).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ a' H (sylowGenerated_le _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_ending_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2 H
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
theorem reduced_ending_linear_constituent_bound (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    (Q Γ a').relIndex (Z Γ a) ≤
      (centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a'
  let A := (V Γ a' 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((Z Γ a).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ a' H (sylowGenerated_le _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_ending_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2 H
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
theorem reduced_ending_special_unitary_constituent_bound (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* J.specialSubgroup) :
    let Γ := Reduction.reducedFamily L S₀
    ((Q Γ a').relIndex (Z Γ a)) ^ 2 ≤
      (centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a'
  let A := (V Γ a' 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((Z Γ a).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ a' H (sylowGenerated_le _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_ending_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2 H
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
theorem reduced_ending_projective_unitary_constituent_bound (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    let Γ := Reduction.reducedFamily L S₀
    ((Q Γ a').relIndex (Z Γ a)) ^ 2 ≤
      (centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a'
  let A := (V Γ a' 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((Z Γ a).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ a' H (sylowGenerated_le _)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_ending_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2 H
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



private theorem dihedral_two_rank : primeRank 2 (DihedralGroup 5) ≤ 1 := by
  let S : Sylow 2 (DihedralGroup 5) := Sylow.ofCard (zpowers (DihedralGroup.sr 0 : DihedralGroup 5)) (by
    rw [Nat.card_zpowers,DihedralGroup.orderOf_sr,DihedralGroup.nat_card]
    rw [Nat.factorization_mul (by decide) (by decide),
      Nat.prime_two.factorization,Nat.prime_five.factorization]
    norm_num)
  exact S.primeRank_le_one_of_isCyclic
    (inferInstanceAs (IsCyclic (zpowers (DihedralGroup.sr 0 : DihedralGroup 5))))

private theorem dihedral_action_faithful {L W : Type*} [Group L] [Finite L]
    [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]
    (e : (L ⧸ pCore 2 L) ≃* DihedralGroup 5)
    (ρ : Representation (ZMod 2) (DihedralGroup 5) W)
    (hres : fixedSpace ρ (pResidual 2 (DihedralGroup 5)) = ⊥) : Function.Injective ρ := by
  have hnot : ¬ pResidual 2 (DihedralGroup 5) ≤ ρ.ker := by
    intro h
    have he : fixedSpace ρ (pResidual 2 (DihedralGroup 5)) = ⊤ := by
      apply top_unique
      intro v _ g
      change ρ g v = v
      rw [show ρ g = 1 from h g.property]
      rfl
    exact top_ne_bot (he.symm.trans hres)
  apply ρ.ker_eq_bot_iff.mp
  by_cases hd : 5 ∣ Nat.card ρ.ker
  · have hi : ρ.ker.index ∣ 2 := by
      apply Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 5)
      have hm := Nat.mul_dvd_mul_right hd ρ.ker.index
      rw [ρ.ker.card_mul_index,DihedralGroup.nat_card,mul_comm 5 ρ.ker.index] at hm
      exact hm
    have hp : IsPGroup 2 ((DihedralGroup 5) ⧸ ρ.ker) :=
      IsPGroup.of_card_dvd_pow (n := 1) (by simpa only [pow_one,←Subgroup.index_eq_card] using hi)
    exact (hnot ((pResidual_le_iff_isPGroup_quotient 2 ρ.ker).mpr hp)).elim
  · have hc : Nat.card ρ.ker ∣ 2 := by
      apply ((Nat.prime_five.coprime_iff_not_dvd.mpr hd).symm).dvd_of_dvd_mul_right
      simpa only [DihedralGroup.nat_card] using ρ.ker.card_subgroup_dvd_card
    have hp : IsPGroup 2 ρ.ker := IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hc)
    have hk : ρ.ker ≤ pCore 2 (DihedralGroup 5) := le_sSup ⟨inferInstance,hp⟩
    have hcore : pCore 2 (DihedralGroup 5) = ⊥ := by
      rw [←pCore_map_iso 2 e,Subgroup.pCore_quotient_pCore_eq_bot,Subgroup.map_bot]
    exact bot_unique (hk.trans hcore.le)

private theorem dihedral_elementary_fixed_bound {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (DihedralGroup 5) W) (hf : Function.Injective ρ)
    (A : Subgroup (DihedralGroup 5)) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥) :
    4 ≤ Nat.card (W ⧸ fixedSpace ρ A) := by
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hd := involution_fixedCodim_ge_two_of_two_rank_one dihedral_two_rank
    (DihedralGroup.sr 0) (DihedralGroup.sr 1) (DihedralGroup.sr 3)
    (by constructor <;> decide) (by constructor <;> decide) (by constructor <;> decide)
    (by decide) (by decide) (by decide) (by decide)
    ρ hf a ⟨ha1,elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha⟩
  have hlo : 4 ≤ Nat.card (W ⧸ fixedSpace ρ (zpowers a)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hd
  have hle : Nat.card (W ⧸ fixedSpace ρ (zpowers a)) ≤ Nat.card (W ⧸ fixedSpace ρ A) := by
    let : Finite (W ⧸ fixedSpace ρ A) := Finite.of_surjective _ (fixedSpace ρ A).mkQ_surjective
    exact Nat.card_le_card_of_surjective _
      (Submodule.factor_surjective (fixedSpace_antitone ρ (zpowers_le.mpr ha)))
  exact hlo.trans hle


/-- The D₁₀ endpoint gives the original square inequality on the selected
factor, using its actual dihedral action and the binary transvection bound. -/
theorem reduced_ending_dihedral_constituent_bound (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* DihedralGroup 5) :
    let Γ := Reduction.reducedFamily L S₀
    ((Q Γ a').relIndex (Z Γ a)) ^ 2 ≤
      (centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a'
  let A := (V Γ a' 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((Z Γ a).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ a' H (sylowGenerated_le _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_ending_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2 H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite d.space.toSubmodule := d.finiteSpace
  let : d.action.IsIrreducible := d.irreducible
  let : Nontrivial d.space.toSubmodule := Subrepresentation.irreducible_module_nontrivial d.action
  have hf := dihedral_action_faithful e d.action d.residualFixed
  let : IsElementaryAbelian 2 Aq := d.elementary
  have hne : Aq ≠ ⊥ := by
    intro he
    have hcard : Nat.card Aq = (Q Γ a').relIndex (Z Γ a) := d.actorCard
    rw [he,card_bot] at hcard
    exact hc.2 ((relIndex_eq_one.mp hcard.symm).trans (source_Z_Q_U ht a').2)
  have hlo := dihedral_elementary_fixed_bound d.action hf Aq hne
  have htwo : Nat.card Aq ≤ 2 := by
    simpa only [pow_one] using (primeRank_le_iff_elementary_card_le (DihedralGroup 5)).mp
      dihedral_two_rank Aq inferInstance
  have hsq : Nat.card Aq ^ 2 ≤ Nat.card (d.space.toSubmodule ⧸ fixedSpace d.action Aq) := by
    nlinarith
  rw [d.actorCard] at hsq
  exact hsq.trans d.fixedIndex

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

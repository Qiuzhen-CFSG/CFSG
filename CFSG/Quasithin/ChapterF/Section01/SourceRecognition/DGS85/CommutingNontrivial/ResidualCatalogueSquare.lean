module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ResidualConstituent
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.QuotientFaithfulness
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiElementBounds
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryActorElements

/-!
# Nonlinear residual square bounds on the original opposite span

An arbitrary escaping subgroup of the opposite span acts on an irreducible
constituent of the canonical residual quotient. Suzuki involution bounds, or
the unitary element bound in the full opposite quadratic actor, give the field
square lower bound. Restriction and the original coordinate map return it to
the literal centralizer index. No descent of the entire residual is assumed.

Source: DGS, Groups and Graphs (1985), 5.10(b), 8.6--8.7, pp.111--112,139--140.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CommutingTrivial Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The canonical residual constituent for any subgroup of the opposite span. -/
theorem reduced_critical_subactor_constituent (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {D : Type*} [Group D] [Finite D]
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* D)
    (E : Subgroup (Reduction.G₀ L S₀))
    (hEV : E ≤ V (Reduction.reducedFamily L S₀) a' 1) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ beta
    let A := (V Γ beta 1).subgroupOf H
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    let Aq := (E.subgroupOf H).map q
    letI : ∀ i, Finite (Γ i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
    ∃ hb2 : 2 < b Γ,
      letI := neighborhoodIn_elementary Γ (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) beta hb2 H
      Nonempty (ResidualConstituent (fixedQuotientAction A (pResidual 2 H)) q Aq
        ((Q Γ beta).relIndex E)
        ((centralizer (E : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1))) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := (E.subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  dsimp only
  obtain ⟨hb2,hnz,⟨c⟩,hr,hVH,hquad⟩ := reduced_critical_residual_section h hc hab hd hb hcomm
  refine ⟨hb2,?_⟩
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Nontrivial (FixedQuotient A (pResidual 2 H)) := hnz
  have hVL : V Γ beta 1 ≤ H := neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) beta beta hb
    (show (graph Γ).dist beta beta + 1 ≤ b Γ by
      simp only [SimpleGraph.dist_self,zero_add]; exact hb.le)
  let : Finite (V Γ beta 1) := Finite.of_injective (inclusion hVL) (inclusion_injective _)
  let : Finite (FixedQuotient A (pResidual 2 H)) :=
    Finite.of_surjective (fun x : V Γ beta 1 => (c.coordinates x).toAdd)
      (Multiplicative.toAdd.surjective.comp c.onto)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hk' : q.ker = (Q Γ beta).subgroupOf H := by
    have hcore : H.pCoreIn 2 = Q Γ beta := graphLocalGroup_core ht beta
    rw [hk,←hcore]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  let : IsElementaryAbelian 2 (V Γ a' 1) := V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) a' hb2
  have hEq : IsQuadratic (fixedQuotientAction A (pResidual 2 H)) (E.subgroupOf H) := by
    intro x hx y hy z
    exact hquad x (hEV hx) y (hEV hy) z
  exact section_constituent H (Q Γ beta) (V Γ beta 1) _ E
    (fixedQuotientAction A (pResidual 2 H)) c hr q hq (hk.symm ▸ pCore_isPGroup)
    hk' (hEV.trans hVH) (IsElementaryAbelian.of_le hEV) hEq


private theorem constituent_quadratic {H D W : Type*} [Group H] [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (q : H →* D)
    {A₀ : Subgroup D} {i j : ℕ} (d : ResidualConstituent ρ q A₀ i j)
    (A : Subgroup H) (hq : IsQuadratic ρ A) : IsQuadratic d.action (A.map q) := by
  rintro x ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩ z
  rw [d.descent,d.descent]
  apply Subtype.ext
  exact hq x hx y hy z

private theorem residual_action_nontrivial {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] [Nontrivial W] (ρ : Representation (ZMod 2) D W)
    (hr : fixedSpace ρ (pResidual 2 D) = ⊥) : ∃ g, ρ g ≠ 1 := by
  by_contra! hh
  obtain ⟨w,hw⟩ := exists_ne (0 : W)
  apply hw
  apply hr.le
  intro g
  change ρ g w = w
  rw [hh]
  rfl

private theorem residual_element_square (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {D : Type*} [Group D] [Finite D]
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* D)
    (q₀ actorMin : ℕ)
    (hlower : ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Nontrivial W],
      ∀ (ρ : Representation (ZMod 2) D W), fixedSpace ρ (pResidual 2 D) = ⊥ →
      ∀ A : Subgroup D, IsElementaryAbelian 2 A → actorMin ≤ Nat.card A →
      IsQuadratic ρ A → ∀ t : D, t ∈ A → t ≠ 1 →
        q₀^2 ≤ Nat.card (W ⧸ fixedSpace ρ (zpowers t)))
    (hlarge : actorMin ≤ (Q (Reduction.reducedFamily L S₀) beta).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1))
    (E : Subgroup (Reduction.G₀ L S₀))
    (hEV : E ≤ V (Reduction.reducedFamily L S₀) a' 1)
    (hEQ : ¬ E ≤ Q (Reduction.reducedFamily L S₀) beta) :
    q₀^2 ≤ (centralizer (E : Set (Reduction.G₀ L S₀))).relIndex
      (V (Reduction.reducedFamily L S₀) beta 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let U := (V Γ beta 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let A := ((V Γ a' 1).subgroupOf H).map q
  let D₀ := (E.subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_subactor_constituent h hc hab hd hb hcomm e E hEV
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite d.space.toSubmodule := d.finiteSpace
  let : d.action.IsIrreducible := d.irreducible
  let : Nontrivial d.space.toSubmodule := Subrepresentation.irreducible_module_nontrivial d.action
  obtain ⟨_,_,_,_,hVH,hquad⟩ := reduced_critical_residual_section h hc hab hd hb hcomm
  let : IsElementaryAbelian 2 (V Γ a' 1) := V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) a' hb2
  let : IsElementaryAbelian 2 ((V Γ a' 1).subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  have hk : q.ker = (Q Γ beta).subgroupOf H := by
    have hcore : H.pCoreIn 2 = Q Γ beta := graphLocalGroup_core ht beta
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',←hcore]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hcA : Nat.card A = (Q Γ beta).relIndex (V Γ a' 1) :=
    BinaryConjugationSection.actor_image_card_eq_relIndex H (Q Γ beta) (V Γ a' 1) q hk hVH
  have hqA : IsQuadratic d.action A :=
    constituent_quadratic (fixedQuotientAction U (pResidual 2 H)) q d
      ((V Γ a' 1).subgroupOf H) hquad
  have hD : D₀ ≠ ⊥ := by
    intro he
    have hh : Nat.card D₀ = (Q Γ beta).relIndex E := d.actorCard
    rw [he,card_bot] at hh
    exact hEQ (relIndex_eq_one.mp hh.symm)
  obtain ⟨t,htD,ht1⟩ := D₀.bot_or_exists_ne_one.resolve_left hD
  have hDA : D₀ ≤ A := map_mono (subgroupOf_mono H hEV)
  have hlo := hlower d.space.toSubmodule d.action d.residualFixed A inferInstance
    (hcA.symm ▸ hlarge) hqA t (hDA htD) ht1
  have hidx : Nat.card (d.space.toSubmodule ⧸ fixedSpace d.action (zpowers t)) ≤
      Nat.card (d.space.toSubmodule ⧸ fixedSpace d.action D₀) := by
    let : Finite (d.space.toSubmodule ⧸ fixedSpace d.action D₀) :=
      Finite.of_surjective _ (fixedSpace d.action D₀).mkQ_surjective
    exact Nat.card_le_card_of_surjective _
      (Submodule.factor_surjective (fixedSpace_antitone d.action (zpowers_le.mpr htD)))
  exact hlo.trans (hidx.trans d.fixedIndex)

/-- Every escaping subactor has Suzuki field-square displacement on the original span. -/
theorem reduced_critical_suzuki_residual_square (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (m : ℕ)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SuzukiMatrixGroup m)
    (E : Subgroup (Reduction.G₀ L S₀))
    (hEV : E ≤ V (Reduction.reducedFamily L S₀) a' 1)
    (hEQ : ¬ E ≤ Q (Reduction.reducedFamily L S₀) beta) :
    (2^(2*m+1))^2 ≤ (centralizer (E : Set (Reduction.G₀ L S₀))).relIndex
      (V (Reduction.reducedFamily L S₀) beta 1) := by
  let : ∀ i, Finite ((Reduction.reducedFamily L S₀) i) :=
    finite_endpoints (Reduction.reduced_triple h)
  let : Finite (graphLocalGroup (Reduction.reducedFamily L S₀) beta) :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  apply residual_element_square h hc hab hd hb hcomm e (2^(2*m+1)) 0 ?_ (Nat.zero_le _) E hEV hEQ
  intro W _ _ _ _ ρ hr A hA _ _ t ht ht1
  let := hA
  have hf := suzuki_quotient_action_faithful m e ρ hr
  have ht2 : orderOf t = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
  simpa only [←pow_mul,Nat.mul_comm (2*m+1) 2] using suzuki_element_fixed_index m ρ hf t ht2

/-- The full opposite quadratic actor supplies the unitary square bound for every escaping subactor. -/
theorem reduced_critical_unitary_residual_square (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) 3 (2^n) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) 3 (2^n))
    (hlarge : 4 ≤ (Q (Reduction.reducedFamily L S₀) beta).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1))
    (E : Subgroup (Reduction.G₀ L S₀))
    (hEV : E ≤ V (Reduction.reducedFamily L S₀) a' 1)
    (hEQ : ¬ E ≤ Q (Reduction.reducedFamily L S₀) beta) :
    (2^n)^2 ≤ (centralizer (E : Set (Reduction.G₀ L S₀))).relIndex
      (V (Reduction.reducedFamily L S₀) beta 1) := by
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    apply residual_element_square h hc hab hd hb hcomm e (2^n) 4 ?_ hlarge E hEV hEQ
    intro W _ _ _ _ ρ hr A hA hA4 hq t ht ht1
    let := hA
    exact psu3_elementary_element_field_square J hn hK hconj ρ (residual_action_nontrivial ρ hr) A hA4 hq t ht ht1
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    apply residual_element_square h hc hab hd hb hcomm e (2^n) 4 ?_ hlarge E hEV hEQ
    intro W _ _ _ _ ρ hr A hA hA4 hq t ht ht1
    let := hA
    exact su3_elementary_element_field_square J hn hK hconj ρ (residual_action_nontrivial ρ hr) A hA4 hq t ht ht1

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

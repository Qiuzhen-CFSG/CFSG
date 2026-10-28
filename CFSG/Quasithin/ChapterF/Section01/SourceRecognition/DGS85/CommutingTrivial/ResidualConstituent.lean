module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ResidualSource
public import Theory.Representation.NormalPKernelDescent
public import Theory.Representation.RankOne.QuadraticRecognition.FixedGeneratedReduction
public import Theory.Representation.BinaryConjugationSection.FixedQuotientIndex


/-!
# Irreducible constituents of the original residual section

A nonzero irreducible submodule of V_beta/C_V_beta(O²(L_beta)) has zero
O²-fixed space. The normal-two-subgroup fixed-vector theorem makes its
action descend through the actual local two-core quotient. Its Sylow-fixed
space generates by irreducibility, and restriction cannot increase the
original centralizer index. The coordinate surjection proves finiteness
without expanding the nested quotient action.

The reduced F1.11 constructor supplies every section, descent, quadraticity
and generation premise. It does not assert descent or naturality of the
whole residual section. ConstituentBounds applies this construction to the
actual rank-one models, before the later naturality assertions.
Source: DGS, *Groups and Graphs* (1985), 9.3, printed p.142; corrected 5.12,
pp.113--115, and the modular normal-p-subgroup fixed-vector argument.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

/-- An actual constituent of a specified residual action, retaining the
quotient homomorphism, actor and original index bounds. -/
structure ResidualConstituent {H D W : Type*} [Group H] [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (q : H →* D) (Aq : Subgroup D)
    (actorIndex centralizerIndex : ℕ) where
  space : Subrepresentation ρ
  action : Representation (ZMod 2) D space.toSubmodule
  finiteSpace : Finite space.toSubmodule
  irreducible : action.IsIrreducible
  descent : ∀ l, action (q l) = space.toRepresentation l
  residualFixed : fixedSpace action (pResidual 2 D) = ⊥
  generated : ∀ T : Sylow 2 D, GeneratedByFixedSpace action T
  quadratic : IsQuadratic action Aq
  elementary : IsElementaryAbelian 2 Aq
  actorCard : Nat.card Aq = actorIndex
  fixedIndex : Nat.card (space.toSubmodule ⧸ fixedSpace action Aq) ≤ centralizerIndex

private theorem irreducible_generated {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) D W) [σ.IsIrreducible] (T : Sylow 2 D) :
    GeneratedByFixedSpace σ T := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨w,hw,hfix⟩ := pGroup_fix_nonzero_vector
    (by rw [ringChar.eq (ZMod 2) 2]; decide)
    (by simpa only [ringChar.eq (ZMod 2) 2] using T.isPGroup') (σ.comp (T : Subgroup D).subtype)
  have he : fixedGeneratedSubrepresentation σ T = ⊤ := by
    rcases eq_bot_or_eq_top (fixedGeneratedSubrepresentation σ T) with hh | hh
    · have hm := fixedSpace_le_fixedGenerated σ (T : Subgroup D) hfix
      rw [hh] at hm
      exact (hw hm).elim
    · exact hh
  exact congrArg Subrepresentation.toSubmodule he

private theorem residual_constituent {H D W : Type*} [Group H] [Finite H] [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Nontrivial W]
    (ρ : Representation (ZMod 2) H W)
    (hr : fixedSpace ρ (pResidual 2 H) = ⊥)
    (q : H →* D) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker) :
    ∃ U : Subrepresentation ρ,
      ∃ σ : Representation (ZMod 2) D U.toSubmodule,
        σ.IsIrreducible ∧ (∀ l, σ (q l) = U.toRepresentation l) ∧
        fixedSpace σ (pResidual 2 D) = ⊥ ∧
        (∀ T : Sylow 2 D, GeneratedByFixedSpace σ T) ∧
        ∀ A : Subgroup H,
          (IsQuadratic ρ A → IsQuadratic σ (A.map q)) ∧
          Nat.card (U.toSubmodule ⧸ fixedSpace σ (A.map q)) ≤
            Nat.card (W ⧸ fixedSpace ρ A) := by
  obtain ⟨U,hU⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρ
  let : U.toRepresentation.IsIrreducible := hU
  obtain ⟨σ,hσ,hi⟩ := exists_irreducible_descent_of_pGroup_kernel U.toRepresentation q hq hk
  let : σ.IsIrreducible := hi
  have he : σ.comp q = U.toRepresentation := MonoidHom.ext hσ
  have hf : fixedSpace σ (pResidual 2 D) = ⊥ := by
    rw [← map_pResidual_of_surjective 2 q hq, ← fixedSpace_comp_map, he]
    apply bot_unique
    intro w hw
    apply Subtype.ext
    exact hr.le (fun a => congrArg Subtype.val (hw a))
  refine ⟨U,σ,hi,hσ,hf,irreducible_generated σ,?_⟩
  intro A
  refine ⟨?_,?_⟩
  · intro hquad
    rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩ w
    simp only [hσ]
    apply Subtype.ext
    exact hquad a ha b hb w
  · have hfixed : fixedSpace σ (A.map q) = fixedSpace U.toRepresentation A := by
      rw [← fixedSpace_comp_map,he]
    rw [hfixed]
    let : Finite (U.toSubmodule ⧸ fixedSpace U.toRepresentation A) :=
      Finite.of_surjective _ (fixedSpace U.toRepresentation A).mkQ_surjective
    let : Finite (W ⧸ fixedSpace ρ A) := Finite.of_surjective _ (fixedSpace ρ A).mkQ_surjective
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := U.toSubmodule ⧸ fixedSpace U.toRepresentation A),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W ⧸ fixedSpace ρ A),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (fixedCodim_subrepresentation_le ρ U A)

/-- Construct a constituent for any literal elementary actor on the same
residual section. The mixed branch uses the original critical center as
actor rather than the entire opposite neighborhood span. -/
theorem section_constituent {G D W : Type*} [Group G] [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Nontrivial W]
    (H K V C E : Subgroup G) [Finite H] [Finite V]
    (ρ : Representation (ZMod 2) H W) (c : BinaryConjugationSection H V C ρ)
    (hr : fixedSpace ρ (pResidual 2 H) = ⊥)
    (q : H →* D) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hker : q.ker = K.subgroupOf H) (hEH : E ≤ H)
    (helem : IsElementaryAbelian 2 E) (hquad : IsQuadratic ρ (E.subgroupOf H)) :
    Nonempty (ResidualConstituent ρ q ((E.subgroupOf H).map q)
      (K.relIndex E) ((centralizer (E : Set G)).relIndex V)) := by
  obtain ⟨U,σ,hi,hσ,hres,hgen,hbound⟩ := residual_constituent ρ hr q hq hk
  let := helem
  let : IsElementaryAbelian 2 (E.subgroupOf H) :=
    IsElementaryAbelian.comap_of_injective H.subtype H.subtype_injective E
  have hu := BinaryConjugationSection.fixed_quotient_card_le_centralizer_index
    ρ (MonoidHom.id H) c E
  simp only [Subgroup.map_id] at hu
  exact ⟨⟨U,σ,inferInstance,hi,hσ,hres,hgen,(hbound _).1 hquad,IsElementaryAbelian.map q,
    BinaryConjugationSection.actor_image_card_eq_relIndex H K E q hker hEH,
    (hbound _).2.trans hu⟩⟩

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- A nonzero irreducible submodule of the literal residual section descends
through the original two-core quotient. Its actor remains the full opposite
span image, its fixed space generates for every quotient Sylow, and its
fixed-space index is bounded by the original centralizer index. No action
descent or naturality of the whole residual section is assumed. -/
theorem reduced_critical_residual_constituent (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {D : Type*} [Group D] [Finite D]
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* D) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ beta
    let A := (V Γ beta 1).subgroupOf H
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    let Aq := ((V Γ a' 1).subgroupOf H).map q
    letI : ∀ i, Finite (Γ i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
    ∃ hb2 : 2 < b Γ,
      letI := neighborhoodIn_elementary Γ (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) beta hb2 H
      Nonempty (ResidualConstituent (fixedQuotientAction A (pResidual 2 H)) q Aq
        ((Q Γ beta).relIndex (V Γ a' 1))
        ((centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1))) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((V Γ a' 1).subgroupOf H).map q
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
  exact section_constituent H (Q Γ beta) (V Γ beta 1) _ (V Γ a' 1)
    (fixedQuotientAction A (pResidual 2 H)) c hr q hq (hk.symm ▸ pCore_isPGroup)
    hk' hVH (V_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
      (Reduction.reduced_kernel_sylow h) a' hb2) hquad
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

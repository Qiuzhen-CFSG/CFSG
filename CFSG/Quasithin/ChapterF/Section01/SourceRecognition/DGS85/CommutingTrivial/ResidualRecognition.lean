module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ResidualDescent
public import Theory.Representation.BinaryConjugationSection.FixedQuotientIndex

/-!
# Residual-section recognition in the original core indices

The literal opposite span maps to a two-subgroup of the actual linear
local quotient. Place it in a Sylow and transport the already proved
fixed-space generation to that Sylow. The action is faithful, so corrected
5.12 bounds its order by the fixed-space index. The original section
coordinates bound this index by the original centralizer index; the actor
order is exactly the opposite core index. A strict comparison consequently
produces natural coordinates on the same vectors and quotient action.

The local quotient and action descent are explicit in this application;
`ResidualDescent` constructs descent from neighboring-center quadraticity.
Initial recognition and the terminal Chapter 9 bounds remain separate.

Source: DGS, *Groups and Graphs* (1985), 9.3, printed p.142, and corrected
5.12, printed pp.113--115.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph

private theorem sylow_fixed_generation_transport {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (S T : Sylow 2 D)
    (hgen : GeneratedByFixedSpace ρ S) : GeneratedByFixedSpace ρ T := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq D S T
  have hg := generatedByFixedSpace_of_equivariant_surjection ρ ρ
    (MulAut.conj g).toMonoidHom (ρ g)
    (fun v => ⟨ρ g⁻¹ v, ρ.self_inv_apply g v⟩)
    (by intro a v; simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
      MulAut.conj_apply,map_mul,Module.End.mul_apply,ρ.inv_self_apply]) S hgen
  exact hg

/-- Numerical and natural-module conclusions on the specified action,
actor image and original group indices. -/
def ResidualIndexControl {F W : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W) (Aq : Subgroup SL(2,F))
    (n actorIndex centralizerIndex : ℕ) : Prop :=
  ∃ T : Sylow 2 SL(2,F), Aq ≤ T ∧
    GeneratedByFixedSpace σ T ∧ Function.Injective σ ∧
    Nat.card Aq = actorIndex ∧
    Nat.card Aq ≤ Nat.card (W ⧸ fixedSpace σ Aq) ∧
    Nat.card (W ⧸ fixedSpace σ Aq) ≤ centralizerIndex ∧
    (centralizerIndex < actorIndex ^ 2 →
      letI : Algebra (ZMod 2) F := ZMod.algebra F 2
      IsSourceNatural σ T n ∧ ∃ E : W ≃ₗ[ZMod 2] (Fin 2 → F),
        ∀ g z, E (σ g z) = Matrix.mulVec g.val (E z))

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Corrected 5.12 on the same residual-section vectors, with the original
opposite-span actor and original centralizer index. Its quotient action is
explicit; no faithfulness, generation or Sylow-placement premise is assumed. -/
theorem reduced_critical_residual_index_recognition (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hob : ¬ stabilizer (Reduction.reducedFamily L S₀) a ≤ normalizer
      ((Q (Reduction.reducedFamily L S₀) beta ⊓ Q (Reduction.reducedFamily L S₀) a :
        Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ beta
    let A := (V Γ beta 1).subgroupOf H
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    let Aq := ((V Γ a' 1).subgroupOf H).map q
    letI : ∀ i, Finite (Γ i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
    ∀ hb2 : 2 < b Γ,
      letI := neighborhoodIn_elementary Γ (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) beta hb2 H
      ∀ σ : Representation (ZMod 2) SL(2,F) (FixedQuotient A (pResidual 2 H)),
        (∀ l : H, σ (q l) = fixedQuotientAction A (pResidual 2 H) l) →
        ResidualIndexControl σ Aq n ((Q Γ beta).relIndex (V Γ a' 1))
          ((centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1)) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((V Γ a' 1).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  dsimp only
  intro hb2
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  intro σ hact
  obtain ⟨S,hS,hgen,hres,hfaith,hquad,_⟩ :=
    reduced_critical_linear_residual_prepared h hc hab hd hb hcomm hob hn hF e hb2 σ hact
  obtain ⟨_,hnz,⟨c⟩,_,hVH,_⟩ := reduced_critical_residual_section h hc hab hd hb hcomm
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hself : (graph Γ).dist beta beta + 1 ≤ b Γ := by
    simp only [SimpleGraph.dist_self,zero_add]; exact hb.le
  have hVL : V Γ beta 1 ≤ H := neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) beta beta hb hself
  let : Finite (V Γ beta 1) := Finite.of_injective (inclusion hVL) (inclusion_injective _)
  let : Finite A := inferInstance
  let : Finite (FixedQuotient A (pResidual 2 H)) :=
    Finite.of_surjective _ (fixedSpace (originalAction A) (pResidual 2 H)).mkQ_surjective
  have hcomp : σ.comp q = fixedQuotientAction A (pResidual 2 H) := MonoidHom.ext hact
  have hp : IsPGroup 2 Aq := by
    have he : IsElementaryAbelian 2 (V Γ a' 1) :=
      V_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
        (Reduction.reduced_kernel_sylow h) a' hb2
    exact ((he.isPGroup).comap_subtype (K := H)).map q
  obtain ⟨T,hAT⟩ := hp.exists_le_sylow
  have hgT := sylow_fixed_generation_transport σ S T hgen
  have hk : q.ker = (Q Γ beta).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    have hcore : H.pCoreIn 2 = Q Γ beta := graphLocalGroup_core ht beta
    rw [←hcore]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hcard : Nat.card Aq = (Q Γ beta).relIndex (V Γ a' 1) :=
    BinaryConjugationSection.actor_image_card_eq_relIndex H (Q Γ beta) (V Γ a' 1) q hk hVH
  have hu := BinaryConjugationSection.fixed_quotient_card_le_centralizer_index σ q
    (hcomp.symm ▸ c) (V Γ a' 1)
  have hlo := sl2_actor_bound σ hfaith T Aq hAT hF
  refine ⟨T,hAT,hgT,hfaith,hcard,hlo,hu,?_⟩
  intro hstrict
  have hfix : fixedSpace σ ⊤ = ⊥ := bot_unique ((fixedSpace_antitone σ le_top).trans hres.le)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  exact (sl2_strict_actor_natural σ hfaith T Aq hAT hquad hgT hfix hF
    (by rw [hcard]; exact hu.trans_lt hstrict))

/-- Construct the literal quotient action and apply corrected recognition
in the original indices. Only the preceding neighboring-center quadraticity
and actual linear quotient markings remain; descent, faithfulness and
Sylow-fixed generation are discharged. -/
theorem reduced_critical_constructed_residual_recognition (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hobα : ¬ stabilizer (Reduction.reducedFamily L S₀) a ≤ normalizer
      ((Q (Reduction.reducedFamily L S₀) beta ⊓ Q (Reduction.reducedFamily L S₀) a :
        Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (hobβ : ¬ stabilizer (Reduction.reducedFamily L S₀) beta ≤ normalizer
      ((Q (Reduction.reducedFamily L S₀) a ⊓ Q (Reduction.reducedFamily L S₀) beta :
        Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {K F : Type*} [Field K] [Finite K] [CharP K 2] [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (eα : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,K))
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ beta
    let A := (V Γ beta 1).subgroupOf H
    let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    let qα := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ a)))
    letI : ∀ i, Finite (Γ i) := finite_endpoints (Reduction.reduced_triple h)
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    ∀ ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)),
      (∀ (l : graphLocalGroup Γ a) (z : Additive (Z Γ a)),
        ((ρ (qα l) z).toMul : Reduction.G₀ L S₀) =
          (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) →
      (∃ R : Sylow 2 SL(2,K), IsQuadratic ρ R) →
      letI := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
      ∃ hb2 : 2 < b Γ,
        letI := neighborhoodIn_elementary Γ (Reduction.reduced_triple h).generate
          (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
          (Reduction.reduced_kernel_sylow h) beta hb2 H
        ∃ σ : Representation (ZMod 2) SL(2,F) (FixedQuotient A (pResidual 2 H)),
          (∀ l : H, σ (q l) = fixedQuotientAction A (pResidual 2 H) l) ∧
          ResidualIndexControl σ (((V Γ a' 1).subgroupOf H).map q) n
            ((Q Γ beta).relIndex (V Γ a' 1))
            ((centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1)) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  dsimp only
  intro ρ hact hquad
  obtain ⟨hb2,σ,T,hσ,_⟩ := reduced_critical_linear_residual_action h hc hab hd hb hcomm
    hobα hobβ hn hF eα eβ ρ hact hquad
  refine ⟨hb2,σ,hσ,?_⟩
  exact reduced_critical_residual_index_recognition h hc hab hd hb hcomm hobα hn hF eβ hb2 σ hσ

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

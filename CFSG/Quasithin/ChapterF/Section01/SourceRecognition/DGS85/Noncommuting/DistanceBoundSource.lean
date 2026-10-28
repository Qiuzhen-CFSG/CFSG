module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RadiusOneSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalBoundSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.EndpointRecognitionSource

/-!
# The two epsilon branches of the reduced Chapter 7 bound

The minimum `b` is taken over both vertex orbits.  Once the actual local
rank-one data are supplied on the source graph, its epsilon-one branch is the
already proved radius-one bound.  In the epsilon-two branch the literal
endpoint sections, their quotient markings and the terminal argument give
`b = 2`.  The original interface keeps its recognition inputs explicit. The specialized
`reduced_noncommuting_distance_bound_of_localData` constructs them and both
Sylow products, and applies (6.6) in the correct neighbor orientation. Only
local actor data, covariance, odd indices, the centralizer dichotomy,
(6.5) obstruction and branching remain explicit earlier-source inputs.

Source: DGS, *Groups and Graphs* (1985), (7.3)--(7.5), pp.127--131.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- The literal reduced-source Chapter 7 conclusion, split at the exact
epsilon-one/epsilon-two center alternative.  The endpoint representations
and sections are the actual quotient actions used in the epsilon-two branch.
-/
theorem reduced_noncommuting_distance_bound
    (h : HypothesisF11 L₀ S₀)
    (L : Vertex F → Subgroup (G₀ L₀ S₀))
    (hL : ∀ x, L x ≤ stabilizer F x)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph F).Adj x y →
      LocalRankOneData (stabilizer F x) (stabilizer F x ⊓ stabilizer F y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer F x))
    (hprod : ∀ x y, IsCriticalPair F x y → ⁅Z F x,Z F y⁆ ≠ ⊥ →
      Stellmacher.IsSylowSubgroupIn (Z F x ⊔ Q F y) (stabilizer F y))
    (h66 : ∀ x y, (graph F).Adj x y →
      stabilizer F x ≤ normalizer ((Z F y ⊔ Z F x : Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)) →
      Z F x = Stellmacher.omegaOneCenterAmbient
        ((stabilizer F x ⊓ stabilizer F y).pCoreIn 2))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x)
      (L x ⊓ centralizer (Z F x : Set (G₀ L₀ S₀))) ∨
      Z F x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph F).Adj x y → ¬ stabilizer F y ≤
      normalizer ((Q F x ⊓ Q F y : Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)))
    {v w u : Vertex F} (hc : IsCriticalPair F v w)
    (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hvu : (graph F).Adj v u)
    (hdu : (graph F).dist u w + 1 = b F)
    (E₀ E₁ : Subgroup (G₀ L₀ S₀))
    (c₀ : LocalRankOneData (stabilizer F v) E₀)
    (c₁ : LocalRankOneData (stabilizer F w) E₁)
    (h₀ : c₀.Pstar = L v) (h₁ : c₁.Pstar = L w)
    [((Q F v).subgroupOf c₀.Pstar).Normal]
    [((Q F w).subgroupOf c₁.Pstar).Normal]
    {W₀ W₁ : Type*}
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (σ₀ : Representation (ZMod 2) (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar) W₀)
    (σ₁ : Representation (ZMod 2) (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar) W₁)
    (d₀ : BinaryConjugationSection c₀.Pstar (Z F v)
      (Stellmacher.omegaOneCenterAmbient c₀.Pstar)
      (σ₀.comp (QuotientGroup.mk' ((Q F v).subgroupOf c₀.Pstar))))
    (d₁ : BinaryConjugationSection c₁.Pstar (Z F w)
      (Stellmacher.omegaOneCenterAmbient c₁.Pstar)
      (σ₁.comp (QuotientGroup.mk' ((Q F w).subgroupOf c₁.Pstar))))
    (M₀ : BinaryRankOneModel (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar))
    (M₁ : BinaryRankOneModel (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar))
    (hf₀ : Function.Injective σ₀) (hf₁ : Function.Injective σ₁)
    (hr₀ : fixedSpace σ₀ (pResidual 2 (c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar)) = ⊥)
    (hr₁ : fixedSpace σ₁ (pResidual 2 (c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar)) = ⊥)
    (hbranch : ∀ i, ∃ k, ((F (!i)).subgroupOf (F i)).index - 1 = 2^k) :
    b F = 1 ∨ b F = 2 := by
  by_cases hcentral : Z F u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer F v ⊓ stabilizer F u).pCoreIn 2)
  · have hb := reduced_epsilonTwo_distance_two h L hcov d hstar hodd hdich hob
      hc hne hvu hdu hcentral E₀ E₁ c₀ c₁ h₀ h₁ σ₀ σ₁ d₀ d₁ M₀ M₁
      hf₀ hf₁ hr₀ hr₁ hbranch
    exact Or.inr hb.2
  · have hle := reduced_epsilonOne_bound_of_localData h L hL hcov d hstar hodd
      hprod h66 hdich hc hne hvu hcentral
    exact hle

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- Both distance branches from the actual local actors and earlier Chapter 6 inputs.
All endpoint representations, models, natural coordinates and Sylow products are constructed. -/
theorem reduced_noncommuting_distance_bound_of_localData
    (h : HypothesisF11 L₀ S₀)
    (L : Vertex F → Subgroup (G₀ L₀ S₀))
    (hL : ∀ x, L x ≤ stabilizer F x)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph F).Adj x y →
      LocalRankOneData (stabilizer F x) (stabilizer F x ⊓ stabilizer F y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer F x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x)
      (L x ⊓ centralizer (Z F x : Set (G₀ L₀ S₀))) ∨
      Z F x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph F).Adj x y → ¬ stabilizer F y ≤
      normalizer ((Q F x ⊓ Q F y : Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)))
    {v w : Vertex F} (hc : IsCriticalPair F v w)
    (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hbranch : ∀ i, ∃ k, ((F (!i)).subgroupOf (F i)).index - 1 = 2^k) :
    (b F = 1 ∨ b F = 2) ∧
    HasNaturalCenter (L v) (Z F v) (Q F v) ∧
    HasNaturalCenter (L w) (Z F w) (Q F w) := by
  let ht := reduced_triple h
  have hn := reduced_critical_natural_centers_of_localData h L d hstar hodd hc hne
  refine ⟨?_,hn.1,hn.2.1⟩
  have hvw : v ≠ w := by
    intro he
    have hd := hc.1
    have hp : 0 < b F := source_b_positive ht
    rw [he,SimpleGraph.dist_self] at hd
    omega
  obtain ⟨u,hvu,hdu⟩ := exists_predecessor F ht.generate w v hvw.symm
  have hdu' : (graph F).dist u w + 1 = b F := by
    simpa only [SimpleGraph.dist_comm (u := w),hc.1] using hdu
  by_cases hcentral : Z F u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer F v ⊓ stabilizer F u).pCoreIn 2)
  · exact Or.inr (graph_epsilonTwo_distance_two ht (reduced_borel_core_sylow h)
      (reduced_kernel_sylow h) L hcov d hstar hodd hdich hob hc hne hvu hdu'
      hcentral hn.1 hn.2.1 hn.2.2.2 hbranch)
  · let := finite_endpoints ht
    let : ∀ i, Finite (F i) := finite_endpoints ht
    let := graph_Z_elementary ht w
    let : IsElementaryAbelian 2 (Z F w) := graph_Z_elementary ht w
    have hother : Z F w ≤ L v := by
      rw [←hstar v u hvu]
      exact local_twoGroup_le_star (d v u hvu) (by rw [hstar]; exact hodd v)
        _ (IsElementaryAbelian.isPGroup 2 _) (criticalPair_centers F ht.generate hc).1
    have hnoncentral : Z F u ≠ Stellmacher.omegaOneCenterAmbient (L u) := by
      rw [←hstar u v hvu.symm]
      apply graph_noncentral_of_edgeSeed_ne ht (reduced_borel_core_sylow h) hvu.symm
        (d u v hvu.symm) (by rw [hstar]; exact hodd u)
      simpa only [reducedFamily,inf_comm] using hcentral
    have hCS := graph_sylow_centralizers_of_epsilonOne ht L hcov hdich
      hvu hnoncentral hother hne
    have hobs : ∀ x y, (graph F).Adj x y → ¬ stabilizer F x ≤
        normalizer ((Z F y ⊔ Z F x : Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)) := by
      intro x y he hnorm
      have hseed := (reduced_normal_center_product h he.symm hnorm (hob y x he.symm)).1
      obtain ⟨T,hT⟩ := source_edge_vertex_sylow ht (reduced_vertex_sylow h) he.symm
      have heq := Theory.GroupTheory.AmalgamGraph.sylow_image_eq_edge_core
        (stabilizer F y) (stabilizer F y ⊓ stabilizer F x) inf_le_left
        (source_edge_core_sylow ht (reduced_borel_core_sylow h) he.symm) T hT
      apply graph_seed_ne_of_centralizerSylow ht (reduced_borel_core_sylow h) he.symm
        (d y x he.symm) (by rw [hstar]; exact hodd y)
        (by rw [hstar]; exact hCS y)
      exact (hseed T).trans (congrArg omegaCenterIn heq)
    have hb := graph_radiusOne_bound_of_localData ht (reduced_borel_core_sylow h)
      (reduced_kernel_sylow h) L hL d hstar hodd
      (fun x y hc hne =>
        (reduced_critical_natural_centers_of_localData h L d hstar hodd hc hne).2.2.2)
      hobs hCS hc hne
    have hb' : b F ≤ 2 := hb
    have hp : 0 < b F := source_b_positive ht
    omega

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction

module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReciprocalRecognizedSections
public import Theory.Representation.SL2.StrictCoverDescent
public import Theory.Representation.RankOne.QuadraticRecognition.SL2PairGeneration

/-!
# The nonnatural residual square bound without assumed action descent

The original opposite span is a quadratic actor on the canonical residual
section. When its local quotient image is a full Sylow, any smaller actor
escaping the local core has displacement at least the square of the field
order, unless the entire canonical residual section is natural.

A hypothetical strict bound first gives irreducibility and quotient descent
through the normal Sylow seed theorem. The full quadratic Sylow then has
the same fixed space as the smaller actor, so corrected 5.12 recognizes
natural coordinates on the original vectors. Thus 8.5 supplies the square
bound by its exact nonnaturality conclusion, with no constituent-to-whole
naturality inference and no assumed descent.

Source: DGS, Groups and Graphs (1985), 8.5--8.7 and 5.10, printed pp.139--140.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open CommutingTrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- A strict displacement bound for an escaping subgroup of the opposite
span recognizes the entire original residual section. -/
theorem reduced_critical_strict_residual_natural (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hob : ¬ stabilizer (Reduction.reducedFamily L S₀) a ≤ normalizer
      ((Q (Reduction.reducedFamily L S₀) beta ⊓ Q (Reduction.reducedFamily L S₀) a :
        Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hactor : (Q (Reduction.reducedFamily L S₀) beta).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1) = Nat.card F)
    (E : Subgroup (Reduction.G₀ L S₀))
    (hEV : E ≤ V (Reduction.reducedFamily L S₀) a' 1)
    (hEQ : ¬ E ≤ Q (Reduction.reducedFamily L S₀) beta)
    (hindex : (centralizer (E : Set (Reduction.G₀ L S₀))).relIndex
      (V (Reduction.reducedFamily L S₀) beta 1) < Nat.card F ^ 2) :
    NaturalResidualSection h beta e n := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let U := (V Γ beta 1).subgroupOf H
  let B := (Q Γ a).subgroupOf H
  let A := (V Γ a' 1).subgroupOf H
  let D := E.subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := A.map q
  let Dq := D.map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  obtain ⟨hb2,hnz,⟨c⟩,hzero,hVH,hquad,hBH,hgen⟩ :=
    reduced_critical_residual_actor_generated h hc hab hd hb hcomm
  refine ⟨hb2,?_⟩
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let W := FixedQuotient U (pResidual 2 H)
  let ρ := fixedQuotientAction U (pResidual 2 H)
  let : Nontrivial W := hnz
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hVL : V Γ beta 1 ≤ H := neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) beta beta hb
    (show (graph Γ).dist beta beta + 1 ≤ b Γ by simpa only [SimpleGraph.dist_self,zero_add] using hb.le)
  let : Finite (V Γ beta 1) := Finite.of_injective (inclusion hVL) (inclusion_injective _)
  let : Finite W := Finite.of_surjective (fun x : V Γ beta 1 => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkQ : q.ker = (Q Γ beta).subgroupOf H := by
    have hcore : H.pCoreIn 2 = Q Γ beta := graphLocalGroup_core ht beta
    rw [hk,←hcore]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hp : IsPGroup 2 q.ker := hk.symm ▸ pCore_isPGroup
  have hEH : E ≤ H := hEV.trans hVH
  have hDn : Dq ≠ ⊥ := by
    intro hh
    have hle := (Subgroup.map_eq_bot_iff _).mp hh
    rw [hkQ] at hle
    exact hEQ (fun x hx => hle (show (⟨x,hEH hx⟩ : H) ∈ D from hx))
  have hAe : IsElementaryAbelian 2 (V Γ a' 1) := V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) a' hb2
  have hAp : IsPGroup 2 Aq := (hAe.isPGroup.comap_subtype (K := H)).map q
  have hDp : IsPGroup 2 Dq := (hAp.to_le (map_mono (subgroupOf_mono H hEV)))
  obtain ⟨T,hT,hTf⟩ := linear_neighbor_core_sylow_image ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab.symm
    (core_escape_of_intersection_obstruction Γ hob) e
  change B.map q = (T : Subgroup SL(2,F)) at hT
  let S : Sylow 2 H := T.comapOfKerIsPGroup q hp (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top)
  have hS : q.ker ⊔ B = S := by
    have hh := congrArg (Subgroup.comap q) hT
    rw [comap_map_eq] at hh
    exact (sup_comm _ _).trans hh
  have hnormal : (S : Subgroup H) ≤ normalizer (B : Set H) := by
    intro l hl
    apply le_normalizer_comap H.subtype
    apply stabilizer_normalizes_Q Γ a
    exact (hTf l).mp ((T : Subgroup SL(2,F)).le_normalizer hl)
  have hBn : B.map q ≠ ⊥ := by
    rw [hT]
    intro hz
    have hcard : Nat.card (T : Subgroup SL(2,F)) = Nat.card F :=
      Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv
    rw [hz,card_bot,hF] at hcard
    have hpw : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hu := BinaryConjugationSection.fixed_quotient_card_le_centralizer_index
    ρ (MonoidHom.id H) c E
  simp only [Subgroup.map_id] at hu
  obtain ⟨σ,hσ,hσirr⟩ := SL2.strict_cover_descent ρ q hq hp B S hS hnormal hBn hzero hgen
    D hDp hDn hn hF (hu.trans_lt hindex)
  have hcomp : σ.comp q = ρ := MonoidHom.ext hσ
  obtain ⟨R,hAR,hgR,hfaith,hcard,hlo,hup,_⟩ :=
    reduced_critical_residual_index_recognition h hc hab hd hb hcomm hob (by omega) hF e hb2 σ hσ
  have hAR_eq : Aq = (R : Subgroup SL(2,F)) := by
    apply eq_of_le_of_card_ge hAR
    have hRc : Nat.card (R : Subgroup SL(2,F)) = Nat.card F :=
      Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 R).symm.toEquiv
    exact hRc.le.trans_eq (hcard.trans hactor).symm
  have hquadσ : IsQuadratic σ Aq := by
    rintro x ⟨x',hx,rfl⟩ y ⟨y',hy,rfl⟩ z
    change (σ (q x')) (σ (q y') z - z) = σ (q y') z - z
    rw [hσ,hσ]
    exact hquad x' hx y' hy z
  have hgenA : GeneratedByFixedSpace σ Aq := hAR_eq.symm ▸ hgR
  have hAc : 4 ≤ Nat.card Aq := by
    rw [hcard,hactor,hF]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ n)
  have hDA : Dq ≤ Aq := map_mono (subgroupOf_mono H hEV)
  obtain ⟨t,htD,ht1⟩ := Dq.bot_or_exists_ne_one.resolve_left hDn
  have hfixed : fixedSpace σ Dq = fixedSpace σ Aq := by
    have he := sl2_quadratic_fixedSpace_eq σ (by omega) hF R Aq hAR hAc hquadσ hgenA t (hDA htD) ht1
    exact le_antisymm ((fixedSpace_antitone σ (zpowers_le.mpr htD)).trans he.symm.le)
      (fixedSpace_antitone σ hDA)
  have hstrict : Nat.card (W ⧸ fixedSpace σ Aq) < Nat.card Aq ^ 2 := by
    rw [←hfixed,hcard,hactor]
    have hfixD : fixedSpace σ Dq = fixedSpace ρ D := by rw [←fixedSpace_comp_map,hcomp]
    rw [hfixD]
    exact hu.trans_lt hindex
  have hres : fixedSpace σ (pResidual 2 SL(2,F)) = ⊥ := by
    rw [←map_pResidual_of_surjective 2 q hq,←fixedSpace_comp_map,hcomp]
    exact hzero
  have hfix : fixedSpace σ ⊤ = ⊥ := bot_unique ((fixedSpace_antitone σ le_top).trans hres.le)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨hN,E₀,hE₀⟩ := sl2_strict_actor_natural σ hfaith R Aq hAR hquadσ hgR hfix hF hstrict
  exact ⟨σ,R,hσ,hfaith,hN,E₀,hE₀⟩

/-- The lower comparison used in 8.6 and 8.7. Its nonnaturality premise is
exactly the conclusion of 8.5 for the canonical residual section. -/
theorem reduced_critical_nonnatural_residual_square (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hob : ¬ stabilizer (Reduction.reducedFamily L S₀) a ≤ normalizer
      ((Q (Reduction.reducedFamily L S₀) beta ⊓ Q (Reduction.reducedFamily L S₀) a :
        Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hactor : (Q (Reduction.reducedFamily L S₀) beta).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1) = Nat.card F)
    (E : Subgroup (Reduction.G₀ L S₀))
    (hEV : E ≤ V (Reduction.reducedFamily L S₀) a' 1)
    (hEQ : ¬ E ≤ Q (Reduction.reducedFamily L S₀) beta)
    (hnatural : ¬ NaturalResidualSection h beta e n) :
    Nat.card F ^ 2 ≤ (centralizer (E : Set (Reduction.G₀ L S₀))).relIndex
      (V (Reduction.reducedFamily L S₀) beta 1) := by
  by_contra! hsmall
  exact hnatural (reduced_critical_strict_residual_natural h hc hab hd hb hcomm hob
    hn hF e hactor E hEV hEQ hsmall)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

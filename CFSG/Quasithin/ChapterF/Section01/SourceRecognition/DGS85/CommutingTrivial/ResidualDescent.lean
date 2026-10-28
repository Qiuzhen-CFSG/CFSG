module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CoreDisplacement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.LinearResidual

/-!
# Descending the original residual neighborhood action

Core displacement in the local central omega vanishes on the literal
V/C_V(O²(L)) section. Thus conjugation factors through an actual local
core quotient, with equality on every representative. The reduced-source
application combines the neighboring quadratic-center argument with the
proved Sylow-fixed generation and faithfulness of the same residual section.

This discharges action descent from the core-displacement bound. A supplied
linear quotient and quadratic action on the neighboring center remain
explicit; this does not establish the preceding recognition in 9.3--9.4
or the terminal distance and field conclusions. The final Chapter 9
assembly must discharge those premises without circularity.

Source: DGS, *Groups and Graphs* (1985), 9.3--9.4, printed pp.142--143,
and the corrected fixed-space-generation hypothesis of 5.12.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

open Representation.NormalElementaryQuotient

/-- The literal residual section descends through any actual local core
quotient once its core displacement is in the local central omega. -/
theorem neighborhood_residual_action_descent
    (h : LocallyRankOneTriple P B)
    (hS : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    (v : Vertex (family P)) (hb : 2 < b (family P))
    (hz : Z (family P) v = omegaCenterIn (graphLocalGroup (family P) v))
    (hc : ⁅V (family P) v 1,Q (family P) v⁆ ≤ Z (family P) v)
    {D : Type*} [Group D]
    (q : graphLocalGroup (family P) v →* D) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (graphLocalGroup (family P) v)) :
    let H := graphLocalGroup (family P) v
    let A := (V (family P) v 1).subgroupOf H
    letI := finite_endpoints h
    letI := neighborhoodIn_normal (family P) v H (sylowGenerated_le _)
    letI := neighborhoodIn_elementary (family P) h.generate
      (fun w => (source_Z_Q_U h w).1) hS v hb H
    ∃ σ : Representation (ZMod 2) D (FixedQuotient A (pResidual 2 H)),
      ∀ l : H, σ (q l) = fixedQuotientAction A (pResidual 2 H) l := by
  let := finite_endpoints h
  let H := graphLocalGroup (family P) v
  let A := (V (family P) v 1).subgroupOf H
  let := neighborhoodIn_normal (family P) v H (sylowGenerated_le _)
  let := neighborhoodIn_elementary (family P) h.generate
    (fun w => (source_Z_Q_U h w).1) hS v hb H
  apply exists_fixedQuotientAction_descent A (pResidual 2 H) q hq
  apply commutator_le.mpr
  intro a ha k hk'
  have hkQ : (k : G) ∈ Q (family P) v := by
    rw [←graphLocalGroup_core h v]
    exact mem_map_of_mem H.subtype (hk ▸ hk')
  have hcZ : (⁅a,k⁆ : H).val ∈ Z (family P) v :=
    hc (commutator_mem_commutator ha hkQ)
  have hcC := ((mem_omegaCenterIn_iff _ _).mp (hz ▸ hcZ)).2.1
  intro r hr
  exact Subtype.ext (hcC r r.property)

open Representation.RankOne.QuadraticRecognition
variable {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The reduced source application constructs the actual residual quotient
representation from neighboring-center quadraticity; no descent,
faithfulness or fixed-space-generation premise is supplied. The two exact
6.5(a) obstructions remain owned by the earlier source setup. -/
theorem reduced_critical_linear_residual_action (h : HypothesisF11 L S₀)
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
        ∃ (σ : Representation (ZMod 2) SL(2,F) (FixedQuotient A (pResidual 2 H)))
          (T : Sylow 2 SL(2,F)),
          (∀ l : H, σ (q l) = fixedQuotientAction A (pResidual 2 H) l) ∧
          ((Q Γ a).subgroupOf H).map q = T ∧
          GeneratedByFixedSpace σ T ∧
          fixedSpace σ (pResidual 2 SL(2,F)) = ⊥ ∧ Function.Injective σ ∧
          IsQuadratic σ (((V Γ a' 1).subgroupOf H).map q) ∧
          ∀ l : H, q l ∈ normalizer (T : Set SL(2,F)) ↔ (l : Reduction.G₀ L S₀) • a = a := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  dsimp only
  intro ρ hact hquad
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  have hgeom := Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm
  have hb3 : 3 ≤ b Γ := hgeom.2.1
  have hb2 : 2 < b Γ := by omega
  refine ⟨hb2, ?_⟩
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  have hdisp := linear_neighbor_quadratic_core_displacement ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab
    (core_escape_of_intersection_obstruction Γ hobβ) eα ρ hact hquad
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ eβ.injective, QuotientGroup.ker_mk']
  obtain ⟨σ, hσ⟩ := neighborhood_residual_action_descent ht
    (Reduction.reduced_kernel_sylow h) beta hb2 hgeom.2.2.1 hdisp q
    (eβ.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 H))) hk
  obtain ⟨T,hT,hgen,hres,hfaith,hquadr,hTf⟩ :=
    reduced_critical_linear_residual_prepared h hc hab hd hb hcomm hobα hn hF eβ hb2 σ hσ
  exact ⟨σ,T,hσ,hT,hgen,hres,hfaith,hquadr,hTf⟩

/-- The literal reduced graph satisfies both commutator identities in 9.4(c)
once the preceding natural-center assertion is proved on its actual quotient.
The neighboring central-omega identity is supplied by the critical geometry. -/
theorem reduced_critical_natural_core_commutator (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hob : ¬ stabilizer (Reduction.reducedFamily L S₀) beta ≤ normalizer
      ((Q (Reduction.reducedFamily L S₀) a ⊓ Q (Reduction.reducedFamily L S₀) beta :
        Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ a)))
    ∀ ρ : Representation (ZMod 2) SL(2,F) (Additive (Z Γ a)),
      (∀ (l : graphLocalGroup Γ a) (z : Additive (Z Γ a)),
        ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
          (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) →
      Function.Injective ρ → (∃ T : Sylow 2 SL(2,F), IsSourceNatural ρ T n) →
      ⁅Q Γ beta, Z Γ a⁆ = Z Γ beta ∧ ⁅V Γ beta 1,Q Γ beta⁆ = Z Γ beta := by
  exact linear_natural_neighbor_core_commutator (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab
    (core_escape_of_intersection_obstruction _ hob)
    (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1 hn hF e

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

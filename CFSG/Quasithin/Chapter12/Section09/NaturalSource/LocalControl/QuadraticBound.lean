module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointJoin
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.F8SourceApplication
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.OriginalF916

/-!
# Quadratic actors on the original abelian natural span

For every J in the original Hz family, the abelian point span supplies all
F.8.1 and F.9.1 hypotheses, with V+ = V. The order-two point has equal
normalizer and centralizer, so both local residuals are the literal L₁.
Intersecting seed conjugates commute by 12.8.6, and V+ = V discharges the
extra centralizer condition in the critical-pair proof of F.9.16.

That proof constructs the faithful J/O₂(J) action on U_J/V₁ and gives
quadratic ratio at most two. The actual overlap LT intersect J is L₁T;
hence a nontrivial quadratic actor with fixed codimension at most twice
its rank lies in the image of the original R₁ = O₂(L₁T). The final
application uses J = K₁T with the preceding quotient-centralizer and
outer-two premises, without assuming the surviving point models.

Source: Aschbacher--Smith, 12.8.6 and the proof of 12.9.5,
printed pp.848, 860--861; F.9.1, F.9.2(4), F.9.16(3--4), pp.317--324.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.ModuleBound
universe u
variable {G : Type u} [Group G] [Finite G]
  {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

private theorem source_characteristic_L
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K) :
    generalizedFitting L = pCore 2 L := by
  let J := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf J
  let e : A ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  have hh := Chapter1.lemma_1_1_4_6 T (h.source.simpleQTKE.evenCharacteristic T)
    (show J ∈ Chapter1.HOver G (T : Set G) from
      ⟨h.source.maximal_faithful.1.1.2.2,fun _ hx => mem_sup_right hx⟩)
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer (h.sylow_normalizes earlier.structural))
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
      (normal_core_selfCentralizing (Chapter1.mem_He_iff.mp hh) A))

/-- F.8.1 on every original point overgroup, from the abelian span. -/
theorem abelian_local_f8
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    ChapterF.Section08.Setup.Hypothesis (F.f8SourceSetup L J) := by
  let := h.chosen.elementary
  obtain ⟨z,hz,hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by have := h.rank; omega)
  apply F.f8Source_hypothesis h.source.simpleQTKE L _ (by have := h.rank; omega)
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique earlier.structural earlier.uniqueness).2
    (h.seed_centralizer_le earlier.structural earlier.uniqueness) h.centralizer_L
    (source_characteristic_L h earlier) (h.seed_reduced earlier.structural)
    (h.centralizer_LT earlier.structural) z hpoint hz ?_ hab J hJ
  intro x hx hx1
  obtain ⟨l,hl,he⟩ := h.vector_transitive
    (F.le_seed 1 (hpoint ▸ mem_zpowers z)) hx hz hx1
  exact ⟨l,h.chosen.normalizes hl,he⟩

/-- The F.9 setup uses V itself as V+, retaining the original point and residual. -/
abbrev naturalF9Setup (F : InvariantFlag T V n) (L J : Subgroup G) :
    ChapterF.Section09.Setup G := ⟨T,L,V,V,F.Vi 1,J⟩

/-- All F.9.1 clauses hold on the actual abelian natural branch. -/
theorem abelian_local_f9
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    (naturalF9Setup F L J).Hypothesis := by
  let hf := abelian_local_f8 h earlier F hab J hJ
  let D := naturalF9Setup F L J
  have hpoint : Nat.card (F.Vi 1) = 2 := by
    simpa using F.card 1 (by have := h.rank; omega)
  have hcent : F.H = centralizer (F.Vi 1 : Set G) :=
    le_antisymm (normalizer_le_centralizer_of_card_two _ hpoint)
      (Subgroup.centralizer_le_normalizer _)
  have hres : D.L₁ = (F.f8SourceSetup L J).L₁ := by
    change (pResidual 2 (L ⊓ centralizer (F.Vi 1 : Set G) : Subgroup G)).map
        (L ⊓ centralizer (F.Vi 1 : Set G)).subtype =
      (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype
    rw [hcent]
  have hvJ : V ≤ J := hf.V_le_T.trans (le_sup_right.trans hf.local_le)
  refine {
    elementary := hf.elementary
    residual := hf.residual
    normalizes_L := hf.T_normalizes_L
    characteristic_L := hf.characteristic_L
    V_le_LT := hf.V_le_LT
    reduced := hf.reduced
    sylow_centralizer := hf.centralizer_eq
    point_card := hpoint
    normalizes_point := F.invariant 1
    point_lt := lt_of_le_of_ne hf.point_le hf.quotient_nonzero
    plus_le := le_rfl
    H_centralizes := hJ.2.1.trans hcent.le
    local_le := by change D.L₁ ⊔ (T : Subgroup G) ≤ J; rw [hres]; exact hf.local_le
    characteristic_H := hf.characteristic_H
    kernel_core := ?_
    local_normalizes := ?_
    irreducible := ?_
    normalizer_control := le_rfl
    generated_core := hf.generated_core
    commutator_lifting := ?_ }
  · have he := (F.f8SourceSetup L J).quotientCentralizer_eq_intrinsic hf.H_le V hvJ
    rw [←he]
    exact hf.centralizer_core_le
  · change D.L₁ ⊔ (T : Subgroup G) ≤ normalizer (V : Set G)
    rw [hres,F.localKernel_L₁ L J]
    exact sup_le ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
      (h.sylow_normalizes_seed earlier.structural)
  · intro A ha hb hn
    apply hf.irreducible A ha hb
    change D.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) at hn
    rwa [hres] at hn
  · intro g hg _ _ _
    let : IsMulCommutative (conjugateSpanBy V J) :=
      ((h.abelian_source_geometry earlier F).1.mpr hab) J hJ
    let : IsMulCommutative (F.UH J) := inferInstanceAs
      (IsMulCommutative (conjugateSpanBy V J))
    have hv : V ≤ F.UH J := le_conjugateSpanBy _ _
    have hvg : V.map (MulAut.conj g).toMonoidHom ≤ F.UH J := by
      rintro _ ⟨v,hv,rfl⟩
      exact subset_closure ⟨g,hg,v,hv,rfl⟩
    have hc : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        (hv.trans ((le_centralizer (F.UH J)).trans (Subgroup.centralizer_le hvg)))
    exact ⟨hc,(commutator_comm _ _).trans hc⟩

/-- F.9.16(3) on the literal quotient of every original point overgroup. -/
theorem abelian_local_quadratic_bound
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    ∃ hU : IsElementaryAbelian 2 (F.UH J),
      let := hU
      ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
        quadraticRatio a.representation ≤ 2 := by
  let := h.chosen.elementary
  let : IsMulCommutative (conjugateSpanBy V J) :=
    ((h.abelian_source_geometry earlier F).1.mpr hab) J hJ
  apply OriginalF916.original_bounded_action
    (SourceF91.ofF91 (abelian_local_f9 h earlier F hab J hJ))
  · intro g hg
    have hh := ((h.abelian_source_geometry earlier F).2.mp hab) g⁻¹
    simpa only [conjugate,inv_inv] using
      hh (by simpa only [conjugate,inv_inv] using hg)
  · intro x hx
    left
    rw [commutator_eq_bot_iff_le_centralizer,le_centralizer_iff]
    exact zpowers_le.mpr hx

/-- The original edge is L₁T, so the bound is witnessed in the literal R₁. -/
theorem abelian_local_quadratic_actor
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    ∃ hU : IsElementaryAbelian 2 (F.UH J),
      let := hU
      ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
        quadraticRatio a.representation ≤ 2 ∧
        ∃ B : Subgroup J,
          B ≤ (F.Ri L 1).subgroupOf J ∧
          IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 J))) ∧
          IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 J))) ∧
          fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 J))) ≤
            2 * rank (B.map (QuotientGroup.mk' (pCore 2 J))) := by
  obtain ⟨hU,a,ha⟩ := abelian_local_quadratic_bound h earlier F hab J hJ
  let : IsElementaryAbelian 2 (conjugateSpanBy V J) := hU
  let := h.chosen.elementary
  let : IsMulCommutative (conjugateSpanBy V J) :=
    ((h.abelian_source_geometry earlier F).1.mpr hab) J hJ
  have hf := abelian_local_f9 h earlier F hab J hJ
  have hres : (naturalF9Setup F L J).L₁ = F.Li L 1 :=
    hf.g2_L₁.symm.trans (F.localKernel_L₁ L J)
  have hedge : (L ⊔ (T : Subgroup G)) ⊓ J = F.Li L 1 ⊔ (T : Subgroup G) := by
    have he := hf.LT_inf_H_eq
    change (L ⊔ (T : Subgroup G)) ⊓ J =
      (naturalF9Setup F L J).L₁ ⊔ (T : Subgroup G) at he
    rwa [hres] at he
  refine ⟨hU,a,ha,?_⟩
  change ∃ B : Subgroup J,
    B ≤ ((F.Li L 1 ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf J ∧ _
  rw [←hedge]
  apply OriginalF916.original_witness
    (SourceF91.ofF91 (abelian_local_f9 h earlier F hab J hJ))
  · intro g hg
    have hh := ((h.abelian_source_geometry earlier F).2.mp hab) g⁻¹
    simpa only [conjugate,inv_inv] using
      hh (by simpa only [conjugate,inv_inv] using hg)
  · intro x hx
    left
    rw [commutator_eq_bot_iff_le_centralizer,le_centralizer_iff]
    exact zpowers_le.mpr hx

/-- Apply the original quadratic construction to the actual K₁T of 12.9.5.
Only its preceding quotient-centralizer and outer-two premises are used;
the surviving model list is not assumed. -/
theorem abelian_point_join_quadratic_actor
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (C : ComponentGeometry F L)
    (ho : IsPGroup 2 (MulAut.Outer (C.K1 ⧸ pCore 2 C.K1)))
    (hc : pointQuotientCentralizer C ≤ normalizer (L : Set G)) :
    ∃ hU : IsElementaryAbelian 2 (F.UH (C.K1 ⊔ (T : Subgroup G))),
      let := hU
      ∃ a : LocalQuotientAction (C.K1 ⊔ (T : Subgroup G))
        (F.UH (C.K1 ⊔ (T : Subgroup G))) (F.Vi 1),
        quadraticRatio a.representation ≤ 2 ∧
        ∃ B : Subgroup (C.K1 ⊔ (T : Subgroup G) : Subgroup G),
          B ≤ (F.Ri L 1).subgroupOf (C.K1 ⊔ (T : Subgroup G)) ∧
          IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 (C.K1 ⊔ (T : Subgroup G) : Subgroup G)))) ∧
          IsQuadratic a.representation
            (B.map (QuotientGroup.mk' (pCore 2 (C.K1 ⊔ (T : Subgroup G) : Subgroup G)))) ∧
          fixedCodim a.representation
            (B.map (QuotientGroup.mk' (pCore 2 (C.K1 ⊔ (T : Subgroup G) : Subgroup G)))) ≤
            2 * rank (B.map (QuotientGroup.mk' (pCore 2 (C.K1 ⊔ (T : Subgroup G) : Subgroup G)))) :=
  abelian_local_quadratic_actor h earlier F hab _
    (point_join_mem_Hz_of_quotient_centralizer h earlier F C ho hc)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource

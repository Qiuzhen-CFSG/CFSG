module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Recognition.Action
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The G.1.6 hypotheses on the original source action

An actual Sylow witness in K* and its literal image equality identify its
binary fixed space with C_{V_H}(A). Orbit generation gives the first G.1.6
hypothesis. E.3.6, using s(G,V)=n and the actual Sylow rank, gives uniformity.
The selected conjugate A=V^g is retained throughout.

Source: Aschbacher--Smith, 11.3.7 and G.1.6, printed pp.773 and 329.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
namespace NaturalRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {H : Subgroup G}
  {F : Type*} [Field F]
  [IsElementaryAbelian 2 (omegaClosure T H)]
  (e : residualStar T H ≃* SL(2,F)) (R : Sylow 2 (residualStar T H))
  (A : Subgroup G) (hAH : A ≤ H)
  (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
    (A.subgroupOf H).map (starProjection T H))

include hAH hR in
theorem sylow_fixed_iff (v : Additive (omegaClosure T H)) :
    v ∈ fixedSpace (binaryAction T H e) (R.mapSurjective (f := e.toMonoidHom) e.surjective) ↔
      (v.toMul : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro hv a ha
    have hi : starProjection T H ⟨a,hAH ha⟩ ∈
        (R : Subgroup (residualStar T H)).map (residualStar T H).subtype := by
      rw [hR]
      exact mem_map_of_mem (starProjection T H) ha
    obtain ⟨r,hr,he⟩ := hi
    change (r : Star T H) = starProjection T H ⟨a,hAH ha⟩ at he
    have hf := congrArg Additive.toMul
      (hv ⟨e r,mem_map_of_mem e.toMonoidHom hr⟩)
    change (binaryAction T H e (e r) v).toMul = v.toMul at hf
    rw [binaryAction_equiv,he] at hf
    have hf' := congrArg (fun w : omegaClosure T H => (w : G)) hf
    rw [starAction_apply] at hf'
    exact mul_inv_eq_iff_eq_mul.mp hf'
  · intro hv a
    obtain ⟨r,hr,ha⟩ := a.property
    change e r = a.val at ha
    change binaryAction T H e a.val v = v
    rw [← ha]
    apply Additive.toMul.injective
    rw [binaryAction_equiv]
    have hi : r.val ∈ (A.subgroupOf H).map (starProjection T H) := by
      rw [← hR]
      exact mem_map_of_mem (residualStar T H).subtype hr
    obtain ⟨b,hb,hbr⟩ := hi
    rw [← hbr]
    apply Subtype.ext
    rw [starAction_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (hv b hb)

include hAH hR in
theorem generated_of_conjugateSpan
    (hgen : conjugateSpanBy (omegaClosure T H ⊓ centralizer (A : Set G))
      (outsideResidual H) = omegaClosure T H) :
    (⨆ g : SL(2,F),
      (fixedSpace (binaryAction T H e) (R.mapSurjective (f := e.toMonoidHom) e.surjective)).map
        (binaryAction T H e g)) = ⊤ := by
  let ρ := binaryAction T H e
  let W := ⨆ g : SL(2,F),
    (fixedSpace ρ (R.mapSurjective (f := e.toMonoidHom) e.surjective)).map (ρ g)
  let P₀ : Subgroup (omegaClosure T H) := W.toAddSubgroup.toSubgroup'
  let P := P₀.map (omegaClosure T H).subtype
  have hseed : omegaClosure T H ⊓ centralizer (A : Set G) ≤ P := by
    intro v hv
    refine ⟨⟨v,hv.1⟩,?_,rfl⟩
    exact le_iSup_maps ρ _ ((sylow_fixed_iff e R A hAH hR _).mpr hv.2)
  have hnorm : outsideResidual H ≤ normalizer (P : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk v hv
    obtain ⟨v,hv,rfl⟩ := hv
    refine ⟨residualAction T H ⟨k,hk⟩ v,?_,rfl⟩
    have he := (iSup_maps_invariant ρ _ (mem_top (e (residualProjection T H ⟨k,hk⟩)))
      (Additive.ofMul v)).2 hv
    change binaryAction T H e (e (residualProjection T H ⟨k,hk⟩))
      (Additive.ofMul v) ∈ W at he
    change Additive.ofMul (residualAction T H ⟨k,hk⟩ v) ∈ W
    exact (congrArg Additive.ofMul (binaryAction_residual T H e ⟨k,hk⟩ _)) ▸ he
  have hcover : omegaClosure T H ≤ P := hgen ▸ conjugateSpanBy_le hseed hnorm
  apply top_unique
  intro v _
  obtain ⟨w,hw,he⟩ := hcover v.toMul.property
  have he' : w = v.toMul := Subtype.ext he
  subst w
  exact hw

variable {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Both G.1.6 assumptions, derived from the original source and the one
independent Sylow-image witness. -/
theorem source_fixedSpaceHypotheses
    (s : Hypothesis1131At D S U₁ H)
    (e : residualStar T H ≃* SL(2,S.field.Carrier))
    (R : Sylow 2 (residualStar T H)) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H)) :
    SL2SylowFixedRecognition.FixedSpaceHypotheses (binaryAction T H e)
      (R.mapSurjective (f := e.toMonoidHom) e.surjective) := by
  let A := V.map (MulAut.conj g).toMonoidHom
  have hAH : A ≤ H := hg.trans s.outside.1.1.2
  refine ⟨generated_of_conjugateSpan e R A hAH hR
    (omegaClosure_generated_by_actor_fixed T H s.outside.1.1.2 A hg),?_⟩
  intro r hr hr1
  obtain ⟨b,hb,rfl⟩ := hr
  have hbA : b.val ∈ (A.subgroupOf H).map (starProjection T H) := by
    rw [← hR]
    exact mem_map_of_mem (residualStar T H).subtype hb
  have hb1 : b.val ≠ 1 := by
    intro hz
    have hb0 : b = 1 := Subtype.ext hz
    exact hr1 (by rw [hb0,map_one])
  have hrank : rank ((A.subgroupOf H).map (starProjection T H)) = S.field.degree := by
    rw [← hR]
    exact source_residualStar_sylow_rank s hmodel R
  have hu := selected_star_uniform_fixed_of_rank s g hg hs hrank b hbA hb1
  ext v
  rw [mem_fixedSpace_zpowers_iff, sylow_fixed_iff e R A hAH hR]
  change binaryAction T H e (e b) v = v ↔ _
  change (binaryAction T H e (e b) v).toMul = v.toMul ↔ _
  rw [binaryAction_equiv]
  rw [← MulAut.mem_fixedSubgroup,hu]
  rfl

end NaturalRecognition
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

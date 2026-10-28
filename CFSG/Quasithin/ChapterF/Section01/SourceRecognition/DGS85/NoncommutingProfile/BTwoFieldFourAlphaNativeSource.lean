module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourAlphaActionSource
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.BorelRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoParabolics

/-!
# The source alpha endpoint and the native J₂ second parabolic

Both actual groups are the proved root-normalizer model. Their comparison
can be aligned on the actual Sylow subgroup by conjugacy; its full Borel
then agrees with the native Sylow normalizer by containment and order.
Restricting this same endpoint map retains the core, Borel and Sylow
inclusion squares. The first endpoint was constructed independently, so
agreement of its Borel restriction with this one remains an amalgam
compatibility obligation.

Source: DGS, *Groups and Graphs* (1985), (10.9), pp.162–163.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open Theory.GroupTheory
open SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourAlphaNativeAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2


local notation "Jα" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.p₂
local notation "JQ" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.q₂
local notation "JS" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.s
local notation "JB" => Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap.B

/-- The whole reduced alpha endpoint, together with its actual Borel, Sylow
and intrinsic core, identifies with the native second J₂ parabolic. -/
theorem original_bTwo_field_four_reduced_alpha_borel_equiv
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    let T := (commonBorel L S).pCoreIn 2
    ∃ (f : P₀ L S 0 ≃* Jα) (fB : B₀ L S ≃* JB)
      (fT : T ≃* JS) (fQ : pCore 2 (P₀ L S 0) ≃* JQ),
      (∀ b : B₀ L S, (fB b : Sporadic.LeechRelated.J2.Carrier) =
        (f (inclusion le_sup_right b) : Sporadic.LeechRelated.J2.Carrier)) ∧
      (∀ t : T, (fT t : Sporadic.LeechRelated.J2.Carrier) =
        (f (inclusion (le_sup_right.trans le_sup_right) t) : Sporadic.LeechRelated.J2.Carrier)) ∧
      ∀ q : pCore 2 (P₀ L S 0), (fQ q : Sporadic.LeechRelated.J2.Carrier) =
        (f (q : P₀ L S 0) : Sporadic.LeechRelated.J2.Carrier) := by
  let P := P₀ L S 0
  let T := (commonBorel L S).pCoreIn 2
  have hTP : T ≤ P := le_sup_right.trans le_sup_right
  obtain ⟨f₀,d₀,hf₀⟩ := original_bTwo_field_four_alpha_model
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨j,dj,hj⟩ := Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.RootCoordinates.exists_model_equiv
  let e₀ : P ≃* Jα := f₀.trans j.symm
  let : Finite P := Finite.of_injective e₀ e₀.injective
  obtain ⟨fβ,fBβ,fTβ,hfBβ,hfTβ,dβ,hdβ⟩ := original_bTwo_field_four_reduced_beta_borel_equiv
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hT : Nat.card (T.subgroupOf P) = 128 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTP).toEquiv,
      Nat.card_congr fTβ.toEquiv]
    exact Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.card_s
  have hB : Nat.card ((B₀ L S).subgroupOf P) = 384 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show B₀ L S ≤ P from le_sup_right)).toEquiv,
      Nat.card_congr fBβ.toEquiv]
    exact Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap.card_B
  have hnorm : commonBorel L S ≤ normalizer (T : Set G) :=
    (commonBorel L S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (commonBorel L S)))
  have hn : (B₀ L S).subgroupOf P ≤ normalizer (T.subgroupOf P : Set P) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro t
    change (t : G) ∈ T ↔ (x : G) * (t : G) * (x : G)⁻¹ ∈ T
    exact mem_normalizer_iff.mp (hnorm (B₀_le h hx)) (t : G)
  obtain ⟨f,hfT,hfB,gT,gB,hgT,hgB⟩ :=
    Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.exists_borel_aligned_equiv
      e₀ (T.subgroupOf P) ((B₀ L S).subgroupOf P) hT hB hn
  let fT := (subgroupOfEquivOfLe hTP).symm.trans
    (gT.trans (subgroupOfEquivOfLe
      Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.s_le_p₂))
  let fB := (subgroupOfEquivOfLe (show B₀ L S ≤ P from le_sup_right)).symm.trans
    (gB.trans (subgroupOfEquivOfLe
      Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap.B_le_p₂))
  have hcore : pCore 2 Jα = (JQ).subgroupOf Jα :=
    Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.p₂_core_eq_q₂
      Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.l₂_core_card
  let fQ := (LocalCoreTransport.coreEquiv 2 f).trans
    ((MulEquiv.subgroupCongr hcore).trans
      (subgroupOfEquivOfLe (show JQ ≤ Jα from (JQ).le_normalizer)))
  refine ⟨f,fB,fT,fQ,?_,?_,?_⟩
  · intro b
    change ((gB ((subgroupOfEquivOfLe (show B₀ L S ≤ P from le_sup_right)).symm b) : Jα) :
      Sporadic.LeechRelated.J2.Carrier) = _
    rw [hgB]
    rfl
  · intro t
    change ((gT ((subgroupOfEquivOfLe hTP).symm t) : Jα) :
      Sporadic.LeechRelated.J2.Carrier) = _
    rw [hgT]
    rfl
  · intro q
    change (((LocalCoreTransport.coreEquiv 2 f q) : Jα) :
      Sporadic.LeechRelated.J2.Carrier) = _
    rw [LocalCoreTransport.coreEquiv_apply]


/-- Both reduced endpoint groups and the whole reduced Borel identify with
the concrete J₂ parabolics in their source orientation. -/
theorem original_bTwo_field_four_reduced_parabolic_equiv
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    Nonempty (RankTwoAmalgam.ParabolicEquiv
      (OriginalExtension.reducedAmalgam L S).reverse
      GreenBook.HallJanko.j2Model.toMarking.amalgam) := by
  obtain ⟨fα,fBα,fTα,fQα,hBα,hTα,hQα⟩ :=
    original_bTwo_field_four_reduced_alpha_borel_equiv
      h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨fβ,fBβ,fTβ,hBβ,hTβ,dβ,hdβ⟩ :=
    original_bTwo_field_four_reduced_beta_borel_equiv
      h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  exact ⟨{
    left := ((MulEquiv.subgroupCongr (P₀_eq_source h 1).symm).trans fβ).trans
      (MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_P_zero.symm)
    middle := ((MulEquiv.subgroupCongr (B₀_eq_source h).symm).trans fBβ).trans
      (MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_B.symm)
    right := ((MulEquiv.subgroupCongr (P₀_eq_source h 0).symm).trans fα).trans
      (MulEquiv.subgroupCongr GreenBook.HallJanko.j2Model_P_one.symm) }⟩

/-- The original inner case is restored; a remaining outer case has the
actual doubled Sylow and Borel orders. -/
theorem original_bTwo_field_four_parabolic_models_or_outer_sizes
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    (GreenBook.ExceptionalModels.ParabolicModel .j2 (OriginalExtension.originalAmalgam L S) ∨
      GreenBook.ExceptionalModels.ParabolicModel .j2 (OriginalExtension.originalAmalgam L S).reverse) ∨
    (Nat.card S = 256 ∧ Nat.card (commonBorel L S) = 768) := by
  apply OriginalExtension.JankoTwo.original_parabolicModels_or_outer_sizes h
  exact Or.inr (original_bTwo_field_four_reduced_parabolic_equiv
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction

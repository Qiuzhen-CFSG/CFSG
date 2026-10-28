module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.LocalGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.TripleHeptad
public import Theory.GroupTheory.Recognition.QuasithinM23.ParabolicOvergroups
public import Theory.SpecificGroups.PSL3.BorelTwoParabolics

/-!
# The original linear factors and their overgroups

Transport maximality and order from the recognized PSL₃(4) completion to the
literal source parabolics. The second theorem records all overgroups of the
left factor inside the original Sylow completion, as used in 5.2.20.
Source: Aschbacher--Smith 5.2.16 and 5.2.20, printed pp.655--656.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Matrix.PSL3.LinearThree

theorem Preparation.linear_nonmaximal_parabolic_eq
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∀ i : Fin 2, ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i =
      ![L,residual H] i := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  have hfour := (d.linear_nonmaximal_core_geometry h hH hp E hm hE he hnonmax).2.2.1
  obtain ⟨c,hc,_⟩ := M23Completion.native_completion P Q E hfour he
  have hP : Group.IsPerfect P := by
    rcases hc with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · let := c.left_isPerfect
      let a := (MulEquiv.subgroupCongr hl).trans (subgroupOfEquivOfLe (show P ≤ P ⊔ Q from le_sup_left))
      exact Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
    · let := c.right_isPerfect
      let a := (MulEquiv.subgroupCongr hr).trans (subgroupOfEquivOfLe (show P ≤ P ⊔ Q from le_sup_left))
      exact Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  have hQ : Group.IsPerfect Q := by
    rcases hc with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · let := c.right_isPerfect
      let a := (MulEquiv.subgroupCongr hr).trans (subgroupOfEquivOfLe (show Q ≤ P ⊔ Q from le_sup_right))
      exact Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
    · let := c.left_isPerfect
      let a := (MulEquiv.subgroupCongr hl).trans (subgroupOfEquivOfLe (show Q ≤ P ⊔ Q from le_sup_right))
      exact Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  intro i
  have hi := d.parabolic_residuals h hH.1.1.2 hp i
  let : Group.IsPerfect (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i) := by
    fin_cases i
    · exact hP
    · exact hQ
  rwa [solvableResidual_eq_top,←MonoidHom.range_eq_map,range_subtype] at hi


/-- The original factors themselves are the maximal parabolics of the completion. -/
theorem Preparation.linear_nonmaximal_factor_geometry
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    IsCoatom (L.subgroupOf (L ⊔ residual H)) ∧
    IsCoatom ((residual H).subgroupOf (L ⊔ residual H)) ∧
    Nat.card L = 960 ∧ Nat.card (residual H) = 960 ∧
    Nat.card (L ⊔ residual H : Subgroup G) = 20160 := by
  have hP := d.linear_nonmaximal_parabolic_eq h hH hp E hm hE he hnonmax 0
  have hQ := d.linear_nonmaximal_parabolic_eq h hH hp E hm hE he hnonmax 1
  change ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 = L at hP
  change ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 = residual H at hQ
  have hex := d.linear_nonmaximal_generated_equiv h hH hp E hm hE he hnonmax
  dsimp only at hex
  rw [hP,hQ] at hex
  obtain ⟨e,hmark,_⟩ := hex
  have hmax := projective_parabolics_isCoatom Matrix.PSL3Four.F
  have hcard (b : Bool) : Nat.card (Matrix.PSL3.RootPlaneGeometry.parabolic Matrix.PSL3Four.F b) = 960 := by
    have hh := Matrix.PSL3Four.FullPlaneNormalizer.parabolic_card
      (MonoidHom.id Matrix.PSL3Four.PSL) Function.surjective_id b
    simpa using hh
  have hc (U : Subgroup G) (hU : U ≤ L ⊔ residual H) :
      Nat.card ((U.subgroupOf (L ⊔ residual H)).map e.toMonoidHom) = Nat.card U := by
    rw [card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hU).toEquiv]
  refine ⟨?_,?_,?_,?_,(Nat.card_congr e.toEquiv).trans Matrix.PSL3Four.card_PSL⟩
  · apply (e.mapSubgroup.isCoatom_iff _).mp
    rcases hmark with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · change IsCoatom ((L.subgroupOf (L ⊔ residual H)).map e.toMonoidHom)
      rw [hl]; exact hmax.1
    · change IsCoatom ((L.subgroupOf (L ⊔ residual H)).map e.toMonoidHom)
      rw [hr]; exact hmax.2
  · apply (e.mapSubgroup.isCoatom_iff _).mp
    rcases hmark with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · change IsCoatom (((residual H).subgroupOf (L ⊔ residual H)).map e.toMonoidHom)
      rw [hr]; exact hmax.2
    · change IsCoatom (((residual H).subgroupOf (L ⊔ residual H)).map e.toMonoidHom)
      rw [hl]; exact hmax.1
  · rw [←hc L le_sup_left]
    rcases hmark with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · rw [hl]; exact hcard true
    · rw [hr]; exact hcard false
  · rw [←hc (residual H) le_sup_right]
    rcases hmark with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · rw [hr]; exact hcard false
    · rw [hl]; exact hcard true

theorem Preparation.linear_nonmaximal_overgroup_alternatives
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∀ R : Subgroup G, L ≤ R → R ≤ L ⊔ H →
      R = L ∨ R = L ⊔ (T : Subgroup G) ∨ L ⊔ residual H ≤ R := by
  have hP := d.linear_nonmaximal_parabolic_eq h hH hp E hm hE he hnonmax
  have hC : ChapterF.Source.generated ![L,residual H] (sourceS L H) = L ⊔ residual H := by
    rw [←ChapterF.Source.parabolics_generate,hP 0,hP 1]
    rfl
  have hgeom := d.linear_nonmaximal_factor_geometry h hH hp E hm hE he hnonmax
  have hCT := (d.linear_nonmaximal_extension_geometry h hH hp E hm hE he hnonmax).1
  change ChapterF.Source.generated ![L,residual H] (sourceS L H) ⊓ (T : Subgroup G) = _ at hCT
  rw [hC] at hCT
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hSL : sourceS L H ≤ L := d.linear_sourceS_le_factors h hH.1.1.2 hp E hm hE he 0
  have hLT : L ⊓ (T : Subgroup G) = sourceS L H :=
    le_antisymm ((inf_le_inf_right _ le_sup_left).trans_eq hCT) (le_inf hSL hST)
  have hi : L.relIndex (L ⊔ (T : Subgroup G)) = 2 := by
    obtain ⟨_,_,_,_,_,_,_,hT,hS,_⟩ :=
      d.linear_nonmaximal_core_geometry h hH hp E hm hE he hnonmax
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes L (T : Subgroup G) h.sylow_normalizes
    rw [hgeom.2.2.1,hT,hLT,hS] at hc
    have hj := relIndex_mul_relIndex (⊥ : Subgroup G) L (L ⊔ (T : Subgroup G)) bot_le le_sup_left
    simp only [relIndex_bot_left] at hj
    rw [hgeom.2.2.1] at hj
    omega
  have hn : (T : Subgroup G) ≤ normalizer ((L ⊔ residual H : Subgroup G) : Set G) := by
    rw [←hC]
    exact residual_completion_sylow_normalizes h.sylow_normalizes hH.1.1.2
  have hx : (L ⊔ residual H) ⊔ (T : Subgroup G) = L ⊔ H := by
    rw [sup_assoc,residual_sup_sylow T H hH.1.1.2]
  intro R hLR hRX
  exact QuasithinM23.parabolic_overgroup_alternatives L (L ⊔ residual H) (T : Subgroup G)
    le_sup_left hgeom.1 h.sylow_normalizes hn
    (fun hh => d.right_outside (le_sup_right.trans hh)) hi R hLR (hx.symm ▸ hRX)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Suzuki.Complete
public import Theory.SpecificGroups.PSL2.OrdinaryBorelGeometry

/-!
# Ordinary linear Borels and the odd-degree rank-one exclusion

The literal PSL₂ Borel is two-perfect, and its centralizer inside the source
Sylow centralizes the component, without assuming component normality. For
odd field degree the two-group action is inner. Elementary replacement then
puts J(S) in the component normalizer even when S exchanges components.
The model Borel normalizes J(S), so original Thompson control and the residual
intersection argument give the required contradiction. Even field degree,
including the exceptional L₂(4) actor, remains with the rank-one owner.

Source: Aschbacher--Smith 15.1.21(i), printed pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
variable {F : Type} [Field F] [Finite F] {n : ℕ}

/-- Two-perfectness of the actual rank-one linear Borel. -/
theorem PreExclusionSource.rankOne_linear_borel_twoPerfect
    (s : d.PreExclusionSource h.normalized p)
    (hn : 2 ≤ n) (hF : Nat.card F=2^n) (e : d.L ≃* PSL(2,F)) :
    IsPPerfect 2 d.ordinaryBorel := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L)=d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  let Q := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let B := normalizer (P : Set d.L)
  have hBQ : B.map e.toMonoidHom = normalizer (Q : Set PSL(2,F)) :=
    map_equiv_normalizer_eq (P : Subgroup d.L) e
  let eB : B ≃* normalizer (Q : Set PSL(2,F)) :=
    (e.subgroupMap B).trans (MulEquiv.subgroupCongr hBQ)
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact (by decide : 4=2^2) ▸ Nat.pow_le_pow_right (by decide) hn
  have hb : IsPPerfect 2 B := (Theory.PSL2.OrdinaryBorel.normalizer_twoPerfect hq Q).of_surjective
    eB.symm.toMonoidHom eB.symm.surjective
  have hBG : B.map d.L.subtype = d.ordinaryBorel := by
    change (normalizer ((P : Subgroup d.L) : Set d.L)).map _ = _
    rw [hP']
    rfl
  rw [←hBG]
  exact hb.of_surjective (d.L.subtype.subgroupMap B) (d.L.subtype.subgroupMap_surjective B)

/-- The model centralizer comparison retains relative component normality. -/
theorem PreExclusionSource.rankOne_linear_borel_centralizers
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hn : 2 ≤ n) (hF : Nat.card F=2^n) (e : d.L ≃* PSL(2,F)) :
    d.S ⊓ centralizer (d.ordinaryBorel : Set G) ≤ d.S ⊓ centralizer (d.L : Set G) := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L)=d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  have hBG : (normalizer (P : Set d.L)).map d.L.subtype = d.ordinaryBorel := by
    change (normalizer ((P : Subgroup d.L) : Set d.L)).map _ = _
    rw [hP']
    rfl
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by decide : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) (by omega)
  have hc := Theory.PSL2.OrdinaryBorel.relative_centralizer d.G1 d.L d.L_component.1 hL hF hq e P
  rw [hBG] at hc
  exact le_inf inf_le_left ((le_inf (inf_le_left.trans d.S_le_G1) inf_le_right).trans hc)

/-- Odd field degree supplies the required normalization of the original J(S). -/
theorem PreExclusionSource.rankOne_linear_borel_thompson_of_odd
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hn : 2 ≤ n) (ho : Odd n) (hF : Nat.card F=2^n) (e : d.L ≃* PSL(2,F)) :
    d.ordinaryBorel ≤ normalizer (elementaryAbelianMaxJ d.S : Set G) := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L)=d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by decide : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) (by omega)
  have hj := Theory.PSL2.OrdinaryBorel.component_normalizer_thompson_of_odd
    d.G1 d.L d.S d.L_component.1 d.S_le_G1 hL (T.isPGroup'.to_le d.S_le_T)
    (s.ordinary_normalizer_relIndex_le_two (h := h) hG hL) P (hP ▸ d.SL_le_S) ho hF hq e
  change (normalizer ((P : Subgroup d.L) : Set d.L)).map d.L.subtype ≤ _ at hj
  rw [hP'] at hj
  exact hj

/-- The full odd-degree linear constructor is impossible, with its literal Borel clause. -/
theorem PreExclusionSource.false_of_rankOne_linear_odd
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hn : 2 ≤ n) (ho : Odd n) (hm : ClassicalGroup.IsPSL d.L 2 (2^n))
    (hB : d.ML=d.ordinaryBorel) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact s.no_thompson_borel (h := h) hG hM hJ
    (s.rankOne_linear_borel_twoPerfect (h := h) hn hF e) (hB ▸ d.ML_le_MZ)
    (s.rankOne_linear_borel_thompson_of_odd (h := h) hG hL hn ho hF e)
    (s.rankOne_linear_borel_centralizers (h := h) hL hn hF e)

/-- After the completed exclusions, the linear parameter is even or the model is unitary. -/
theorem PreExclusionSource.rankOne_after_suzuki_and_odd_linear
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hmodel : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (hB : d.ML=d.ordinaryBorel) :
    (∃ f : ℕ, 2 ≤ f ∧ Even f ∧ ClassicalGroup.IsPSL d.L 2 (2^f)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSU d.L 3 (2^f)) := by
  rcases s.rankOne_after_all_suzuki (h := h) hG hM hJ hu hL hmodel hB with ⟨f,hf,hm⟩ | hm
  · refine Or.inl ⟨f,hf,?_,hm⟩
    rcases Nat.even_or_odd f with he | ho
    · exact he
    · exact (s.false_of_rankOne_linear_odd (h := h) hG hM hJ hL hf ho hm hB).elim
  · exact Or.inr hm

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

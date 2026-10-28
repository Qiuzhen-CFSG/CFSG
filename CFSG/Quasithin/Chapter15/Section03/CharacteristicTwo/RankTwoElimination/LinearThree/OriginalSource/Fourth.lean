module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Inheritance
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Sylow
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Survivors
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Reapplying the MS theorem to the genuine Sylow overgroup

After the residual argument proves that S normalizes L and moves V through
Y_L, 15.3.11(12) supplies the characteristic-subgroup condition for (LS,S).
The subgroup LS inherits SQTK and characteristic two from I. Its Sylow
subgroup is the original S, and S itself witnesses the odd-index radical
condition. Thus C.1.34 can be applied anew in LS, where the central-four
alternative contradicts the original bound on Ω₁(Z(S)).

Every surviving alternative is transported to its ambient module marking.
The downstream moving-plane argument excludes the fifth alternative.
No equality between S and the Sylow subgroup of LR is used.

Source: Aschbacher–Smith, 15.3.11(12), 15.3.23, printed pp.1123–1124 and
1128; C.1.31–34, printed pp.135–137. The full earlier C.1.34 implication
remains explicit; its universal source producer belongs to Chapter C.
-/

public section

open Subgroup
open scoped Pointwise
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.SourceCases
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.Fourth

universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The original component remains a component after adjoining the source Sylow. -/
theorem component_in_join (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hSI : d.S ≤ I) :
    (c.L.subgroupOf (c.L ⊔ d.S)).IsCComponent := by
  have hJI : c.L ⊔ d.S ≤ I := sup_le (component_le c) hSI
  have hLJ : c.L.subgroupOf I ≤ (c.L ⊔ d.S).subgroupOf I :=
    fun _ hx => mem_sup_left hx
  have hc := ((component_in_overgroup d c).subgroupOf hLJ).map_equiv
    (subgroupOfEquivOfLe hJI)
  convert hc using 1
  ext x
  simp only [mem_subgroupOf, mem_map_equiv]
  rfl

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) (hC : C.Characteristic) :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let b : MulAut A := e.trans (a.trans e.symm)
  exact ⟨b y, (characteristic_iff_le_comap.mp hC b) hy, e.apply_symm_apply _⟩

/-- Construct all binary MS hypotheses in LS from the original Sylow and
characteristic-subgroup conclusions. The quotient marking is transported
through the literal inclusion of L. -/
noncomputable def sylowInput (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) {κ : GroupClass.{u}}
    (hSQTK : IsSQTK κ I) (hf : HasCharacteristicTwo I)
    (hS : Chapter1.IsSylowIn 2 d.S I)
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (h11 : ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
      ¬ ((C.map d.S.subtype).subgroupOf (c.L ⊔ d.S)).Normal)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ChapterC.BinaryMS.Input κ (c.L.subgroupOf (c.L ⊔ d.S))
      (d.S.subgroupOf (c.L ⊔ d.S)) := by
  let J := c.L ⊔ d.S
  let K := c.L.subgroupOf J
  let R := d.S.subgroupOf J
  have hSI : d.S ≤ I := (Chapter1.isSylowIn_iff.mp hS).2.1
  have hJI : J ≤ I := sup_le (component_le c) hSI
  have hSyl : Chapter1.IsSylowIn 2 d.S J := hS.restrict le_sup_right hJI
  have hc : K.IsCComponent := component_in_join d c hSI
  refine {
    sqtk := ?_
    fitting := characteristicTwo_of_sylow_overgroup hS hJI le_sup_right hf
    component := hc
    product := ?_
    radical := ?_
    characteristic := ?_
    quotientEquiv := (quotientComparison (show c.L ≤ J from le_sup_left)).trans e }
  · let f := inclusion hJI
    exact ⟨hSQTK.stronglyQuasithin.of_injective f (inclusion_injective hJI),
      hSQTK.isKGroup.of_injective f (inclusion_injective hJI)⟩
  · intro j
    have hj : (j : G) ∈ (c.L : Set G) * (d.S : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hSL]
      exact j.property
    obtain ⟨l, hl, r, hr, he⟩ := hj
    exact ⟨⟨l, mem_sup_left hl⟩, hl, ⟨r, mem_sup_right hr⟩, hr, Subtype.ext he⟩
  · obtain ⟨P, hP⟩ := hSyl
    change ChapterC.MSOddIndexRadical R
    have he : R = (P : Subgroup J) := by
      apply map_injective J.subtype_injective
      exact (map_subgroupOf_eq_of_le le_sup_right).trans hP.symm
    rw [he]
    have hne : (P : Subgroup J) ≠ ⊤ := by
      intro ht
      have hp : IsPGroup 2 K := P.isPGroup'.to_le (by rw [ht]; exact le_top)
      let := hp.isNilpotent
      exact hc.not_isSolvable inferInstance
    refine ⟨P, lt_top_iff_ne_top.mpr hne, ?_, ?_⟩
    · exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using P.not_dvd_index)
    · have ht : pCore 2 (P : Subgroup J) = ⊤ := by
        apply top_unique
        exact le_sSup ⟨inferInstance, P.isPGroup'.to_subgroup ⊤⟩
      rw [ht, ← MonoidHom.range_eq_map, range_subtype]
  · intro C hC hne hn
    let eR : R ≃* d.S := subgroupOfEquivOfLe le_sup_right
    let D : Subgroup d.S := C.map eR.toMonoidHom
    have hD : D.Characteristic := characteristic_map_equiv eR C hC
    have hDne : D ≠ ⊥ := fun hz =>
      hne ((map_eq_bot_iff_of_injective C eR.injective).mp hz)
    have he : (D.map d.S.subtype).subgroupOf J = C.map R.subtype := by
      apply map_injective J.subtype_injective
      rw [map_subgroupOf_eq_of_le (show D.map d.S.subtype ≤ J from
        (map_subtype_le D).trans le_sup_right), map_map, map_map]
      rfl
    exact h11 D hD hDne (he.symm ▸ hn)

private theorem input_sourcePair {D : Type u} [Group D] [Finite D]
    {κ : GroupClass.{u}} {K R : Subgroup D} (b : ChapterC.BinaryMS.Input κ K R) :
    MSPair κ D K R := by
  refine ⟨inferInstance, b.sqtk, b.fitting, b.product, b.component, ?_,
    Or.inl b.radical, b.characteristic⟩
  apply RankTwoDerived.linear (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) 1 (by decide)
  · exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
      ⟨(BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)).symm⟩⟩
  · exact ⟨b.derivedQuotientEquiv⟩

/-- The full source theorem supplies the binary classifier for any literal
binary MS input and any indicated Sylow subgroup containing its radical. -/
theorem binary_classification_of_universal {D : Type u} [Group D] [Finite D]
    {κ : GroupClass.{u}} {L R : Subgroup D}
    (classification : UniversalClassification.{u}) (b : ChapterC.BinaryMS.Input κ L R)
    (P : Sylow 2 D) (hRP : R ≤ (P : Subgroup D)) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Alternatives (ZMod 2) 1 L R P e :=
  classification κ D L R (input_sourcePair b)
    (ZMod 2) 1 (by decide) (by simp) ⟨b.quotientEquiv⟩ P hRP

/-- Apply C.1.34 in LS, where the source Sylow is the original S, and
retain every surviving clause and its compatible ambient module marking.
The moving-plane argument can subsequently exclude the fifth case. -/
theorem source_cases_of_sylow_classification (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) {κ : GroupClass.{u}}
    (classification : ChapterC.BinaryMS.Input κ
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)) →
      ∀ P : Sylow 2 (c.L ⊔ d.S : Subgroup G),
        d.S.subgroupOf (c.L ⊔ d.S) ≤ (P : Subgroup (c.L ⊔ d.S : Subgroup G)) →
        ∃ e' : ((c.L.subgroupOf (c.L ⊔ d.S)) ⧸
          pCore 2 (c.L.subgroupOf (c.L ⊔ d.S))) ≃*
            Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
          Alternatives (ZMod 2) 1 (c.L.subgroupOf (c.L ⊔ d.S))
            (d.S.subgroupOf (c.L ⊔ d.S)) P e')
    (hSQTK : IsSQTK κ I) (hf : HasCharacteristicTwo I)
    (hS : Chapter1.IsSylowIn 2 d.S I)
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (h11 : ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
      ¬ ((C.map d.S.subtype).subgroupOf (c.L ⊔ d.S)).Normal)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4) :
    ∃ P : Sylow 2 (c.L ⊔ d.S : Subgroup G),
      (P : Subgroup (c.L ⊔ d.S : Subgroup G)).map (c.L ⊔ d.S).subtype = d.S ∧
      ∃ e' : ((c.L.subgroupOf (c.L ⊔ d.S)) ⧸ pCore 2 (c.L.subgroupOf (c.L ⊔ d.S))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        (FirstThreeCases (c.L.subgroupOf (c.L ⊔ d.S))
          (d.S.subgroupOf (c.L ⊔ d.S)) P e' ∨
        FifthCase (c.L.subgroupOf (c.L ⊔ d.S))
          (d.S.subgroupOf (c.L ⊔ d.S)) P e') ∧
        AmbientCases (show c.L ≤ c.L ⊔ d.S from le_sup_left)
          (d.S.subgroupOf (c.L ⊔ d.S)) P e' := by
  let J := c.L ⊔ d.S
  let b := sylowInput d c hSQTK hf hS hSL h11 e
  have hJI : J ≤ I := sup_le (component_le c) (Chapter1.isSylowIn_iff.mp hS).2.1
  obtain ⟨P, hP⟩ := hS.restrict (show d.S ≤ J from le_sup_right) hJI
  have hRP : d.S.subgroupOf J ≤ (P : Subgroup J) := by
    intro s hs
    have hm : (s : G) ∈ (P : Subgroup J).map J.subtype := hP.symm ▸ hs
    obtain ⟨t, ht, he⟩ := hm
    exact (Subtype.ext he : t = s) ▸ ht
  obtain ⟨e', ha⟩ := classification b P hRP
  let := b.component_normal
  have hr := local_centralOmega_rank_le_two d J P hP hindex hZ hZS
  have hs := alternatives_without_four P hr ha
  exact ⟨P, hP, e', hs, ambientCases_of_survivors le_sup_left b.component hs⟩

/-- The universal C.1.34 source theorem specializes to the actual LS input. -/
theorem source_cases_of_sylow_source (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) {κ : GroupClass.{u}}
    (classification : UniversalClassification.{u})
    (hSQTK : IsSQTK κ I) (hf : HasCharacteristicTwo I)
    (hS : Chapter1.IsSylowIn 2 d.S I)
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (h11 : ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
      ¬ ((C.map d.S.subtype).subgroupOf (c.L ⊔ d.S)).Normal)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4) :
    ∃ P : Sylow 2 (c.L ⊔ d.S : Subgroup G),
      (P : Subgroup (c.L ⊔ d.S : Subgroup G)).map (c.L ⊔ d.S).subtype = d.S ∧
      ∃ e' : ((c.L.subgroupOf (c.L ⊔ d.S)) ⧸ pCore 2 (c.L.subgroupOf (c.L ⊔ d.S))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        (FirstThreeCases (c.L.subgroupOf (c.L ⊔ d.S))
          (d.S.subgroupOf (c.L ⊔ d.S)) P e' ∨
        FifthCase (c.L.subgroupOf (c.L ⊔ d.S))
          (d.S.subgroupOf (c.L ⊔ d.S)) P e') ∧
        AmbientCases (show c.L ≤ c.L ⊔ d.S from le_sup_left)
          (d.S.subgroupOf (c.L ⊔ d.S)) P e' := by
  exact source_cases_of_sylow_classification d c
    (fun b P hRP => binary_classification_of_universal classification b P hRP)
    hSQTK hf hS hSL h11 e hindex hZ hZS

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.Fourth

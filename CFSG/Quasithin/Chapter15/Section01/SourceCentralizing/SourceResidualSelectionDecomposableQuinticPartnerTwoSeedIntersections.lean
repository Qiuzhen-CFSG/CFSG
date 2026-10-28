module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoCanonicalAction

/-!
# The canonical denominator and the original marked planes

Sylow exchange forces equal proper intersections with the two original
Thompson planes. Their literal quotient images retain the original join.
In the three-dimensional case the denominator meets E exactly in the
order-two partner module, and the two image planes meet in a line.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem section_image_sup
    {H F D A B : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} (dF : BinaryConjugationSection H F D ρ)
    (hAF : A ≤ F) (hBF : B ≤ F) :
    dF.imageSpace (A ⊔ B) = dF.imageSpace A ⊔ dF.imageSpace B := by
  let o : Subgroup (Multiplicative W) ≃o Submodule (ZMod 2) W :=
    Subgroup.toAddSubgroup'.trans (AddSubgroup.toZModSubmodule 2)
  change o (((A ⊔ B).subgroupOf F).map dF.coordinates) =
    o ((A.subgroupOf F).map dF.coordinates) ⊔ o ((B.subgroupOf F).map dF.coordinates)
  rw [subgroupOf_sup hAF hBF,Subgroup.map_sup,o.map_sup]

/-- Literal canonical intersections and their dimensions in any supplied
coordinates on the same F/D section. The dimension-three alternative keeps
both original marked planes and their intersection line. -/
theorem PreparedChosenModule.decomposable_five_partner_two_seed_intersections
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
      V ≤ Mc.pCoreIn 2 ∨
        (Nat.card (D ⊓ Z₁ : Subgroup G) = Nat.card (D ⊓ Z₂ : Subgroup G) ∧
          (Nat.card (D ⊓ Z₁ : Subgroup G) = 1 ∨ Nat.card (D ⊓ Z₁ : Subgroup G) = 2) ∧
          (Nat.card (D ⊓ E : Subgroup G) = 2 ∨ Nat.card (D ⊓ E : Subgroup G) = 4 ∨ Nat.card (D ⊓ E : Subgroup G) = 8) ∧
          ∀ {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
            (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
            let P := dF.imageSpace E
            let P₁ := dF.imageSpace Z₁
            let P₂ := dF.imageSpace Z₂
            P = P₁ ⊔ P₂ ∧
              Module.finrank (ZMod 2) P₁ = Module.finrank (ZMod 2) P₂ ∧
              (Module.finrank (ZMod 2) P₁ = 1 ∨ Module.finrank (ZMod 2) P₁ = 2) ∧
              ((D ⊓ E = localModule T Mc ∧ Module.finrank (ZMod 2) P = 3 ∧
                  Module.finrank (ZMod 2) P₁ = 2 ∧
                  Module.finrank (ZMod 2) (P₁ ⊓ P₂ : Submodule (ZMod 2) W) = 1) ∨
                (Nat.card (D ⊓ E : Subgroup G) = 4 ∧ Module.finrank (ZMod 2) P = 2) ∨
                (Nat.card (D ⊓ E : Subgroup G) = 8 ∧ Module.finrank (ZMod 2) P = 1 ∧
                  Module.finrank (ZMod 2) P₁ = 1 ∧ P₁ = P₂))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let Uc := localModule T Mc
  let C := centralizer (Uc : Set G)
  change Nat.card Uc = 2 at hcU
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  rcases h.decomposable_five_partner_two_core_or_canonical_action
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU with
    hcore | ⟨hDF,hUD,_,hnD,_⟩
  · exact Or.inl hcore
  have hUE : Uc ≤ E := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hEF : E ≤ F := le_conjugateSpanBy E C
  have hCMc : C ≤ Mc := localModule_centralizer_le_partner T Mc hu
  have hMcC : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) := hTMc.trans hnD
  let S₀ := (T : Subgroup G) ⊓ normalizer (plane V (c.ambientFactor d s.first).space : Set G)
  have hSne : S₀ ≠ (T : Subgroup G) := by
    intro he
    have hh : S₀.relIndex (T : Subgroup G) = 2 := s.stabilizer_index
    rw [he,relIndex_self] at hh
    omega
  obtain ⟨t,ht,htS⟩ := SetLike.exists_of_lt
    (lt_of_le_of_ne (show S₀ ≤ (T : Subgroup G) from inf_le_left) hSne)
  have hex := s.thompson_exchanges t ht (fun hh => htS ⟨ht,hh⟩)
  have hnotE : ¬E ≤ D := fun hED =>
    hDF.not_ge (conjugateSpanBy_le hED (hCMc.trans hnD))
  have hnot₁ : ¬Z₁ ≤ D := by
    intro hz
    have hm : Z₁.map (MulAut.conj t).toMonoidHom ≤ D :=
      (map_mono hz).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hTD ht))
    rw [hex.1] at hm
    apply hnotE
    change thompsonFixed T V ≤ D
    rw [s.thompson_split]
    exact sup_le hz hm
  have hmap : (D ⊓ Z₁).map (MulAut.conj t).toMonoidHom = D ⊓ Z₂ := by
    have hDm : D.map (MulAut.conj t).toMonoidHom = D :=
      mem_normalizer_iff_map_conj_eq.mp (hTD ht)
    rw [map_inf _ _ _ (MulAut.conj t).injective,hDm,hex.1]
  have hcards : Nat.card (D ⊓ Z₁ : Subgroup G) = Nat.card (D ⊓ Z₂ : Subgroup G) := by
    rw [←hmap,card_map_of_injective (MulAut.conj t).injective]
  have hcZ₁ : Nat.card Z₁ = 4 := s.thompson_card s.first
  have hcZ₂ : Nat.card Z₂ = 4 := s.thompson_card s.second
  have hcE : Nat.card E = 16 := s.fixed_card
  have hc₁ : Nat.card (D ⊓ Z₁ : Subgroup G) = 1 ∨ Nat.card (D ⊓ Z₁ : Subgroup G) = 2 := by
    have hv : Nat.card (D ⊓ Z₁ : Subgroup G) ∣ 4 := hcZ₁ ▸ card_dvd_of_le (show D ⊓ Z₁ ≤ Z₁ from inf_le_right)
    have hh := Nat.mem_divisors.mpr ⟨hv,by decide⟩
    rw [show Nat.divisors 4 = {1,2,4} by decide] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr hh
    · have he : D ⊓ Z₁ = Z₁ := eq_of_le_of_card_ge inf_le_right (by omega)
      exact (hnot₁ (he ▸ inf_le_left)).elim
  have hUI : Uc ≤ D ⊓ E := le_inf hUD hUE
  have hcI : Nat.card (D ⊓ E : Subgroup G) = 2 ∨ Nat.card (D ⊓ E : Subgroup G) = 4 ∨ Nat.card (D ⊓ E : Subgroup G) = 8 := by
    have hv : Nat.card (D ⊓ E : Subgroup G) ∣ 16 := hcE ▸ card_dvd_of_le (show D ⊓ E ≤ E from inf_le_right)
    have hl := card_le_of_le hUI
    have hh := Nat.mem_divisors.mpr ⟨hv,by decide⟩
    rw [show Nat.divisors 16 = {1,2,4,8,16} by decide] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    have hne : Nat.card (D ⊓ E : Subgroup G) ≠ 16 := by
      intro he
      have heq : D ⊓ E = E := eq_of_le_of_card_ge inf_le_right (by omega)
      exact hnotE (heq ▸ inf_le_left)
    change Nat.card Uc = 2 at hcU
    omega
  refine Or.inr ⟨hcards,hc₁,hcI,?_⟩
  intro W _ _ ρ dF
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  let P := dF.imageSpace E
  let P₁ := dF.imageSpace Z₁
  let P₂ := dF.imageSpace Z₂
  have hZ₁E : Z₁ ≤ E := inf_le_right
  have hZ₂E : Z₂ ≤ E := inf_le_right
  have hZ₁F := hZ₁E.trans hEF
  have hZ₂F := hZ₂E.trans hEF
  have hjoin : P = P₁ ⊔ P₂ := by
    have hsplit : E = Z₁ ⊔ Z₂ := s.thompson_split
    exact (congrArg dF.imageSpace hsplit).trans (section_image_sup dF hZ₁F hZ₂F)
  have hm₁ := relIndex_mul_card_of_le (show D ⊓ Z₁ ≤ Z₁ from inf_le_right)
  have hm₂ := relIndex_mul_card_of_le (show D ⊓ Z₂ ≤ Z₂ from inf_le_right)
  have hmE := relIndex_mul_card_of_le (show D ⊓ E ≤ E from inf_le_right)
  rw [inf_relIndex_right,hcZ₁] at hm₁
  rw [inf_relIndex_right,hcZ₂,←hcards] at hm₂
  rw [inf_relIndex_right,hcE] at hmE
  have hdim (B : Subgroup G) (hBF : B ≤ F) (n : ℕ) (hn : D.relIndex B = 2^n) :
      Module.finrank (ZMod 2) (dF.imageSpace B) = n :=
    dF.imageSpace_finrank_of_index B hBF n hn
  have hdimZi : Module.finrank (ZMod 2) P₁ = Module.finrank (ZMod 2) P₂ ∧
      (Module.finrank (ZMod 2) P₁ = 1 ∨ Module.finrank (ZMod 2) P₁ = 2) := by
    rcases hc₁ with hc₁ | hc₁
    · rw [hc₁] at hm₁ hm₂
      have hd₁ : Module.finrank (ZMod 2) P₁ = 2 := hdim Z₁ hZ₁F 2 (by norm_num; omega)
      have hd₂ : Module.finrank (ZMod 2) P₂ = 2 := hdim Z₂ hZ₂F 2 (by norm_num; omega)
      exact ⟨hd₁.trans hd₂.symm,Or.inr hd₁⟩
    · rw [hc₁] at hm₁ hm₂
      have hd₁ : Module.finrank (ZMod 2) P₁ = 1 := hdim Z₁ hZ₁F 1 (by norm_num; omega)
      have hd₂ : Module.finrank (ZMod 2) P₂ = 1 := hdim Z₂ hZ₂F 1 (by norm_num; omega)
      exact ⟨hd₁.trans hd₂.symm,Or.inl hd₁⟩
  refine ⟨hjoin,hdimZi.1,hdimZi.2,?_⟩
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq P₁ P₂
  rw [←hjoin] at hsum
  rcases hcI with hcI | hcI | hcI
  · rw [hcI] at hmE
    have hIE : D ⊓ E = Uc := (eq_of_le_of_card_ge hUI (by omega)).symm
    have hdP : Module.finrank (ZMod 2) P = 3 := hdim E hEF 3 (by norm_num; omega)
    have hd₁ : Module.finrank (ZMod 2) P₁ = 2 := by omega
    have hdI : Module.finrank (ZMod 2) (P₁ ⊓ P₂ : Submodule (ZMod 2) W) = 1 := by omega
    exact Or.inl ⟨hIE,hdP,hd₁,hdI⟩
  · rw [hcI] at hmE
    exact Or.inr (Or.inl ⟨hcI,hdim E hEF 2 (by norm_num; omega)⟩)
  · rw [hcI] at hmE
    have hdP : Module.finrank (ZMod 2) P = 1 := hdim E hEF 1 (by norm_num; omega)
    have hl : Module.finrank (ZMod 2) P₁ ≤ Module.finrank (ZMod 2) P :=
      Submodule.finrank_mono (dF.imageSpace_mono hZ₁E)
    have hd₁ : Module.finrank (ZMod 2) P₁ = 1 := by omega
    have he₁ : P₁ = P := Submodule.eq_of_le_of_finrank_eq
      (dF.imageSpace_mono hZ₁E) (hd₁.trans hdP.symm)
    have he₂ : P₂ = P := Submodule.eq_of_le_of_finrank_eq
      (dF.imageSpace_mono hZ₂E) (hdimZi.1.symm.trans (hd₁.trans hdP.symm))
    exact Or.inr (Or.inr ⟨hcI,hdP,hd₁,he₁.trans he₂.symm⟩)

end CFSG.Quasithin.Chapter15.Section01

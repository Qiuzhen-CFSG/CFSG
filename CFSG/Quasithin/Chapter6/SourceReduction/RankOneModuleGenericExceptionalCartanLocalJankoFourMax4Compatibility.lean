module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.FiveSectionUniqueness
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.A5ResidualMarked
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourFirstExclusion

/-!
# Compatible placement and exclusion of the original max4 Cartan row

Every local A₅ residual normalized by the full Sylow centralizes the same
Sylow-central involution. The first-centralizer quotient calculation then
makes that residual unique. Applying uniqueness to the genuine residual
of the marked max4 A₅ preimage places the original residual in the SAME
max4 as its Sylow. The existing normalization theorem now applies without
an extra residual-containment premise.

Every conjugate max4 is therefore excluded for the escaping actor. The
native source and chosen-module consumers retain all original maps, both
Hall products and the S₅/S₃ markings, leaving only the max1 actor row.
The max1 argument and the remaining source component/module branches are
still obligations of the local Cartan escape theorem.

Source: Aschbacher--Smith A.3.14(10) and 5.1.13, printed pp.49--50,637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Janko4 Janko4.LocalStructure.SymmetricLinear
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup
local notation "C₁" => InvolutionCentralizers.First.centralizer

private theorem first_pair_unique (S : Sylow 2 Model) (B C : Subgroup Model)
    [Group.IsPerfect B] [Group.IsPerfect C]
    (hB : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (hC : (S : Subgroup Model) ≤ normalizer (C : Set Model))
    (eB : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5))
    (eC : C ⧸ pCore 2 C ≃* alternatingGroup (Fin 5))
    (hBC : B ≤ C₁) (hCC : C ≤ C₁) (hSC : (S : Subgroup Model) ≤ C₁) : B = C := by
  let dB := subgroupOfEquivOfLe hBC
  let dC := subgroupOfEquivOfLe hCC
  let : Group.IsPerfect (B.subgroupOf C₁) := Group.IsPerfect.ofSurjective
    (f := dB.symm.toMonoidHom) dB.symm.surjective
  let : Group.IsPerfect (C.subgroupOf C₁) := Group.IsPerfect.ofSurjective
    (f := dC.symm.toMonoidHom) dC.symm.surjective
  have he := InvolutionCentralizers.First.QuotientExtension.five_section_unique
    (S.subtype hSC) (B.subgroupOf C₁) (C.subgroupOf C₁)
    (by rw [←subgroupOf_normalizer_eq hBC]; exact comap_mono hB)
    (by rw [←subgroupOf_normalizer_eq hCC]; exact comap_mono hC)
    ((QuotientGroup.congr _ _ dB (pCore_map_iso 2 dB)).trans eB)
    ((QuotientGroup.congr _ _ dC (pCore_map_iso 2 dC)).trans eC)
  have hh := congrArg (map (C₁).subtype) he
  simpa only [map_subgroupOf_eq_of_le hBC,map_subgroupOf_eq_of_le hCC] using hh

/-- A full J₄ Sylow normalizes at most one local A₅ residual. -/
theorem jankoFour_local_five_unique (S : Sylow 2 Model) (B C : Subgroup Model)
    (hlB : B ∈ ChapterA.Section03.localCComponents S)
    (hlC : C ∈ ChapterA.Section03.localCComponents S)
    (hB : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (hC : (S : Subgroup Model) ≤ normalizer (C : Set Model))
    (heB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (heC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4) : B = C := by
  let Z := (center S).map (S : Subgroup Model).subtype
  have hZ : Nat.card Z = 2 := by
    rw [card_map_of_injective (S : Subgroup Model).subtype_injective,sylow_center_card_two S]
  have hSZ : (S : Subgroup Model) ≤ centralizer (Z : Set Model) := by
    apply le_centralizer_iff.mpr
    change (center S).map (S : Subgroup Model).subtype ≤ _
    rw [map_center_subtype_eq_inf_centralizer]
    exact inf_le_right
  have hCZ := jankoFour_common_line_centralizer S C Z hlC hC heC hZ hSZ
  obtain ⟨g,hBg,hSg,hKg⟩ := jankoFour_common_first_centralizer S B
    (C ⊔ (S : Subgroup Model)) Z hlB hB heB hZ le_sup_right (sup_le hCZ hSZ)
  let a := MulAut.conj g
  let := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients.local_perfect hlB
  let := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients.local_perfect hlC
  let : Group.IsPerfect (B.map a.toMonoidHom) := Group.IsPerfect.map _
  let : Group.IsPerfect (C.map a.toMonoidHom) := Group.IsPerfect.map _
  have mark (R : Subgroup Model) (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
      Nonempty (((R.map a.toMonoidHom) ⧸ pCore 2 (R.map a.toMonoidHom)) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨F,_,_,hF,⟨eF⟩⟩ := he
    let d := a.subgroupMap R
    exact ⟨(QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans
      (eF.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  apply map_injective (f := a.toMonoidHom) a.injective
  exact first_pair_unique (S.mapSurjective (f := a.toMonoidHom) a.surjective)
    (B.map a.toMonoidHom) (C.map a.toMonoidHom)
    ((map_mono hB).trans (B.le_normalizer_map a.toMonoidHom))
    ((map_mono hC).trans (C.le_normalizer_map a.toMonoidHom)) (mark B heB).some (mark C heC).some
    hBg ((map_mono le_sup_left).trans hKg) hSg

/-- The SAME original residual lies in every literal max4 containing its full Sylow. -/
theorem jankoFour_residual_le_max4 (S : Sylow 2 Model) (R : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hS : (S : Subgroup Model) ≤ max4Subgroup) : R ≤ max4Subgroup := by
  let B := a5Residual.map max4Subgroup.subtype
  have hBM : B ≤ max4Subgroup := map_subtype_le _
  have hcomp : (B.subgroupOf max4Subgroup).IsCComponent := by
    change (comap max4Subgroup.subtype (a5Residual.map max4Subgroup.subtype)).IsCComponent
    rw [comap_map_eq, max4Subgroup.subtype.ker_eq_bot max4Subgroup.subtype_injective,sup_bot_eq]
    exact a5Residual_component_and_image.1
  have hlB := ChapterA.Section03.cComponent_mem_localCComponents hcomp hBM hS
  have hnB : max4Subgroup ≤ normalizer (B : Set Model) := by
    apply (normal_subgroupOf_iff_le_normalizer hBM).mp
    change (comap max4Subgroup.subtype (a5Residual.map max4Subgroup.subtype)).Normal
    rw [comap_map_eq,max4Subgroup.subtype.ker_eq_bot max4Subgroup.subtype_injective,sup_bot_eq]
    infer_instance
  let d := max4Subgroup.subtype.subgroupMap a5Residual
  let e : a5Residual ≃* B := MulEquiv.ofBijective d
    ⟨fun x y hh => Subtype.ext (Subtype.ext (congrArg (fun b : B => (b : Model)) hh)),
      max4Subgroup.subtype.subgroupMap_surjective a5Residual⟩
  let eB := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans a5ResidualQuotientEquiv
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := he
  let eR := eF.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  have heR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 := ⟨F,inferInstance,inferInstance,hF,⟨eF⟩⟩
  have heB := heR.of_mulEquiv (eB.trans eR.symm)
  exact (jankoFour_local_five_unique S R B hl hlB hn (hS.trans hnB) heR heB).trans_le hBM

/-- Common Sylow containment now suffices: max4 normalizes the original residual. -/
theorem jankoFour_max4_normalizes (S : Sylow 2 Model) (R : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hS : (S : Subgroup Model) ≤ max4Subgroup) :
    max4Subgroup ≤ normalizer (R : Set Model) := by
  let := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients.local_perfect hl
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := he
  let eR := eF.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  exact max4_normalizes_perfect_five S R eR hn hS
    (jankoFour_residual_le_max4 S R hl hn ⟨F,inferInstance,inferInstance,hF,⟨eF⟩⟩ hS)

/-- No conjugate of max4 contains both an escaping actor and the original full Sylow. -/
theorem jankoFour_no_actor_max4 (S : Sylow 2 Model) (R D : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hout : ¬ D ≤ normalizer (R : Set Model)) (a : MulAut Model)
    (hS : (S : Subgroup Model) ≤ max4Subgroup.map a.toMonoidHom)
    (hD : D ≤ max4Subgroup.map a.toMonoidHom) : False := by
  let f := a.symm
  have hid : f.toMonoidHom.comp a.toMonoidHom = MonoidHom.id Model := by
    ext x
    exact a.symm_apply_apply x
  have hSf : (S : Subgroup Model).map f.toMonoidHom ≤ max4Subgroup := by
    have hh := map_mono (f := f.toMonoidHom) hS
    rwa [map_map,hid,map_id] at hh
  have hDf : D.map f.toMonoidHom ≤ max4Subgroup := by
    have hh := map_mono (f := f.toMonoidHom) hD
    rwa [map_map,hid,map_id] at hh
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]
    infer_instance
  let d := f.subgroupMap R
  let e := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  have hh := hDf.trans (jankoFour_max4_normalizes
    (S.mapSurjective (f := f.toMonoidHom) f.surjective) (R.map f.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom)
    ((map_mono hn).trans (R.le_normalizer_map f.toMonoidHom)) (he.of_mulEquiv e.symm) hSf)
  rw [←map_equiv_normalizer_eq] at hh
  exact hout ((map_le_map_iff_of_injective f.injective).mp hh)

/-- Only the Mathieu max1 row survives for the whole escaping actor. -/
theorem jankoFour_actor_max1 (S : Sylow 2 Model) (R D E : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hout : ¬ D ≤ normalizer (R : Set Model))
    (hp : JankoFourRemainingActorPlacement S ((D ⊔ (S : Subgroup Model)) ⊔ E)) :
    ∃ g : Model, (S : Subgroup Model).map (MulAut.conj g).toMonoidHom =
        Janko4.OuterReduction.OddIndex.twoSubgroup ∧
      ((D ⊔ (S : Subgroup Model)) ⊔ E).map (MulAut.conj g).toMonoidHom ≤
        Janko4.Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four := by
  obtain ⟨g,hS,hmax | hmax⟩ := hp
  · exact ⟨g,hS,hmax⟩
  · exfalso
    let f := MulAut.conj g
    let : Group.IsSolvable f.toMonoidHom.ker := by
      rw [f.toMonoidHom.ker_eq_bot f.injective]
      infer_instance
    let d := f.subgroupMap R
    let e := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
    apply jankoFour_no_actor_max4
      (S.mapSurjective (f := f.toMonoidHom) f.surjective) (R.map f.toMonoidHom) (D.map f.toMonoidHom)
      (Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom)
      ((map_mono hn).trans (R.le_normalizer_map f.toMonoidHom)) (he.of_mulEquiv e.symm)
    · intro hh
      rw [←map_equiv_normalizer_eq] at hh
      exact hout ((map_le_map_iff_of_injective f.injective).mp hh)
    · exact (map_mono (le_sup_right.trans le_sup_left)).trans hmax
    · exact (map_mono (le_sup_left.trans le_sup_left)).trans hmax
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The original native map retains all markings, and its whole escaping actor lies in max1. -/
theorem normal_jankoFour_native_max1
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hRC : residual H ≤ C.map Y.subtype)
    (e : (C ⧸ pCore 2 C) ≃* Janko4.Model) :
    ∃ (f : Y →* Janko4.Model) (S : Sylow 2 Janko4.Model),
      Function.Surjective f ∧
      (∀ x : C, f x = e (QuotientGroup.mk' (pCore 2 C) x)) ∧
      (S : Subgroup Janko4.Model) = ((T : Subgroup G).subgroupOf Y).map f ∧
      let R := ((residual H).subgroupOf Y).map f
      let D := (A.subgroupOf Y).map f
      let E := (B.subgroupOf Y).map f
      R ∈ ChapterA.Section03.localCComponents S ∧
      (S : Subgroup Janko4.Model) ≤ normalizer (R : Set Janko4.Model) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
      Nat.card B = 3 ∧ Nat.card E = 3 ∧ E ≤ R ∧
      IsCyclic D ∧ Odd (Nat.card D) ∧ E ≤ normalizer (D : Set Janko4.Model) ∧
      (D : Set Janko4.Model) * (S : Set Janko4.Model) =
        (S : Set Janko4.Model) * (D : Set Janko4.Model) ∧
      Group.IsSolvable ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) ∧
      (E : Set Janko4.Model) * (S : Set Janko4.Model) =
        (S : Set Janko4.Model) * (E : Set Janko4.Model) ∧
      Nat.card (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) = 3 * 2^21 ∧
      Nat.card (pCore 2 (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) = 2^20 ∧
      Nonempty (((R ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) ⧸
        pCore 2 (R ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) ≃*
        Equiv.Perm (Fin 5)) ∧
      (∃ e₃ : ((E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) ⧸
          pCore 2 (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) ≃*
          Equiv.Perm (Fin 3),
        let N := E ⊔ (S : Subgroup Janko4.Model)
        let q := e₃.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
        Nat.card (((S : Subgroup Janko4.Model).subgroupOf N).map q) = 2 ∧
        Nat.card ((E.subgroupOf N).map q) = 3) ∧
      ¬ D ≤ normalizer (R : Set Janko4.Model) ∧ ¬ D ≤ E ∧
      pCore 2 ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) ≠ ⊥ ∧
      JankoFourWholeActorPlacement S ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E) ∧
      JankoFourSolvableActorPlacement S ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E) ∧
      (∀ g : MulAut Janko4.Model,
        (S : Subgroup Janko4.Model).map g.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup →
        D.map g.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup →
        ¬ R.map g.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup) ∧
      pCore 2 R ≠ ⊥ ∧
      JankoFourRemainingActorPlacement S ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E) ∧
      (∃ g : Janko4.Model,
        (S : Subgroup Janko4.Model).map (MulAut.conj g).toMonoidHom =
          Janko4.OuterReduction.OddIndex.twoSubgroup ∧
        ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E).map (MulAut.conj g).toMonoidHom ≤
          Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four) := by
  obtain ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,hplace,hsolplace,hmax,hRcore,hremain⟩ :=
    normal_jankoFour_native_two_placements h hH hgen c hY hescape hR C hC hRC e
  exact ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,hplace,hsolplace,hmax,hRcore,hremain,
    jankoFour_actor_max1 S _ _ _ hl hSR hfour hout hremain⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

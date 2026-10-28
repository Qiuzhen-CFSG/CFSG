module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.OddActor
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourCentralizer

/-!
# Excluding the involution-centralizer row of the original J₄ Cartan actor

The unique Sylow-central involution places the original residual and the
entire actor in one literal first centralizer. Its M₂₂ projection carries
the same cubic injectively; the solvable image has order 384. The odd actor
therefore maps into that cubic, and the two successive normalizer lifts
recover normalization of the original residual, contradicting escape.

Only max1 and the specified max4 conjugate remain for the whole actor.
The native consumer retains the original surjection, Sylow, residual,
both Hall products, both quotient markings and the common-max4 exclusion.
No containment of the residual in either remaining actor container is asserted.

Source: Aschbacher--Smith 5.1.13, printed p.637, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Janko4 Janko4.Cardinality Janko4.LocalStructure Janko4.OuterReduction.OddIndex
open Janko4.LocalStructure.SylowNormalEights
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open KernelOrders OutsideKernelOrders
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "M₁" => max1Subgroup matrixA_mul_self matrixB_pow_four
local notation "C₁" => InvolutionCentralizers.First.centralizer

/-- The actual first-centralizer placement normalizes the same residual. -/
theorem jankoFour_first_actor_normalizes (S : Sylow 2 Model) (R D E K : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hs : Group.IsSolvable K) (hSK : (S : Subgroup Model) ≤ K)
    (hDK : D ≤ K) (hEK : E ≤ K) (hD : Odd (Nat.card D))
    (hE : Nat.card E = 3) (hER : E ≤ R) (hED : E ≤ normalizer (D : Set Model))
    (hRC : R ≤ C₁) (hKC : K ≤ C₁) : D ≤ normalizer (R : Set Model) := by
  let := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients.local_perfect hl
  let d := subgroupOfEquivOfLe hRC
  let : Group.IsPerfect (R.subgroupOf C₁) := Group.IsPerfect.ofSurjective
    (f := d.symm.toMonoidHom) d.symm.surjective
  let e := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := he
  let eR := e.trans (eF.trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (R.subgroupOf C₁ ⧸ pCore 2 (R.subgroupOf C₁)) := eR.isSimpleGroup
  let := hs
  have hs' : Group.IsSolvable (K.subgroupOf C₁) := Group.isSolvable_of_isSolvable_injective
    (f := (C₁).subtype.subgroupComap K)
    (fun x y hh => Subtype.ext (Subtype.ext (congrArg (fun k : K => (k : Model)) hh)))
  have hDC := hDK.trans hKC
  have hEC := hEK.trans hKC
  have hh := InvolutionCentralizers.First.QuotientExtension.odd_actor_normalizes_perfect_section
    (S.subtype (hSK.trans hKC)) (R.subgroupOf C₁) (D.subgroupOf C₁) (E.subgroupOf C₁)
    (K.subgroupOf C₁) (by
      rw [←subgroupOf_normalizer_eq hRC]
      exact comap_mono hn) hs' (comap_mono hSK) (comap_mono hDK) (comap_mono hEK)
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv])
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv]) (comap_mono hER) (by
      rw [←subgroupOf_normalizer_eq hDC]
      exact comap_mono hED)
  have hm := (map_mono (f := (C₁).subtype) hh).trans
    ((R.subgroupOf C₁).le_normalizer_map (C₁).subtype)
  rwa [map_subgroupOf_eq_of_le hDC,map_subgroupOf_eq_of_le hRC] at hm

/-- Every common line-centralizer row normalizes the original residual. -/
theorem jankoFour_line_actor_normalizes (S : Sylow 2 Model) (R D E K A : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hs : Group.IsSolvable K) (hSK : (S : Subgroup Model) ≤ K)
    (hDK : D ≤ K) (hEK : E ≤ K) (hD : Odd (Nat.card D))
    (hE : Nat.card E = 3) (hER : E ≤ R) (hED : E ≤ normalizer (D : Set Model))
    (hA : Nat.card A = 2) (hKA : K ≤ centralizer (A : Set Model)) :
    D ≤ normalizer (R : Set Model) := by
  obtain ⟨g,hRg,hSg,hKg⟩ := jankoFour_common_first_centralizer S R K A hl hn he hA hSK hKA
  let f := MulAut.conj g
  let P := S.mapSurjective (f := f.toMonoidHom) f.surjective
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]
    infer_instance
  have hlg := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom
  let d := f.subgroupMap R
  let e := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  let := hs
  have hsg : Group.IsSolvable (K.map f.toMonoidHom) := Group.isSolvable_of_isSolvable_injective
    (f := (f.subgroupMap K).symm.toMonoidHom) (f.subgroupMap K).symm.injective
  have hh := jankoFour_first_actor_normalizes P (R.map f.toMonoidHom) (D.map f.toMonoidHom)
    (E.map f.toMonoidHom) (K.map f.toMonoidHom) hlg
    ((map_mono hn).trans (R.le_normalizer_map f.toMonoidHom)) (he.of_mulEquiv e.symm)
    hsg (map_mono hSK) (map_mono hDK) (map_mono hEK)
    (by rwa [card_map_of_injective f.injective]) (by rwa [card_map_of_injective f.injective])
    (map_mono hER) ((map_mono hED).trans (D.le_normalizer_map f.toMonoidHom)) hRg hKg
  rw [←map_equiv_normalizer_eq] at hh
  exact (map_le_map_iff_of_injective f.injective).mp hh

/-- Actual simultaneous transport of the whole escaping actor into the two surviving rows. -/
@[expose] def JankoFourRemainingActorPlacement (S : Sylow 2 Model) (K : Subgroup Model) : Prop :=
  ∃ g : Model, (S : Subgroup Model).map (MulAut.conj g).toMonoidHom = twoSubgroup ∧
    (K.map (MulAut.conj g).toMonoidHom ≤ M₁ ∨
      K.map (MulAut.conj g).toMonoidHom ≤ SymmetricLinear.max4Subgroup.map
        (MulAut.conj MatrixNormalizerBounds.ThirdConjugacy.conjugator).toMonoidHom)

/-- The involution-centralizer branch is excluded; the original max1/max4 rows remain. -/
theorem jankoFour_remaining_actor_placement (S : Sylow 2 Model) (R D E : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hs : Group.IsSolvable ((D ⊔ (S : Subgroup Model)) ⊔ E : Subgroup Model))
    (hD : Odd (Nat.card D)) (hE : Nat.card E = 3) (hER : E ≤ R)
    (hED : E ≤ normalizer (D : Set Model)) (hout : ¬ D ≤ normalizer (R : Set Model))
    (hp : JankoFourSolvableActorPlacement S ((D ⊔ (S : Subgroup Model)) ⊔ E)) :
    ∃ g : Model, (S : Subgroup Model).map (MulAut.conj g).toMonoidHom = twoSubgroup ∧
      (((D ⊔ (S : Subgroup Model)) ⊔ E).map (MulAut.conj g).toMonoidHom ≤ M₁ ∨
      ((D ⊔ (S : Subgroup Model)) ⊔ E).map (MulAut.conj g).toMonoidHom ≤
        SymmetricLinear.max4Subgroup.map
          (MulAut.conj MatrixNormalizerBounds.ThirdConjugacy.conjugator).toMonoidHom) := by
  obtain ⟨g,hg,hmax | hline | hmax⟩ := hp
  · exact ⟨g,hg,Or.inl hmax⟩
  · exfalso
    let f := MulAut.conj g
    let A := (candidate 1).comap f.toMonoidHom
    have hAm : A.map f.toMonoidHom = candidate 1 := map_comap_eq_self (by
      rw [f.toMonoidHom.range_eq_top_of_surjective f.surjective]
      exact le_top)
    have hA : Nat.card A = 2 := by
      rw [←card_map_of_injective (f := f.toMonoidHom) f.injective (K := A),hAm]
      simpa [candidateRows] using pureKernelCatalogue.2 1
    have hKA : (D ⊔ (S : Subgroup Model)) ⊔ E ≤ centralizer (A : Set Model) := by
      apply (map_le_map_iff_of_injective (f := f.toMonoidHom) f.injective).mp
      rw [map_centralizer_equiv]
      change _ ≤ centralizer (A.map f.toMonoidHom : Set Model)
      rw [hAm]
      exact hline
    exact hout (jankoFour_line_actor_normalizes S R D E _ A hl hn he hs (le_sup_right.trans le_sup_left)
      (le_sup_left.trans le_sup_left) le_sup_right hD hE hER hED hA hKA)
  · exact ⟨g,hg,Or.inr hmax⟩
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The original native map excludes the line row while preserving every prior marking. -/
theorem normal_jankoFour_native_two_placements
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
        (S : Subgroup Janko4.Model).map g.toMonoidHom ≤ SymmetricLinear.max4Subgroup →
        D.map g.toMonoidHom ≤ SymmetricLinear.max4Subgroup →
        ¬ R.map g.toMonoidHom ≤ SymmetricLinear.max4Subgroup) ∧
      pCore 2 R ≠ ⊥ ∧
      JankoFourRemainingActorPlacement S ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E) := by
  obtain ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,hplace,hsolplace,hmax⟩ :=
    normal_jankoFour_native_max4_residual h hH hgen c hY hescape hR C hC hRC e
  exact ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,hplace,hsolplace,hmax,
    jankoFour_residual_core_ne_bot S _ hl hSR hfour,
    jankoFour_remaining_actor_placement S _ _ _ hl hSR hfour hsol hodd hE hER hED hout hsolplace⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

module
public import Theory.GroupTheory.ElementaryEightSolvableMinimal.OddAction
public import Theory.SpecificGroups.Janko4.Model.ElementarySylowFixers
public import Theory.GroupTheory.InvolutionCentralizerControl
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourCore

/-!
# Three literal placements for the whole solvable J₄ actor

A minimal elementary eight under a solvable actor has odd automizer, so
its full Sylow centralizes it. J₄'s Sylow center has order two, excluding
both eight-element pure rows without any blanket maximal-overgroup cover.
The checked kernel catalogue therefore leaves only its literal line and
plane. The line is centralized; the full plane normalizer lies in the
specified conjugate of max4. Along with the existing mixed-row max1 bound,
this places the entire original actor in three actual overgroups.

The native application retains the original surjection, residual, both Hall
products and both quotient markings. In particular it does not place the
residual in the solvable actor or identify it with a full A₅ preimage.
Normalization of the same residual in these three placements remains open.

Source: Aschbacher--Smith 5.1.9--13, printed pp.634--637, refs/quasithin.pdf.
The literal kernel and max4 imports retain their ATLAS attribution and license.
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

/-- A minimal elementary eight cannot lie in the full Sylow of a solvable actor. -/
theorem jankoFour_minimal_eight_impossible (S : Sylow 2 Model) (K A : Subgroup Model)
    (hs : Group.IsSolvable K) (he : IsElementaryAbelian 2 A)
    (hA : Nat.card A = 8) (hAS : A ≤ (S : Subgroup Model))
    (hSK : (S : Subgroup Model) ≤ K) (hn : K ≤ normalizer (A : Set Model))
    (hm : ∀ X : Subgroup Model, X ≤ A → K ≤ normalizer (X : Set Model) →
      X = ⊥ ∨ X = A) : False := by
  let := hs
  let := he
  have hc := card_le_center_of_solvable_minimal_elementary_eight K A
    (S : Subgroup Model) hA hn hm hSK S.isPGroup' hAS
  rw [hA,Janko4.sylow_center_card_two S] at hc
  omega

/-- The original minimal pure row is the literal line or plane, with all markings retained. -/
theorem jankoFour_minimal_kernel_row_small (K E : Subgroup Model)
    (hs : Group.IsSolvable K) (hSK : twoSubgroup ≤ K) (hES : E ≤ twoSubgroup)
    (hrow : JankoFourMinimalKernelRow K E) :
    ∃ A : Subgroup Model, A ≠ ⊥ ∧ A ≤ E ∧ IsElementaryAbelian 2 A ∧
      K ≤ normalizer (A : Set Model) ∧ A ≤ orderSpectrumKernel ∧
      ClosureNormalizerIrreducible A ∧ (∀ u ∈ A, ¬ IsConj u classSeed) ∧
      (∀ X : Subgroup Model, X ≤ A → K ≤ normalizer (X : Set Model) →
        X = ⊥ ∨ X = A) ∧ (A = candidate 1 ∨ A = candidate 2) := by
  obtain ⟨A,ha,hAE,he,hc,hn,hAK,hi,hp,hm⟩ := hrow
  let S : Sylow 2 Model := twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup,index_map_subtype,localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)
  have hnot : Nat.card A ≠ 8 := fun h8 =>
    jankoFour_minimal_eight_impossible S K A hs he h8 (hAE.trans hES) hSK hn hm
  refine ⟨A,ha,hAE,he,hn,hAK,hi,hp,hm,?_⟩
  obtain ⟨i,heq⟩ := pureKernelCatalogue.1 A hAK (hSK.trans hn) hp
  have hcard : Nat.card A = 2 ^ (candidateRows i).length :=
    heq ▸ pureKernelCatalogue.2 i
  fin_cases i
  · exact (ha (heq.trans candidate_zero)).elim
  · exact Or.inl heq
  · exact Or.inr heq
  · exact (hnot (by simpa [candidateRows] using hcard)).elim
  · exact (hnot (by simpa [candidateRows] using hcard)).elim
  · norm_num [candidateRows] at hcard
    omega

/-- The whole actor centralizes the literal line or lies in the specified max4 conjugate. -/
theorem jankoFour_solvable_kernel_row_placement (K E : Subgroup Model)
    (hs : Group.IsSolvable K) (hSK : twoSubgroup ≤ K) (hES : E ≤ twoSubgroup)
    (hrow : JankoFourMinimalKernelRow K E) :
    K ≤ centralizer (candidate 1 : Set Model) ∨
      K ≤ SymmetricLinear.max4Subgroup.map
        (MulAut.conj MatrixNormalizerBounds.ThirdConjugacy.conjugator).toMonoidHom := by
  obtain ⟨A,_,_,_,hn,_,_,_,_,ha⟩ :=
    jankoFour_minimal_kernel_row_small K E hs hSK hES hrow
  rcases ha with rfl | rfl
  · exact Or.inl (hn.trans (normalizer_le_centralizer_of_card_two _ (by
      simpa [candidateRows] using pureKernelCatalogue.2 1)))
  · apply Or.inr
    apply hn.trans
    rw [←PureNormalizers.max4Plane_map_conjugator,←map_equiv_normalizer_eq]
    exact map_mono (PureNormalizers.max4Plane_normalizer_lt_of_centralizer
      (PureNormalizers.max4Plane_centralizer_le_of_marking
        MatrixNormalizerBounds.Max4EightCentralizer.marking)).le

/-- Actual simultaneous transport of the full Sylow and the whole actor into three overgroups. -/
@[expose] def JankoFourSolvableActorPlacement (S : Sylow 2 Model) (K : Subgroup Model) : Prop :=
  ∃ g : Model, (S : Subgroup Model).map (MulAut.conj g).toMonoidHom = twoSubgroup ∧
    (K.map (MulAut.conj g).toMonoidHom ≤ M₁ ∨
      K.map (MulAut.conj g).toMonoidHom ≤ centralizer (candidate 1 : Set Model) ∨
      K.map (MulAut.conj g).toMonoidHom ≤ SymmetricLinear.max4Subgroup.map
        (MulAut.conj MatrixNormalizerBounds.ThirdConjugacy.conjugator).toMonoidHom)

/-- Solvability removes every elementary-eight row from the whole-actor placement. -/
theorem jankoFour_solvable_actor_placement (S : Sylow 2 Model) (K : Subgroup Model)
    (hs : Group.IsSolvable K) (hSK : (S : Subgroup Model) ≤ K) (hc : pCore 2 K ≠ ⊥) :
    JankoFourSolvableActorPlacement S K := by
  obtain ⟨g,E,hg,_,hES,_,_,_,hrow⟩ := jankoFour_whole_actor_placement S K hSK hc
  refine ⟨g,hg,?_⟩
  rcases hrow with hmax | hrow
  · exact Or.inl hmax
  · apply Or.inr
    let f := (MulAut.conj g).toMonoidHom
    let := hs
    have hs' : Group.IsSolvable (K.map f) :=
      Group.isSolvable_of_isSolvable_injective
        (f := ((MulAut.conj g).subgroupMap K).symm.toMonoidHom)
        ((MulAut.conj g).subgroupMap K).symm.injective
    exact jankoFour_solvable_kernel_row_placement (K.map f) E hs'
      (hg ▸ map_mono hSK) hES hrow

open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- Literal whole-actor placement under the original native map, preserving
both Hall products, the same residual, both marked quotients and escape. -/
theorem normal_jankoFour_native_solvable_placement
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
      JankoFourSolvableActorPlacement S ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E) := by
  obtain ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,hplace⟩ :=
    normal_jankoFour_native_whole_actor h hH hgen c hY hescape hR C hC hRC e
  exact ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,hplace,
    jankoFour_solvable_actor_placement S _ hsol (le_sup_right.trans le_sup_left) htwo⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

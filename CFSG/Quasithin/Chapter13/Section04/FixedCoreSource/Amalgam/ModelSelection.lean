module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.CoveredSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.AlternatingPlaneExclusion
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneOrdinary

/-!
# Selecting the actual nonsolvable amalgam models

The preceding component list loses its triple-cover row by a chosen
constituent detecting the cubic center, and its unitary row by the original
13.3.16 implication. The two remaining rows carry actual quotient
isomorphisms to PSL₃(2) or A₆. Both give ordinary Thompson normality.

For an original plane pair, the S₃ normalizer already forces L/O₂(L) to
be ordinary A₆. The checked alternating-plane exclusion then selects the
linear row and supplies the residual commutator, full overgroup formula
and failure of near-maximum Thompson normality. Neither component nor
original-L model marking is assumed in this application.

The original 13.3.2 module clauses, same-G,T 13.3.16 implication and the
independent large-distance input remain explicit earlier-source inputs.
Their producers and final discharge remain unchanged. The solvable
noncommuting branch and general escape still belong to the source assembly;
this module does not assert either universal 13.4.7 interface.
Source: Aschbacher--Smith 13.4.5(4), 13.4.7(1ii,1iv,2,4),
printed pp.898--903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
variable
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)

include h₀ D m h1332 fixed covered hTA hTB eA eB hne hindexA hindexB hres h13316

/-- The actual component quotient is linear-three or ordinary alternating-six. -/
theorem original_pair_component_models
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent) :
    let C := K.map (A ⊔ B).subtype
    Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 6)) := by
  rcases original_pair_component_quotient_models h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK with hl | hs | hc | hu
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hl
    let := Fintype.ofFinite F
    let a : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
    exact Or.inl ⟨e.trans (Atlas.fieldEquivPSL 3 a)⟩
  · exact Or.inr hs
  · exact (original_pair_component_not_covered h₀ D m h1332 fixed covered
      hTA hTB eA eB hne hindexA hindexB hres K hK hc).elim
  · have hf := (original_pair_component_geometry h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).2.1
    exact (Nonsolvable.selected_unitary_excluded h₀ h13316 hf hu).elim

variable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hnonsolv : ¬ Group.IsSolvable (A ⊔ B : Subgroup G))

include h structural hout hindexL hnonsolv

/-- Every nonsolvable original pair normalizes J(T), without a selected model. -/
theorem original_pair_nonsolvable_thompson_normal :
    A ⊔ B ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable hnonsolv
  have hm := original_pair_component_models h₀ D m h1332 fixed covered
    hTA hTB eA eB hne hindexA hindexB hres h13316 K hK
  rcases hm with hlin | halt
  · exact original_pair_linear_thompson_normal h₀ h structural D m
      hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK hlin.some
  · exact original_pair_alternating_thompson_normal h₀ h structural D m
      hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK halt.some

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- In the actual nonsolvable plane pair, model selection gives the literal
residual commutator and full linear overgroup conclusion. -/
theorem original_pair_nonsolvable_plane_conclusion
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) :
    ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
        (pResidual 2 B).map B.subtype ∧
      Solvable.LinearAmalgamConclusion T (A ⊔ B) ∧
      ¬ A ⊔ B ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
  obtain ⟨eL⟩ := original_plane_ordinary D m W hW hTW hB eB
  obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable hnonsolv
  have hm := original_pair_component_models h₀ D m h1332 fixed covered
    hTA hTB eA eB hne hindexA hindexB hres h13316 K hK
  rcases hm with hlin | halt
  · exact original_pair_linear_plane_conclusion_of_largeDistance h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres hlin.some hl h structural hout hindexL
        eL W hW hTW hB
  · exact (original_pair_alternating_plane_impossible_of_largeDistance h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres halt.some hl h structural hout hindexL
        eL W hW hTW hB).elim

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

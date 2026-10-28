module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ModelSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearPlaneMovementAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.AlternatingPlaneExclusionAt

/-!
# Guarded model selection on the actual original plane pair

The genuine preceding component catalogue leaves linear-three or ordinary
A6. The S3 second plane forces the original L quotient to be ordinary A6;
the guarded plane contradiction excludes the selected A6 row. The surviving
actual component comes with its literal quotient isomorphism, and the
plane argument proves full second-residual movement by J1(T).

No component model, shortness, cubic budget or residual-movement callback
is assumed. Earlier module/catalogue/unitary and natural large-distance
inputs remain explicit. The solvable join alternative and full overgroup
conclusion still require their separate source constructions.
Source: Aschbacher--Smith 13.4.5(4) and 13.4.7(4), printed pp.898,902--903.
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


variable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hnonsolv : ¬ Group.IsSolvable (A ⊔ B : Subgroup G))

include h structural hout hindexL hnonsolv

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- Select the actual linear component in the nonsolvable original plane pair
and derive movement of its literal second two-residual. -/
theorem original_pair_nonsolvable_plane_linear_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) :
    ∃ K : Subgroup (A ⊔ B : Subgroup G), K.IsCComponent ∧
      Nonempty (((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
        Matrix.PSL3Two.PSL) ∧
      ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
        (pResidual 2 B).map B.subtype ∧
      ¬ A ⊔ B ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
  obtain ⟨eL⟩ := original_plane_ordinary D m W hW hTW hB eB
  obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable hnonsolv
  have hm := original_pair_component_models h₀ D m h1332 fixed covered
    hTA hTB eA eB hne hindexA hindexB hres h13316 K hK
  rcases hm with hlin | halt
  · obtain ⟨hc,hn⟩ := original_pair_linear_plane_movement_of_largeDistance_at h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres hlin.some hl h structural hout hindexL
        eL W hW hTW hB
    exact ⟨K,hK,hlin,hc,hn⟩
  · exact (original_pair_alternating_plane_impossible_of_largeDistance_at h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres halt.some hl h structural hout hindexL
        eL W hW hTW hB).elim

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity.SupportObstruction
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The actual Suzuki component in the nonfaithful actor branch

An ordinary component of the faithful full-orbit image is a semisimple
section of the original normalizer. Theorem A therefore supplies its odd
prime-rank bounds, without assuming that arbitrary quotients are SQTK.
Its two-core is trivial by subnormality and reducedness of the full action.
The complete A.3.6 catalogue consequently identifies every three-free
component with a concrete Suzuki matrix group.

The final application retains the component J produced by the actual
starred actor, its entire actor orbit, its placement in the original SL₃
component centralizer, and the same commutator equality. It adds a genuine
isomorphism J ≃ Sz(2^(2r+1)), rather than a family label or an unconnected
model. The support and strict-ratio conclusions from SupportObstruction
remain attached to that same orbit.

The invariant natural-constituent step of D.3.8 is still required, as is
the faithful-actor cubic-containment branch. Both remain with
qt-d-1222-natural-preliminary-source; final chapter assembly belongs to
qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith, Theorems A and C, pp.33--41; A.3.6, pp.43--45;
and the nonfaithful branch of D.3.9, pp.200--201, used in 11.0.4, p.760.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative ENNReal
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original SQTK cover controls each actual component through Theorem A. -/
theorem fullAction_component_sqtk :
    letI := fullModule_elementary D S
    ∀ J : Subgroup (actionImage (fullModuleConjugation D S)),
      IsComponent (actionImage (fullModuleConjugation D S)) J →
      IsSQTK KnownSimple.IsKnownSimple J := by
  let := fullModule_elementary D S
  intro J hJ
  let := hJ.2
  let M := normalizer (L : Set G)
  let ρ := fullModuleConjugation D S
  have hsec : ChapterA.Section02.IsSectionOf J M :=
    (ChapterA.Section02.IsSectionOf.subgroup J).ambient_surjective
      (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective
  have hsemi : ChapterA.Section02.IsSemisimple J := by
    apply top_unique
    exact le_sSup (show IsComponent J ⊤ from
      ⟨.top,IsQuasisimple.of_mulEquiv (topEquiv : (⊤ : Subgroup J) ≃* J).symm⟩)
  have hs := normalizer_sqtk D S
  exact ⟨ChapterA.Section02.TheoremA.stronglyQuasithin_section
    ChapterA.Section02.theoremA_knownSimple hs.stronglyQuasithin hs.isKGroup hsec hsemi,
    hsec.isKGroup hs.isKGroup⟩

/-- A three-free component of the literal full action has an actual Suzuki marking. -/
theorem fullAction_component_suzuki_of_three_free :
    letI := fullModule_elementary D S
    ∀ J : Subgroup (actionImage (fullModuleConjugation D S)),
      IsComponent (actionImage (fullModuleConjugation D S)) J →
      Nat.Coprime 3 (Nat.card J) →
      ∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) := by
  let := fullModule_elementary D S
  intro J hJ h3
  let := hJ.2
  have hJ2 : pCore 2 J = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hJ.1,fullAction_twoCore_eq_bot D S]
    exact J.subtype.ker_eq_bot_iff.mpr J.subtype_injective
  have htop : IsComponent J ⊤ :=
    ⟨.top,IsQuasisimple.of_mulEquiv (topEquiv : (⊤ : Subgroup J) ≃* J).symm⟩
  have hclass := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    J (fullAction_component_sqtk D S J hJ) hJ2 ⊤ htop.isCComponent
  have h3top : Nat.Coprime 3 (Nat.card (⊤ : Subgroup J)) := by
    simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup J) ≃* J).toEquiv] using h3
  obtain ⟨r,hr,⟨e⟩⟩ :=
    Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue.a36_suzuki_of_coprime
      hclass h3top
  exact ⟨r,by omega,⟨(topEquiv : (⊤ : Subgroup J) ≃* J).symm.trans e⟩⟩

/-- The nonfaithful source alternative with its original component and orbit,
now marked by an actual Suzuki isomorphism and retaining the strict-ratio obstruction. -/
theorem sl3_fullAction_starred_nonfaithful_suzuki_component
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let τ := imageRepresentation ρ
    let H := actionImage ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ A : Subgroup H, A ∈ ChapterD.QhatStar τ →
      A ⊓ centralizer (K : Set H) ≠ ⊥ →
      S.field.degree % 4 = 2 ∧
      ∃ J : Subgroup H, IsComponent H J ∧
        ⁅J,A ⊓ centralizer (K : Set H)⁆ ≠ ⊥ ∧
        componentOrbit J A ≤ centralizer (K : Set H) ∧
        ⁅componentOrbit J A,A ⊓ centralizer (K : Set H)⁆ = componentOrbit J A ∧
        Nat.Coprime 3 (Nat.card J) ∧ 5 ∣ Nat.card J ∧
        (∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)) ∧
        (¬ IsIrrPlus τ (componentOrbit J A) (subspaceCommutator τ ⊤ (componentOrbit J A))) ∧
        ∀ I : Submodule (ZMod 2) (Additive (componentOrbit V (normalizer (L : Set G)))),
          IsIrrPlus τ (componentOrbit J A) I → A ≤ subspaceStabilizer τ I →
          restrictedSubgroup τ I A ∈ ChapterD.Qhat (subspaceImageRepresentation τ I) ∧
            actionRatio (subspaceImageRepresentation τ I) (restrictedSubgroup τ I A) < cubicRatio τ ∧
            actionRatio (subspaceImageRepresentation τ I) (restrictedSubgroup τ I A) < 2 := by
  let := fullModule_elementary D S
  dsimp only
  intro A hA hn
  obtain ⟨hd,J,hJ,hm,ho,he,h3,h5,hi,hr⟩ :=
    sl3_fullAction_starred_nonfaithful_component_strict_constituents D S m heven A hA hn
  exact ⟨hd,J,hJ,hm,ho,he,h3,h5,fullAction_component_suzuki_of_three_free D S J hJ h3,hi,hr⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary

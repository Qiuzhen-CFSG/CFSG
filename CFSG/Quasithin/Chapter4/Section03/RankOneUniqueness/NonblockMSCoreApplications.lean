module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCoreComplete
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryTorus
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceAssembly
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameUnitarySourceMarking

/-!
# Applying the original core identity to the secondary source

The completed C.1.35 argument discharges the O₂(KS)=Q premise of the
all-degree secondary-source constructor. The constructor supplies the
original odd torus and whole-radical generation under the same quotient
action. The completed corrected sieve then gives degree two, the full
PSL₃(4)/PSU₃(5) quotient alternative and the original outer-torus clause.
The already proved literal quintic marking and radical bound exclude PSU₃(5),
leaving the original PSL₃(4) terminal representation case.

The original MSData, parabolic/Sylow markings, secondary component and
normalizer geometry remain explicit. Their source construction and the
linear-four terminal representation contradiction belong to the same nonblock owner,
qt-d-1222-rankone-uniqueness-nonblock. This is a conditional application,
not the completed source nonblock exclusion. It never supplies the refuted
whole-radical torus-movement field.
Source: Aschbacher--Smith, original 4.3.11--16, printed pp.617--619.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- The original core identity is now proved from MSData in the actual
all-degree secondary construction; only the earlier geometric inputs remain. -/
theorem MSData.exists_secondarySourceData_of_geometry
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent) (hBn : B.Normal)
    (hBq : IsQuasisimple (B ⧸ pCore 2 B))
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype)
    (henlarged : (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hnorm : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (henlarges : secondary c < (B.map (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c) :
    ∃ s : SecondarySourceData c n, s.component = B ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      ((Q c).subgroupOf (rootNormalizer c)).map s.action ⊔
        ⁅((R₂ c).subgroupOf (rootNormalizer c)).map s.action,
          ((secondary c).subgroupOf (rootNormalizer c)).map s.action⁆ =
        ((R₂ c).subgroupOf (rootNormalizer c)).map s.action :=
  d.exists_secondarySourceData_of_marked_parabolic hn D hL hSL B hB hBn hBq hsec
    (d.joinCore_eq hn) henlarged hnorm henlarges

/-- The same source constructor and the corrected sieve give the exceptional
full quotient and original outer torus without a core-identity premise. -/
theorem MSData.exceptional_of_secondary_geometry
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent) (hBn : B.Normal)
    (hBq : IsQuasisimple (B ⧸ pCore 2 B))
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype)
    (henlarged : (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hnorm : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (henlarges : secondary c < (B.map (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c) :
    ∃ s : SecondarySourceData c n, s.component = B ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      (n = 2 ∧ (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 ∨
        ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)) ∧
      (s.torus.subgroupOf (rootNormalizer c)).map s.action ⊓
        MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥ := by
  obtain ⟨s,hs,hK,hfix,_⟩ := d.exists_secondarySourceData_of_geometry hn D hL hSL B
    hB hBn hBq hsec henlarged hnorm henlarges
  exact ⟨s,hs,hK,hfix,
    EndgameSieve.SecondarySourceData.exceptional_of_marked_parabolic s d hn D h hL hSL⟩

/-- The completed quintic marking and radical bound exclude the unitary
branch of the constructed source witness, leaving the linear-four terminal case. -/
theorem MSData.linearFour_of_secondary_geometry
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent) (hBn : B.Normal)
    (hBq : IsQuasisimple (B ⧸ pCore 2 B))
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype)
    (henlarged : (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hnorm : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (henlarges : secondary c < (B.map (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c) :
    ∃ s : SecondarySourceData c n, s.component = B ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      (n = 2 ∧ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4) ∧
      (s.torus.subgroupOf (rootNormalizer c)).map s.action ⊓
        MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥ := by
  obtain ⟨s,hs,hK,hfix,⟨hn2,hmodel⟩,houter⟩ := d.exceptional_of_secondary_geometry hn D h
    hL hSL B hB hBn hBq hsec henlarged hnorm henlarges
  have hlinear : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4 := by
    rcases hmodel with hlinear | hunitary
    · exact hlinear
    · subst n
      exact (SourceEndgame.unitaryFive_false_of_marked_parabolic d s D h hunitary hL hSL).elim
  exact ⟨s,hs,hK,hfix,⟨hn2,hlinear⟩,houter⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end

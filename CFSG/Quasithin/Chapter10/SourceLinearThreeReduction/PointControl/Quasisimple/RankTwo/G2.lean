module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.CentralImage
public import Theory.AtlasPort.LinearGroups.G2.ShortLocalCoreCenter
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import CFSG.Quasithin.Chapter10.SourceA5PointG2
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Discharging the nonbinary G₂ containing components

Full-Sylow placement marks the literal local image as a parabolic residual.
The first factor centralizes its core center, contradicting full movement
of the original module. The second factor has trivial automorphism fixer,
so the opposite moved factor centralizes I and contradicts its escape.

Source: Aschbacher--Smith A.3.12 and 10.2.9, pp.47--48,750--751.
No module row, fixed kernel or field parameter is removed by assumption.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
variable {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include c
/-- The full point Sylow marks the actual local image as one of the two G₂ residuals. -/
theorem g2_placement [Group.IsPerfect I]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F)
    (eI : (I ⧸ center I) ≃* Atlas.G2.Model F) :
    ∃ f : (I ⧸ center I) ≃* Atlas.G2.Model F,
      (L.subgroupOf I).map
        (f.toMonoidHom.comp (QuotientGroup.mk' (center I))) = Atlas.G2.LieParabolicSetup.local₁ ∨
      (L.subgroupOf I).map
        (f.toMonoidHom.comp (QuotientGroup.mk' (center I))) = Atlas.G2.LieParabolicSetup.local₂ := by
  obtain ⟨S,_,hB,_,_,hproper,_⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let A := B.map eI.toMonoidHom
  let : Group.IsSolvable eI.toMonoidHom.ker := by
    rw [eI.toMonoidHom.ker_eq_bot_iff.mpr eI.injective]
    infer_instance
  have hA : A ∈ localCComponents (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB eI.toMonoidHom
  have hp : A ≠ ⊤ := by
    intro ht
    apply hproper
    apply map_injective (f := eI.toMonoidHom) eI.injective
    rw [map_top_of_surjective _ eI.surjective]
    exact ht
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2.local_placement
    hq (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) A hA hp
  refine ⟨eI.trans (MulAut.conj g), ?_⟩
  have he : (eI.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp eI.toMonoidHom := by ext; rfl
  simpa only [A,B,q,map_map,he,MonoidHom.comp_assoc] using hg


/-- The first residual is impossible; the second has trivial automorphism fixer. -/
theorem g2_common_centralizer [Group.IsPerfect I]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (eI : (I ⧸ center I) ≃* Atlas.G2.Model F) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G) := by
  obtain ⟨f,hf⟩ := g2_placement D c hq eI
  rcases hf with hf | hf
  · have hh := marked_core_center_not_central D c.strict.le f
    dsimp only at hh
    rw [hf] at hh
    exact (hh Atlas.G2.LieParabolicSetup.local₁_core_center_le_center).elim
  · exact source_g2_second_local_component_centralized hq f hf
      (partner_normalizes D c) c.crossed

/-- The common-centralizer contradiction excludes every nonbinary G₂ carrier. -/
theorem not_g2 [Group.IsPerfect I] {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At (I ⧸ center I) (2 ^ n)) : False := by
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn)
  exact source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer I
    c.escapes (g2_common_centralizer D c hq eI)

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo

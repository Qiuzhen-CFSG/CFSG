module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.CentralImage
public import Theory.SpecificGroups.Triality.ArmsLocalCoreCenter
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality
public import CFSG.Quasithin.Chapter10.SourceA5PointTriality

/-!
# Discharging triality over fields larger than two

The full restricted Sylow and nonzero local two-core place the actual image
of L in a root parabolic residual. The arms factor is excluded by its
central core center. The central factor's involutory automorphism fixer
then centralizes I, contrary to the moved-normalizer bound.

Source: Aschbacher--Smith A.3.12 and 10.2.9, pp.47--48,750--751.
The binary field remains an explicit unresolved case; no fixed-setup
irreducibility, generation bound or A₅ quotient is assumed.
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
open Triality.Standard Triality.Standard.Parabolics
/-- The actual local image is the central-node residual; the arms node is impossible. -/
theorem triality_placement [Group.IsPerfect I]
    (n : ℕ) (hn : 0 < n) (hq : 2 < 2 ^ n)
    (eI : (I ⧸ center I) ≃* BinaryCarrier n hn) :
    ∃ f : (I ⧸ center I) ≃* BinaryCarrier n hn,
      (L.subgroupOf I).map (f.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        localFactor (binaryParameters n hn) .central := by
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
  have hcore : pCore 2 A ≠ ⊥ := by
    intro hz
    have hc := marked_core_center_not_central D c.strict.le eI
    have hmap : A = (L.subgroupOf I).map (eI.toMonoidHom.comp q) := map_map _ _ _
    rw [←hmap] at hc
    apply hc
    rintro _ ⟨z,_,rfl⟩
    have hz' : (z : A) = 1 := mem_bot.mp (hz ▸ z.property)
    change (z : A) ∈ center A
    rw [hz']
    exact one_mem _
  obtain ⟨g,a,hg⟩ := SourceEmbeddings.FiveLocalFF.Triality.local_placement n hn hq
    (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) A hA hcore
  let f := eI.trans (MulAut.conj g)
  have hm : (L.subgroupOf I).map (f.toMonoidHom.comp q) =
      localFactor (binaryParameters n hn) a := by
    have he : f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp eI.toMonoidHom := by ext; rfl
    simpa only [A,B,q,map_map,he,MonoidHom.comp_assoc] using hg
  cases a with
  | central => exact ⟨f,hm⟩
  | arms =>
    have hc := marked_core_center_not_central D c.strict.le f
    dsimp only at hc
    rw [hm] at hc
    exact (hc (arms_core_center_le_center _ rfl)).elim

/-- The literal central marking gives common centralization by the involutory fixer theorem. -/
theorem triality_common_centralizer [Group.IsPerfect I]
    (n : ℕ) (hn : 0 < n) (hq : 2 < 2 ^ n)
    (eI : (I ⧸ center I) ≃* BinaryCarrier n hn) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G) := by
  obtain ⟨f,hf⟩ := triality_placement D c n hn hq eI
  let := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) :=
    IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  exact source_triality_central_local_component_centralized n hn f hf
    (partner_normalizes D c) c.crossed

/-- Every triality carrier over a field larger than two is excluded in the original configuration. -/
theorem not_triality_large [Group.IsPerfect I] {n : ℕ} (hn : 2 ≤ n)
    (hm : IsTrialityGroupAt (2 ^ n) (I ⧸ center I)) : False := by
  have hn0 : 0 < n := by omega
  obtain ⟨eI⟩ := (isTrialityGroupAt_binary_iff _ n hn0).mp hm
  have hq : 2 < 2 ^ n :=
    lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn)
  exact source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer I
    c.escapes (triality_common_centralizer D c n hn0 hq eI)

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo

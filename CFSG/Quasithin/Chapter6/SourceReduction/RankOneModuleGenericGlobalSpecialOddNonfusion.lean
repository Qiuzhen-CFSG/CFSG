module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialFieldAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Nonfusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityNonfusion

/-!
# G₂ and triality nonfusion at odd original field degree

The actual field-action kernel calculation gives |T:S| dividing n for G₂.
For triality it first gives divisibility by 3n, using the literal cubic-field
arms quotient; the two-power order of T removes the odd factor three.
When n is odd, T = S, so the original C_T(Z(K)) ≤ S premise is discharged.
The previously constructed root pair, both coherent Sylow placements, and
movement under the original S then prove marked short-root nonfusion.

The Chapter12 companion applies both results to the chosen-module setup.
Even exponents still require the action on the original root center;
source uniqueness, exhaustive comparison and ambient recognition remain
separate obligations. These are special cases of the nonfusion step,
with the same marked representative and both compatible parabolic maps.
Source: Aschbacher–Smith F.4.29(2,7), pp.289–290, F.4.35, p.292, and
5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The actual G₂ row has [T:S] dividing its original field exponent. -/
theorem Preparation.g2_source_sylow_index_dvd
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    (sourceS L H).relIndex (T : Subgroup G) ∣ n := by
  have hs := d.g2_local_structure h hTH hp F he
  exact d.residual_sylow_index_dvd h hTH hs.2.2.2.2 hs.2.2.2.1

/-- The genuine cubic-field arms quotient gives [T:S] dividing 3n. Since
T is a two-group, the same index divides the original exponent n. -/
theorem Preparation.triality_source_sylow_index_dvd
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    (sourceS L H).relIndex (T : Subgroup G) ∣ n := by
  have hs := d.triality_sourceS_le_factors h hTH hp m hm he
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hTH hp _ rfl he).elim
  obtain ⟨e⟩ := he
  have hq := (d.triality_local_structure h hTH hp m hm e).2.2.2.2.1
  have hd := d.residual_sylow_index_dvd h hTH hs hq
  obtain ⟨k,hk⟩ := T.isPGroup'.exists_card_eq
  have ht : (sourceS L H).relIndex (T : Subgroup G) ∣ 2^k := by
    rw [←hk]
    exact relIndex_dvd_card _ _
  have hc : Nat.Coprime ((sourceS L H).relIndex (T : Subgroup G)) 3 :=
    Nat.Coprime.of_dvd_left ht ((by decide : Nat.Coprime 2 3).pow_left k)
  exact hc.dvd_of_dvd_mul_left hd

private theorem sourceS_eq_sylow_of_index_dvd_odd
    {T : Sylow 2 G} {L H : Subgroup G} {n : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) (hn : Odd n)
    (hd : (sourceS L H).relIndex (T : Subgroup G) ∣ n) :
    sourceS L H = (T : Subgroup G) := by
  obtain ⟨k,hk⟩ := T.isPGroup'.exists_card_eq
  have ht : (sourceS L H).relIndex (T : Subgroup G) ∣ 2^k := by
    rw [←hk]
    exact relIndex_dvd_card _ _
  exact le_antisymm (sourceS_le_sylow hTL hTH)
    (relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes
      (hn.coprime_two_right.pow_right k) hd ht))

/-- For odd original exponent the G₂ source Sylow equals S; in particular
no extra centralizer-containment hypothesis is needed for nonfusion. -/
theorem Preparation.g2_short_root_not_fused_of_odd
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (hn : Odd n)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    sourceS L H = (T : Subgroup G) ∧
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      ∃ v ∈ Q, (∃ w : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
        w.val=v ∧ (e.right w).val=Atlas.G2.rootC (1:F)) ∧
      v ∉ Z ∧ orderOf v=2 ∧ ∀ g : G, v ∉ Z.conjBy g := by
  have hs := sourceS_eq_sylow_of_index_dvd_odd h.sylow_normalizes hH.1.1.2 hn
    (d.g2_source_sylow_index_dvd h hH.1.1.2 hp F he)
  exact ⟨hs,d.g2_short_root_not_fused_of_centralizer_le h hH hp F he
    (hs.symm ▸ inf_le_left)⟩

/-- The genuine triality short root is not fused into the original right
center for odd original exponent. The cubic quotient is retained in proving T=S. -/
theorem Preparation.triality_short_root_not_fused_of_odd
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (hn : Odd n) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    sourceS L H = (T : Subgroup G) ∧
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam
        (_root_.Triality.Standard.binaryParameters m hm)).reverse,
      ∃ v∈Q, (∃ w : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
        w.val=v ∧ (e.right w).val=
          _root_.Triality.Standard.RadicalCoordinates.LeviCommutators.short
            (_root_.Triality.Standard.binaryParameters m hm) rfl 2 1) ∧
      v∉Z ∧ orderOf v=2 ∧ ∀ g : G, v∉Z.conjBy g := by
  have hs := sourceS_eq_sylow_of_index_dvd_odd h.sylow_normalizes hH.1.1.2 hn
    (d.triality_source_sylow_index_dvd h hH.1.1.2 hp m hm he)
  exact ⟨hs,d.triality_short_root_not_fused_of_centralizer_le h hH hp m hm he
    (hs.symm ▸ inf_le_left)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

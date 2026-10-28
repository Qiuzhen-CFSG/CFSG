module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.TerminalLine
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.TerminalLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Inputs

/-!
# A noncentral fixed displacement for large two-subgroup actors

In the marked Sylow two-subgroup of S₆, every subgroup of order at least
four contains one of the three nonidentity central elements. A certificate
on its sixteen elements proves this assertion. Each of those elements has
a noncentral displacement fixed by the whole Sylow subgroup on both the
natural module and its augmentation cover. Conjugation and the literal
cover equivalence transport the witness to any containing two-subgroup.

This is the model calculation used by SylowLargeCritical for the first-edge
intersection of a large critical commutator. It does not identify the
replacement radical with a point core or an elementary subgroup, and it
retains the cover's central attachment.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3), (5.10)--(5.11), printed pp.866--867,922--924. This specializes
the critical-commutator argument to the actual six-letter quotient.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace SylowFixedLine
open CFSG.Quasithin.ChapterB.Offenders.Six

private def actors : Fin 3 → S := ![swap45,swap01*swap23,swap01*swap23*swap45]
private def vectors : Fin 3 → BinaryPermutation.core (Fin 6) :=
  ![CoreCrossing.pairWord 0 4,CoreCrossing.pairWord 0 2,CoreCrossing.pairWord 0 2]
private def lines : Fin 3 → BinaryPermutation.core (Fin 6) :=
  ![CoreCrossing.pairWord 4 5,CoreCrossing.pairWord 0 1+CoreCrossing.pairWord 2 3,
    CoreCrossing.pairWord 0 1+CoreCrossing.pairWord 2 3]

private theorem pair_certificate : ∀ i j : Fin 16,
    sylowWords i ≠ 1 → sylowWords j ≠ 1 → sylowWords i ≠ sylowWords j →
    ∃ k : Fin 3, actors k = sylowWords i ∨ actors k = sylowWords j ∨
      actors k = sylowWords i*sylowWords j ∨ actors k = (sylowWords i)^2 ∨
      actors k = (sylowWords j)^2 ∨ actors k = ⁅sylowWords i,sylowWords j⁆ := by
  decide +kernel

private theorem large_subgroup_actor (A : Subgroup S) (hA : A ≤ sylowCarrier)
    (hc : 4 ≤ Nat.card A) : ∃ k : Fin 3, actors k ∈ A := by
  by_contra hn
  have hne : A ≠ ⊥ := by intro he; rw [he,card_bot] at hc; omega
  obtain ⟨g,hg,hg1⟩ := (A.bot_or_exists_ne_one).resolve_left hne
  have hle : A ≤ zpowers g := by
    intro k hk
    by_cases hk1 : k=1
    · rw [hk1]; exact one_mem _
    by_cases hkg : g=k
    · rw [←hkg]; exact mem_zpowers g
    obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff _).mp (hA hg)
    obtain ⟨j,rfl⟩ := (mem_sylowCarrier_iff _).mp (hA hk)
    obtain ⟨n,he|he|he|he|he|he⟩ := pair_certificate i j hg1 hk1 hkg
    · exact (hn ⟨n,he ▸ hg⟩).elim
    · exact (hn ⟨n,he ▸ hk⟩).elim
    · exact (hn ⟨n,he ▸ A.mul_mem hg hk⟩).elim
    · exact (hn ⟨n,he ▸ A.pow_mem hg 2⟩).elim
    · exact (hn ⟨n,he ▸ A.pow_mem hk 2⟩).elim
    · exact (hn ⟨n,he ▸ A.mul_mem (A.mul_mem (A.mul_mem hg hk) (A.inv_mem hg)) (A.inv_mem hk)⟩).elim
  have hs : g^2=1 := by
    obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff _).mp (hA hg)
    have hh : ∀ i : Fin 16, (sylowWords i)^2=1 ∨ (sylowWords i)^2=actors 1 := by decide +kernel
    rcases hh i with hh | hh
    · exact hh
    · exact (hn ⟨1,hh ▸ A.pow_mem hg 2⟩).elim
  have hcard : Nat.card (zpowers g) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hs)
  have hh := (card_le_of_le hle).trans hcard
  omega

private theorem core_displacement : ∀ k : Fin 3,
    coreRepresentation (Fin 6) (actors k) (vectors k)-vectors k=lines k := by decide +kernel
private theorem core_fixed : ∀ k : Fin 3, ∀ i : Fin 16,
    coreRepresentation (Fin 6) (sylowWords i) (lines k)=lines k := by decide +kernel
private theorem core_nonfixed : ∀ k : Fin 3,
    coreRepresentation (Fin 6) (Equiv.swap 0 4) (lines k)≠lines k := by decide +kernel

private theorem natural_lines (k : Fin 3) :
    coreToNatural (Fin 6) (lines k) = pairVector 4 5 := by
  fin_cases k
  · rfl
  all_goals
    apply Subtype.ext
    change (constants (Fin 6)).mkQ _ = (constants (Fin 6)).mkQ _
    apply (Submodule.Quotient.eq (constants (Fin 6))).mpr
    have he : (lines 1).val - (CoreCrossing.pairWord 4 5).val = allOne (Fin 6) := by
      ext i
      fin_cases i <;> decide
    change (lines 1).val - (CoreCrossing.pairWord 4 5).val ∈ constants (Fin 6)
    rw [he]
    exact Submodule.subset_span (by simp)

private theorem witness_transport
    {Y W : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) S Y) (τ : Representation (ZMod 2) S W)
    (E : Y ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (ρ g v) = τ g (E v))
    (a : S) (v w : W) (hdisp : τ a v-v = w)
    (hfix : ∀g∈sylowCarrier, τ g w=w) (hn : ∃g, τ g w≠w)
    (u : S) : ∃ z : Y, let r := ρ (u*a*u⁻¹) z-z
      (∀g∈sylowCarrier.map (MulAut.conj u).toMonoidHom, ρ g r=r) ∧
      ¬ ∀g, ρ g r=r := by
  let z := E.symm (τ u v)
  have hr : E (ρ (u*a*u⁻¹) z-z) = τ u w := by
    rw [map_sub,hE]
    simp only [z,LinearEquiv.apply_symm_apply,map_mul,Module.End.mul_apply,τ.inv_self_apply]
    rw [←map_sub,hdisp]
  refine ⟨z,?_,?_⟩
  · rintro _ ⟨k,hk,rfl⟩
    apply E.injective
    rw [hE,hr]
    change τ (u*k*u⁻¹) (τ u w) = τ u w
    simp only [map_mul,Module.End.mul_apply,τ.inv_self_apply,hfix k hk]
  · intro hall
    obtain ⟨g,hg⟩ := hn
    have hh := congrArg E (hall (u*g*u⁻¹))
    rw [hE,hr] at hh
    have he : τ g w=w := by
      apply (τ.apply_bijective u).injective
      simpa only [map_mul,Module.End.mul_apply,τ.inv_self_apply] using hh
    exact hg he

/-- A large subgroup of a conjugate Sylow has a displacement fixed by that
whole Sylow and noncentral in the full action, on either central cover. -/
theorem cover_model_large_fixed_displacement
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) S Y)
    (hmodel : SixCover.IsNaturalOrCore ρ (MonoidHom.id _))
    (A : Subgroup S) (u : S)
    (hA : A ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hc : 4 ≤ Nat.card A) :
    ∃ a ∈ A, ∃ z : Y, let r := ρ a z-z
      (∀g∈sylowCarrier.map (MulAut.conj u).toMonoidHom, ρ g r=r) ∧
      ¬ ∀g, ρ g r=r := by
  let B := A.map (MulAut.conj u⁻¹).toMonoidHom
  have hB : B ≤ sylowCarrier := by
    rintro _ ⟨g,hg,rfl⟩
    obtain ⟨k,hk,he⟩ := hA hg
    rw [←he]
    simpa [MulAut.conj_apply,mul_assoc] using hk
  obtain ⟨k,hk⟩ := large_subgroup_actor B hB (by
    dsimp only [B]
    rw [card_map_of_injective (MulAut.conj u⁻¹).injective]
    exact hc)
  have ha : u*actors k*u⁻¹ ∈ A := by
    obtain ⟨a,ha,he⟩ := hk
    have hh := congrArg (MulAut.conj u) he
    have heq : (MulAut.conj u) ((MulAut.conj u⁻¹) a) = a := by
      simp [MulAut.conj_apply,mul_assoc]
    change (MulAut.conj u) ((MulAut.conj u⁻¹) a) = (MulAut.conj u) (actors k) at hh
    rw [heq] at hh
    change a = u*actors k*u⁻¹ at hh
    exact hh ▸ ha
  refine ⟨_,ha,?_⟩
  rcases hmodel with ⟨E,hE⟩ | ⟨E,hE⟩
  · apply witness_transport ρ (naturalRepresentation (Fin 6)) E
      (by simpa only [MonoidHom.id_apply] using hE) (actors k)
      (coreToNatural (Fin 6) (vectors k)) (coreToNatural (Fin 6) (lines k))
      (by simpa only [map_sub,coreToNatural_equivariant] using
        congrArg (coreToNatural (Fin 6)) (core_displacement k))
      (by
        intro g hg
        obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff g).mp hg
        simpa only [coreToNatural_equivariant] using
          congrArg (coreToNatural (Fin 6)) (core_fixed k i))
      _ u
    rw [natural_lines]
    exact ⟨_,TerminalLine.canonical_natural_not_fixed⟩
  · apply witness_transport ρ (coreRepresentation (Fin 6)) E
      (by simpa only [MonoidHom.id_apply] using hE) (actors k) (vectors k) (lines k)
      (core_displacement k) _ ⟨_,core_nonfixed k⟩ u
    intro g hg
    obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff g).mp hg
    exact core_fixed k i

/-- The same displacement is fixed by any containing two-subgroup. -/
theorem cover_model_two_group_fixed_displacement
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) S Y)
    (hmodel : SixCover.IsNaturalOrCore ρ (MonoidHom.id _))
    (A T : Subgroup S) (hAT : A ≤ T) (hT : IsPGroup 2 T)
    (hc : 4 ≤ Nat.card A) :
    ∃ a ∈ A, ∃ z : Y, let r := ρ a z-z
      (∀g∈T, ρ g r=r) ∧ ¬ ∀g, ρ g r=r := by
  obtain ⟨P,hP⟩ := hT.exists_le_sylow
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq S sylow P
  have hTs : T ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom := by
    change T ≤ ((u • sylow : Sylow 2 S) : Subgroup S)
    rwa [hu]
  obtain ⟨a,ha,z,hfix,hn⟩ := cover_model_large_fixed_displacement ρ hmodel A u (hAT.trans hTs) hc
  exact ⟨a,ha,z,fun g hg => hfix g (hTs hg),hn⟩

end SylowFixedLine
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.Marked
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.MarkedOrbitCore

/-!
# Best generation and the marker in the faithful action image

An odd action kernel is injective on every elementary two-subgroup. Pulling
back every subgroup of its image therefore preserves the full best-offender
weight comparison, not merely the ordinary offender inequality. Surjectivity
then transports best generation to the whole faithful image. The same Sylow,
marker and literal subgroup image retain the normalizer condition by coprime
normalizer lifting. No identification of the original actor with its image
is made.

These are the transport steps used by `BestReduction.SourceAssembly` for the
first summand of the line section. Source: Aschbacher–Smith, combined manuscript
of 1 March 2004, B.1.2–4, printed p.68, and 15.3.67, printed pp.1153–1154.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.SourceAssembly
variable {D W : Type*} [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Every subgroup weight comparison survives the actual odd action kernel. -/
theorem best_actionImage (ρ : Representation (ZMod 2) D W)
    (hodd : Odd (Nat.card (actionHom ρ).ker)) {A : Subgroup D}
    (hA : IsBestOffender ρ A) : IsBestOffender (imageRepresentation ρ) (actionSubgroup ρ A) := by
  let : IsElementaryAbelian 2 A := hA.1.2
  have hf := faithful_on_elementaryTwo_of_odd_kernel ρ hodd A
  have hw (B : Subgroup D) (hB : B ≤ A) :
      weight (imageRepresentation ρ) (actionSubgroup ρ B) = weight ρ B := by
    rw [weight, weight, fixedSpace_actionSubgroup,
      actionSubgroup_rank ρ B (fun b hb => hf b (hB hb))]
  refine ⟨hA.1.actionSubgroup ρ hf, ?_⟩
  intro B hB
  let B' := B.comap (actionHom ρ) ⊓ A
  have he : actionSubgroup ρ B' = B := by
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      exact hb.1
    · intro b hb
      obtain ⟨a, ha, he⟩ := hB hb
      exact ⟨a, ⟨show actionHom ρ a ∈ B from he.symm ▸ hb, ha⟩, he⟩
  rw [← he, hw B' inf_le_right, hw A le_rfl]
  exact hA.2 B' inf_le_right

/-- Best generation descends to the entire faithful image of the same actor. -/
theorem generated_actionImage (ρ : Representation (ZMod 2) D W)
    (hodd : Odd (Nat.card (actionHom ρ).ker))
    (hgen : offenderSubgroup ρ = ⊤) : offenderSubgroup (imageRepresentation ρ) = ⊤ := by
  have hle : offenderSubgroup ρ ≤
      (offenderSubgroup (imageRepresentation ρ)).comap (actionHom ρ) := by
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, _⟩
    exact (map_le_iff_le_comap).mp ((best_actionImage ρ hodd hA).le_offenderSubgroup _)
  apply top_unique
  intro a _
  obtain ⟨g, rfl⟩ := ρ.asGroupHom.rangeRestrict_surjective a
  exact hle (hgen ▸ mem_top g)

/-- The original marker and literal subgroup image keep their normalizer condition. -/
noncomputable def marked_actionImage {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J) (hodd : Odd (Nat.card (actionHom ρ).ker)) :
    MarkedNormalizer (imageRepresentation ρ) (actionSubgroup ρ J) where
  sylow := d.sylow.mapSurjective (f := actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective
  subgroup_le_sylow := map_mono d.subgroup_le_sylow
  marker := d.marker
  marker_ne_bot := d.marker_ne_bot
  sylow_fixes := by
    change d.marker ≤ fixedSpace (imageRepresentation ρ) (actionSubgroup ρ d.sylow)
    rw [fixedSpace_actionSubgroup]
    exact d.sylow_fixes
  orbit_span := by
    rw [← orbit_span_comp_surjective (imageRepresentation ρ) (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective d.marker]
    simpa only [imageRepresentation_actionHom] using d.orbit_span
  normalizer_fixes := normalizer_fixes_map_of_coprime_kernel
    (imageRepresentation ρ) (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective hodd J
    (d.sylow.isPGroup'.to_le d.subgroup_le_sylow) d.marker d.normalizer_fixes

omit [Finite D] in
/-- A nontrivial best-generated actor supplies an ordinary offender. -/
theorem ff_of_generated [FiniteDimensional (ZMod 2) W] [Nontrivial D] (ρ : Representation (ZMod 2) D W)
    (hgen : offenderSubgroup ρ = ⊤) : IsFFModule ρ := by
  by_contra hn
  have hz : offenderSubgroup ρ = ⊥ := by
    apply bot_unique
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, _⟩
    exact (hn ⟨A, hA.isOffender ρ⟩).elim
  exact bot_ne_top (hz.symm.trans hgen)
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.SourceAssembly

module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.FlagRestoration
public import CFSG.Quasithin.Chapter5.Section03SymplecticSource.NativeLift

/-!
# Restoring the original nonbinary symplectic pair

Every compatible automorphism of the reduced native pair lifts to Sp₄(F).
Its inner flag stabilizer is the entire Borel. The faithful action of the
original Borel therefore glues across both original endpoints, with the
literal reduced restrictions, to a type-preserving automorphism extension.
Both orientations and all nonbinary characteristic-two fields are retained.

Source: DGS, *Groups and Graphs* (1985), (15.2), printed pp.226–228.
The marked reduced comparison is an explicit earlier recognition input.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.SymplecticNative
open Theory.SpecificGroups.SymplecticFour
variable (F : Type*) [Field F]

def endpoint (point : Bool) : Subgroup (Sp F) :=
  if point then pointParabolic else planeParabolic

theorem borel_le_endpoint (point : Bool) : Theory.SpecificGroups.SymplecticFour.borel (F := F) ≤ endpoint F point := by
  cases point
  · exact inf_le_right
  · exact inf_le_left

def amalgam (point : Bool) : RankTwoAmalgam (endpoint F point)
    (Theory.SpecificGroups.SymplecticFour.borel (F := F)) (endpoint F (!point)) :=
  ofSubgroups _ _ _ (borel_le_endpoint F point) (borel_le_endpoint F (!point))

theorem endpoints_inf (point : Bool) :
    endpoint F point ⊓ endpoint F (!point) = Theory.SpecificGroups.SymplecticFour.borel (F := F) := by
  cases point
  · exact inf_comm _ _
  · rfl

theorem endpoints_generate (point : Bool) :
    endpoint F point ⊔ endpoint F (!point) = ⊤ := by
  cases point
  · exact (sup_comm _ _).trans parabolics_sup_eq_top
  · exact parabolics_sup_eq_top

variable [Finite F] [CharP F 2]

theorem native_lifts {m : ℕ} (hF : Nat.card F = 2^m) (hm : 1 < m) (point : Bool)
    (a : Iso (amalgam F point) (amalgam F point)) :
    ∃ f : Sp F →* Sp F,
      (∀ x : endpoint F point, f (x : Sp F) = (a.left x : Sp F)) ∧
      (∀ x : endpoint F (!point), f (x : Sp F) = (a.right x : Sp F)) := by
  cases point
  · obtain ⟨f,hl,hr⟩ := Chapter5.Section03SymplecticSource.native_amalgam_automorphism
      hF hm a.reverse
    exact ⟨f.toMonoidHom,hr,hl⟩
  · obtain ⟨f,hl,hr⟩ := Chapter5.Section03SymplecticSource.native_amalgam_automorphism hF hm a
    exact ⟨f.toMonoidHom,hl,hr⟩

theorem inner_flag {m : ℕ} (hF : Nat.card F = 2^m) (hm : 1 < m) (point : Bool)
    (g : Sp F)
    (hl : (endpoint F point).map (MulAut.conj g).toMonoidHom = endpoint F point)
    (hr : (endpoint F (!point)).map (MulAut.conj g).toMonoidHom = endpoint F (!point)) :
    g ∈ Theory.SpecificGroups.SymplecticFour.borel (F := F) := by
  apply (SourceNormalizerExtension.inner_flag_iff hF hm g).mp
  cases point
  · exact ⟨hr,hl⟩
  · exact ⟨hl,hr⟩

/-- Restore both full endpoints and their full Borel, preserving every reduced
element through the actual inner embedding. Outer automorphisms remain allowed. -/
theorem exists_original_extension_iso
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) {m : ℕ} (hF : Nat.card F = 2^m) (hm : 1 < m)
    (point : Bool) (e : Iso (reducedAmalgam L S) (amalgam F point)) :
    ∃ E : SourceCompletion.UnitaryNonbinary.SourceExtension
      (endpoint F point) (endpoint F (!point)),
      ∃ f : Iso (originalAmalgam L S) E.amalgam,
        (∀ x : parabolic L (SuzukiContainment.reducedSylow L S) 0,
          (f.left (inclusion (SuzukiContainment.reduced_parabolic_le h 0) x) : MulAut (Sp F)) =
            MulAut.conj (e.left x : Sp F)) ∧
        (∀ x : parabolic L (SuzukiContainment.reducedSylow L S) 1,
          (f.right (inclusion (SuzukiContainment.reduced_parabolic_le h 1) x) : MulAut (Sp F)) =
            MulAut.conj (e.right x : Sp F)) ∧
        (∀ b : commonBorel L (SuzukiContainment.reducedSylow L S),
          (f.middle (inclusion (SuzukiContainment.reduced_commonBorel_le h) b) : MulAut (Sp F)) =
            MulAut.conj (e.middle b : Sp F)) := by
  exact exists_original_extension_of_native_flag h
    (endpoint F point) (endpoint F (!point)) (Theory.SpecificGroups.SymplecticFour.borel (F := F))
    (borel_le_endpoint F point) (borel_le_endpoint F (!point))
    (endpoints_inf F point) (endpoints_generate F point)
    (conj_injective_of_center_eq_bot EvenProjective.center_eq_bot)
    (inner_flag F hF hm point) (native_lifts F hF hm point) e

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.SymplecticNative

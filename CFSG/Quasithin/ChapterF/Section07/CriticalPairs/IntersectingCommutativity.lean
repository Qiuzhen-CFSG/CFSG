module

public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion

/-!
# Intersecting conjugates force an odd critical distance

An even critical pair has nontrivial commutator contained in the intersection
of its two first-type modules. If intersecting conjugates commute, the actual
F.7.11(2) pair therefore cannot have even distance. This is the parity
argument used in 13.8.4 after 13.8.3, with the complete F.7 source setup.
-/

public section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (exists_smul_base)
namespace CFSG.Quasithin.ChapterF.Section07.CriticalPairs
open Track
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

theorem odd_track_of_intersecting_conjugates_commute (D : SourceSetup F) (hne : D.V≠⊥)
    (hcomm : ∀g:G, D.seed ⊓ D.seed.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.seed,D.seed.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    Odd (D.track hne) := by
  apply (Nat.even_or_odd _).resolve_left
  intro heven
  obtain ⟨v,hd,hcrit⟩:=(D.critical_witness hne).1
  have hv:=even_endpoint_type F D hne hd heven
  have hp:=SourceAction.even_critical_pair D hne hd heven hcrit
  obtain ⟨g,hg⟩:=exists_smul_base F v
  rw [hv] at hg
  rw [vertexModule_first F D.seed hv,←hg,firstModule_translate_base F D.seed D.seed_normalized] at hp
  apply hp.1
  apply hcomm g
  intro he
  exact hp.1 (bot_unique (he ▸ hp.2.1))
end CFSG.Quasithin.ChapterF.Section07.CriticalPairs

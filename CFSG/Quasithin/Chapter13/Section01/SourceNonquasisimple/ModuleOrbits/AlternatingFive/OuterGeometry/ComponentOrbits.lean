module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.Stabilizer

/-!
# Component orbit indices on the original A₅ cover

Fixed lifting identifies the stabilizer in L with the pullback of the
natural SL₂(4) stabilizer. Transitivity on the fifteen nonzero natural
vectors gives index fifteen; central vectors have index one.

Source: Aschbacher--Smith, 13.1.12, printed p.872, using I.2.3.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Representation.SL2FourNatural

def naturalStabilizer (v : V) : Subgroup SL :=
  (MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v).comap SL2FourNatural.action

theorem naturalStabilizer_index (v : V) :
    (naturalStabilizer v).index = if v = 0 then 1 else 15 := by
  classical
  by_cases hv : v = 0
  · subst v
    have he : naturalStabilizer 0 = ⊤ := by
      ext l
      change SL2FourNatural.action l 0 = 0 ↔ True
      simp
    rw [he, index_top, if_pos rfl]
  · rw [if_neg hv]
    let ρ : MulAction SL V := MulAction.compHom V SL2FourNatural.action
    have horbit : MulAction.orbit SL v = {w : V | w ≠ 0} := by
      ext w
      rw [MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨l,rfl⟩
        exact (SL2FourNatural.action l).map_ne_zero_iff.mpr hv
      · intro hw
        exact transitive_nonzero v w hv hw
    have hi : (naturalStabilizer v).index = (MulAction.orbit SL v).ncard :=
      @MulAction.index_stabilizer SL V _ ρ v
    rw [hi, horbit]
    change (({(0 : V)} : Set V)ᶜ).ncard = 15
    rw [Set.ncard_compl, Set.ncard_singleton, Nat.card_eq_fintype_card, card_vector]

namespace Marking
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {L : Subgroup G} (d : Marking T L W)

theorem component_centralizer_comap
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) (u : normalizerMoved L) :
    (centralizer ({(u : G)} : Set G)).subgroupOf L =
      (naturalStabilizer (d.projection (d.coordinates u).toAdd)).comap d.component := by
  ext l
  change (l : G) ∈ centralizer ({(u : G)} : Set G) ↔
    Natural (d.component l) (d.projection (d.coordinates u).toAdd) =
      d.projection (d.coordinates u).toAdd
  rw [← d.component_fixes_iff]
  exact (d.naturalCover hmoved).fixed_iff_natural_fixed (d.component l) (d.coordinates u).toAdd

theorem component_centralizer_index
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) (u : normalizerMoved L) :
    (centralizer ({(u : G)} : Set G)).relIndex L =
      if d.projection (d.coordinates u).toAdd = 0 then 1 else 15 := by
  change ((centralizer ({(u : G)} : Set G)).subgroupOf L).index = _
  rw [d.component_centralizer_comap hmoved u,
    index_comap_of_surjective _ d.onto, naturalStabilizer_index]

end Marking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive

module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FaithfulSection

/-!
# The radius--moving commutator lower bound

An actor outside Q moves the faithful natural subgroup U nontrivially. It
also moves the natural section of V/Z, so [V,J] cannot be contained in Z.
The nontrivial subgroup [U,J] is therefore proper in [V,J]. The latter is
a finite two-group, forcing its order to be at least four.

The imported actor_le_Q is the elementary faithfulness lemma conditional
only on the actual natural section and local generation; it uses none of
(4.3.2)'s conclusions. Applying it to the endpoint-side moving group gives
source (4.3.1)(vi), already for b > 2.

Source: Meierfrankenfeld--Stellmacher (1993), p.883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Consequences
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- Two faithful layers force a nontrivial local actor to displace at least
four elements of the radius group. -/
theorem commutator_card_four_of_not_le_Q (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false)
    (s : NaturalSectionAt a (V R a) (Z R a))
    (J : Subgroup (FreeAmalgam R)) (hJ : J ≤ stabilizer R a) (hout : ¬ J ≤ Q R a) :
    4 ≤ Nat.card (⁅V R a, J⁆ : Subgroup (FreeAmalgam R)) := by
  let K := ⁅V R a, J⁆
  let D := ⁅U R a, J⁆
  have hKV : K ≤ V R a := le_normalizer_iff_commutator_le_left.mp
    (hJ.trans (V_normalized a))
  have hDU : D ≤ U R a := le_normalizer_iff_commutator_le_left.mp
    (hJ.trans (U_normalized a))
  have hDK : D ≤ K := commutator_mono ((U_le_Z a).trans (Z_le_VBall R a 2)) le_rfl
  let := finite_stabilizer R a
  let : Finite K := Finite.of_injective (inclusion (hKV.trans s.local_group))
    (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDK) (inclusion_injective _)
  have hDne : D ≠ ⊥ := by
    intro h
    apply hout
    rw [← modules.natural.centralizer a ha]
    exact le_inf hJ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h))
  have hDcard : 2 ≤ Nat.card D := (one_lt_card_iff_ne_bot D).mpr hDne
  have hp : IsPGroup 2 K := (source.V_isPGroup geometry hb a ha).to_le hKV
  by_contra! hsmall
  have hKtwo : Nat.card K ≤ 2 := by
    change Nat.card K < 4 at hsmall
    rcases hp.card_eq_or_dvd with h | h
    · omega
    · obtain ⟨n, hn⟩ := h
      omega
  have heq : D = K := eq_of_le_of_card_ge hDK (hKtwo.trans hDcard)
  have hKZ : K ≤ Z R a := heq ▸ hDU.trans (U_le_Z a)
  exact hout (PairingControl.actor_le_Q source ha s J hJ
    ((commutator_mono (Vcirc_le_V a) le_rfl).trans hKZ))

/-- Source (4.3.1)(vi), using the same specified predecessor as p. -/
theorem radius_moving_card (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry)
    (hsections : ∀ q : Counterexample geometry, Nonempty (SectionFacts q)) :
    4 ≤ Nat.card (⁅V R p.a, Vcirc R p.c⁆ : Subgroup (FreeAmalgam R)) := by
  obtain ⟨s⟩ := hsections p
  exact commutator_card_four_of_not_le_Q source hb modules p.a p.color_a s.natural_section
    (Vcirc R p.c) (endpoint_moving_local p) (endpoint_moving_not_le source p hb)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Consequences

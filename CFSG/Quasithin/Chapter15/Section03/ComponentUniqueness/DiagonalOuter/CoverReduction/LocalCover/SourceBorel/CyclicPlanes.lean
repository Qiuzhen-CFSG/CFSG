module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.CyclicPlanes.Model
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.CyclicPlanes.Transport

/-!
# Orienting a cyclic actor on the two original natural planes

Let A ≤ M be two-perfect, normalized by S = N_T(V₁), with
|A/O₂(A)| = 3 and [V,A] nontrivial. The compatible natural orthogonal
action has nontrivial cyclic image in its order-nine base subgroup.
S-invariance forces that image onto one coordinate axis. Relabeling only
the two original planes gives A ≤ C(W₁) and [V,A] = [W₂,A] = W₂.

The surjective actor map carries the specified Sylow subgroup T to a
Sylow subgroup of the literal wreath product. Lifting a swapping element
there supplies t ∈ T which preserves S and interchanges both W₁ and W₂.
No component, Borel, projective marking, or orientation is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), natural
planes on printed pp.1121--1122, local conventions on pp.1123--1125,
and the cyclic actor argument in the first paragraph of p.1136.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
variable {G : Type*} [Group G] [Finite G]

/-- An element of the specified Sylow interchanges both original planes and preserves S. -/
theorem cyclic_sylow_interchange (d : CharacteristicTwo.LocalData G) :
    ∃ t ∈ (d.T : Subgroup G),
      d.S.map (MulAut.conj t).toMonoidHom = d.S ∧
      d.V₁.map (MulAut.conj t).toMonoidHom = d.V₂ ∧
      d.V₂.map (MulAut.conj t).toMonoidHom = d.V₁ := by
  let P := (d.T.subtype d.sylow_le).mapSurjective d.action.onto
  obtain ⟨t, ht, hn⟩ := CyclicModel.exists_shift P
  change t ∈ (d.T.subtype d.sylow_le : Subgroup d.M).map d.action.actor at ht
  obtain ⟨t, ht, rfl⟩ := ht
  have htT : (t : G) ∈ (d.T : Subgroup G) := ht
  have hshift : (d.action.actor t).right = Multiplicative.ofAdd (1 : ZMod 2) := by
    have hh : ∀ i : OrthogonalPlaneIndex, i ≠ 1 →
        i = Multiplicative.ofAdd (1 : ZMod 2) := by decide +kernel
    exact hh _ hn
  refine ⟨t, htT, cyclic_sylow_preserves_stabilizer d t htT, ?_, ?_⟩
  · change (d.action.plane 1).map (MulAut.conj (t : G)).toMonoidHom = _
    rw [cyclic_plane_map, hshift, mul_one]
  · change (d.action.plane (Multiplicative.ofAdd (1 : ZMod 2))).map
      (MulAut.conj (t : G)).toMonoidHom = _
    rw [cyclic_plane_map, hshift]
    exact congrArg d.action.plane (show Multiplicative.ofAdd (1 : ZMod 2) *
      Multiplicative.ofAdd (1 : ZMod 2) = 1 by decide)

private theorem cyclic_actor_card (d : CharacteristicTwo.LocalData G) (A : Subgroup G)
    (hAM : A ≤ d.M) (hA : IsPPerfect 2 A)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) (hn : ⁅d.V, A⁆ ≠ ⊥) :
    Nat.card (d.action.actor.comp (inclusion hAM)).range = 3 := by
  let f := d.action.actor.comp (inclusion hAM)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
    (CyclicModel.range_card_dvd_three f hA hc) with h | h
  · have hb : f.range = ⊥ := f.range.eq_bot_of_card_eq h
    have hAV : A ≤ centralizer (d.V : Set G) := by
      intro a ha
      have he : f ⟨a, ha⟩ = 1 := by
        have hm : f ⟨a, ha⟩ ∈ f.range := ⟨_, rfl⟩
        rwa [hb] at hm
      have hm : inclusion hAM ⟨a, ha⟩ ∈ d.action.actor.ker := he
      rw [d.action.ker_actor] at hm
      exact hm
    exact False.elim (hn (by
      rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
      exact hAV))
  · exact h

/-- A two-perfect cyclic actor normalized by S acts on exactly one of the two
original natural planes. The choices include an actual interchange in T. -/
theorem cyclicPlaneChoice_of_card_quotient_three (d : CharacteristicTwo.LocalData G)
    (A : Subgroup G) (hAM : A ≤ d.M) (hA : IsPPerfect 2 A)
    (hSA : d.S ≤ normalizer (A : Set G))
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) (hn : ⁅d.V, A⁆ ≠ ⊥) :
    Nonempty (CyclicPlaneChoice d A) := by
  let f := d.action.actor.comp (inclusion hAM)
  let P := (d.T.subtype d.sylow_le).mapSurjective d.action.onto
  have hbase := CyclicModel.range_le_cubeBase f hA
  have hcard := cyclic_actor_card d A hAM hA hc hn
  have hrange : f.range = (A.subgroupOf d.M).map d.action.actor := by
    rw [MonoidHom.range_comp, inclusion_range]
  have hnorm : ∀ s ∈ (P : Subgroup OrthogonalActor), s.right = 1 →
      s ∈ normalizer (f.range : Set OrthogonalActor) := by
    intro s hs hshift
    change s ∈ (d.T.subtype d.sylow_le : Subgroup d.M).map d.action.actor at hs
    obtain ⟨s, hs, rfl⟩ := hs
    have hsS : (s : G) ∈ d.S :=
      ⟨hs, (cyclic_mem_plane_normalizer_iff d.action s 1).mpr hshift⟩
    have hsn : s ∈ normalizer (A.subgroupOf d.M : Set d.M) :=
      le_normalizer_comap d.M.subtype (hSA hsS)
    rw [hrange]
    exact le_normalizer_map d.action.actor ⟨s, hsn, rfl⟩
  obtain ⟨i, hi⟩ := CyclicModel.axis_of_sylow_normalized P f.range hbase hcard hnorm
  have hs : ∀ a : A, (d.action.actor (inclusion hAM a)).right = 1 :=
    fun a => (hbase ⟨a, rfl⟩).1
  have hcube : ∀ a : A, ∀ j, ((d.action.actor (inclusion hAM a)).left j) ^ 3 = 1 :=
    fun a => (hbase ⟨a, rfl⟩).2
  have hfix : ∀ a : A, (d.action.actor (inclusion hAM a)).left i = 1 :=
    fun a => hi _ ⟨a, rfl⟩
  obtain ⟨t, ht, hS, h₁, h₂⟩ := cyclic_sylow_interchange d
  have hi_cases : i = 1 ∨ i = Multiplicative.ofAdd (1 : ZMod 2) := by
    have h : ∀ i : OrthogonalPlaneIndex, i = 1 ∨
        i = Multiplicative.ofAdd (1 : ZMod 2) := by decide +kernel
    exact h i
  rcases hi_cases with rfl | rfl
  · have hcomm := cyclic_commutator_eq_plane d.action hAM 1
      (Multiplicative.ofAdd (1 : ZMod 2)) (by decide) hs
      (fun a => hcube a _) hfix hn
    exact ⟨{ W₁ := d.V₁, W₂ := d.V₂, planes := Or.inl ⟨rfl, rfl⟩
             centralizes := cyclic_centralizes_plane d.action hAM 1 hs hfix
             commutator := hcomm.1, moves := hcomm.2
             t := t, t_mem := ht, sylow_invariant := hS
             first_interchange := h₁, second_interchange := h₂ }⟩
  · have hcomm := cyclic_commutator_eq_plane d.action hAM
      (Multiplicative.ofAdd (1 : ZMod 2)) 1 (by decide) hs
      (fun a => hcube a _) hfix hn
    exact ⟨{ W₁ := d.V₂, W₂ := d.V₁, planes := Or.inr ⟨rfl, rfl⟩
             centralizes := cyclic_centralizes_plane d.action hAM
               (Multiplicative.ofAdd (1 : ZMod 2)) hs hfix
             commutator := hcomm.1, moves := hcomm.2
             t := t, t_mem := ht, sylow_invariant := hS
             first_interchange := h₂, second_interchange := h₁ }⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel

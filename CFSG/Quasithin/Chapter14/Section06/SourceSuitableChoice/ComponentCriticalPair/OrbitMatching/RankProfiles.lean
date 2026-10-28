module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.OrbitMatching.CommutatorImages
public import Theory.Representation.BinaryNaturalDual.LowRankProfiles.Sections
public import Theory.Representation.BinaryConjugationSection.DualHyperplaneMovement
public import Theory.Representation.PSL3Two.LowRankProfiles

/-!
# Marked low-rank profiles at the original critical pair

The literal natural--dual action supplies singular commutator images and a
pure vector, including the fixed factor of U/Z. The existing local orbit
argument then constructs the specified crossing in both symmetric ranks.
For a denominator of index two, the dual displacement bound forces movement
on one original support, giving the asymmetric contradiction.

The actual section markings, component placement and selected-endpoint
containments remain explicit earlier-source inputs. No commutator profile,
common pure vector, ambient fusion, crossing or outside-centralizer premise
is assumed. This is a consumer of the model calculations, not an unconditional
proof of 14.6.24. Final endpoint selection belongs to its assembly owner.

Source: Aschbacher--Smith, 14.6.24(4), printed p.1041.
-/

public section
open Subgroup Theory.GroupTheory Representation
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.OrbitMatching
private instance : Finite (BinaryLinear.GL (Fin 3 → ZMod 2)) :=
  Finite.of_injective (fun g : BinaryLinear.GL (Fin 3 → ZMod 2) =>
    (g : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))) DFunLike.coe_injective

variable {G : Type*} [Group G] [Finite G]
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (W W' : Subgroup G)
    (f : (Mc ⊓ normalizer (W : Set G) : Subgroup G) →*
      BinaryLinear.GL (Fin 3 → ZMod 2)) (hf : Function.Surjective f)
    (c : BinaryConjugationSection (Mc ⊓ normalizer (W : Set G)) W (centralInvolutions T)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (s : G) (hs : s ∈ Mc) (hsW : W.map (MulAut.conj s).toMonoidHom = W')
    (u : G) (huW : u ∈ W)
    (hu : ComponentSupports.Suitable
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u)


section Symmetric
variable
    (K B : Subgroup G) (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hBU : B ≤ conjugateSpanBy (localModule T M) Mc)
    (φ : K →* BinaryLinear.GL (Fin 3 → ZMod 2)) (hφ : Function.Surjective φ)
    (d : BinaryConjugationSection K B (centralInvolutions T) (naturalDualRepresentation.comp φ))
    (hW : ∀ v : B, (v : G) ∈ W ↔ (d.coordinates v).toAdd.2 = 0)
    (hW' : ∀ v : B, (v : G) ∈ W' ↔ (d.coordinates v).toAdd.1 = 0)
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint)

local notation "U" => conjugateSpanBy (localModule T M) Mc
local notation "Z" => centralInvolutions T
local notation "R" => ⁅U,i.conjugate U⁆

local notation "A" => i.conjugate U
local notation "A'" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj i.representative⁻¹)) U

include hf c hs hsW huW hu hK hBU hφ d hW hW' in
/-- Both symmetric ranks feed the orbit consumer directly from the marked
quadratic action; the singular profiles and common pure lift are proved.
The actor may lie in a larger support normalizer L than the component K;
its section uses the very same quotient coordinates. -/
theorem source_crossing_of_marked_quadratic_actions
    (L C : Subgroup G)
    (ψ : L →* BinaryLinear.GL (Fin 3 → ZMod 2))
    (dL : BinaryConjugationSection L B Z (naturalDualRepresentation.comp ψ))
    (hcoordinates : ∀ b : B, dL.coordinates b = d.coordinates b)
    (hcover : ∀ v ∈ U, ∃ b ∈ B, ∃ t ∈ C, v = b * t)
    (hAL : A ≤ L) (hAL' : A' ≤ L)
    (hfixed : ⁅A,C⁆ ≤ Z) (hfixed' : ⁅A',C⁆ ≤ Z)
    (hA : Representation.BinaryOffender.IsElementaryTwo (((A).subgroupOf L).map ψ))
    (hA' : Representation.BinaryOffender.IsElementaryTwo (((A').subgroupOf L).map ψ))
    (hRB : R ≤ B) (hRBg : R ≤ i.conjugate B) (hZR : i.conjugate Z ≤ R) :
    ∃ x ∈ Mc, ∃ k : G,
      k = x⁻¹ * i.representative ∧
      (∀ L : Subgroup G, L.map (MulAut.conj k).toMonoidHom =
        (i.conjugate L).map (MulAut.conj x⁻¹).toMonoidHom) ∧
      ∃ q : SourceCrossingGeometry (localModule T M) Mc Mc u,
        q.A = U ∧ q.g = k ∧ ¬ centralizer ({u} : Set G) ≤ Mc := by
  have he : (A).map (MulAut.conj i.representative⁻¹).toMonoidHom = U := by
    rw [Subgroup.map_map]
    have hid : (MulAut.conj i.representative⁻¹).toMonoidHom.comp
        (MulAut.conj i.representative).toMonoidHom = MonoidHom.id G := by
      ext v
      simp [MulAut.conj_apply,mul_assoc]
    rw [hid,Subgroup.map_id]
  have hrev : (R).map (MulAut.conj i.representative⁻¹).toMonoidHom = ⁅A',U⁆ := by
    rw [map_commutator,he]
  have hAA : ⁅A,A⁆ = ⊥ := by
    rw [← map_commutator,commutator_self_eq_bot_iff.mpr hab,Subgroup.map_bot]
  have hAA' : ⁅A',A'⁆ = ⊥ := by
    rw [← map_commutator,commutator_self_eq_bot_iff.mpr hab,Subgroup.map_bot]
  have hRA : ⁅A,B⁆ ≤ A := by
    have hc : ⁅A,B⁆ ≤ R := by
      rw [commutator_comm U A]
      exact commutator_mono le_rfl hBU
    exact hc.trans (hRBg.trans (map_mono hBU))
  have hRA' : ⁅A',B⁆ ≤ A' := by
    have hc : ⁅A',U⁆ ≤ A' := by
      rw [← hrev]
      exact map_mono (hRB.trans hBU)
    exact (commutator_mono le_rfl hBU).trans hc
  have hquad : ⁅A,⁅A,B⁆⁆ ≤ Z :=
    (commutator_mono le_rfl hRA).trans (hAA.le.trans bot_le)
  have hquad' : ⁅A',⁅A',B⁆⁆ ≤ Z :=
    (commutator_mono le_rfl hRA').trans (hAA'.le.trans bot_le)
  have himages (S : Subgroup G) : dL.imageSpace S = d.imageSpace S := by
    ext v
    rw [dL.mem_imageSpace_iff,d.mem_imageSpace_iff]
    simp only [hcoordinates]
  have hp := LowRankProfiles.section_profile_of_fixed_extension ψ dL A U C
    hAL hBU hcover hfixed hA hquad
  rw [himages] at hp
  rw [commutator_comm A U] at hp
  have hp' := LowRankProfiles.section_profile_of_fixed_extension ψ dL A' U C
    hAL' hBU hcover hfixed' hA' hquad'
  rw [himages] at hp'
  apply source_crossing_of_symmetric_commutator_images hG T hempty hM hunique hmany
    hcard e hab W W' f hf c s hs hsW u huW hu K B hK hBU φ hφ d hW hW' i
    hRB hRBg hZR hp.1 _ hp.2
  rw [hrev]
  exact hp'.1

end Symmetric

include hf c hs hsW huW hu in
/-- The literal denominator of index at most two supplies the asymmetric
movement premise; the two fixed-hyperplane assumptions are contradicted
by the rank of its actual natural action. -/
theorem source_false_of_rank_two_denominator_index_two
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint)
    (cdual : BinaryConjugationSection (Mc ⊓ normalizer (W : Set G)) W'
      (centralInvolutions T) (LowRankProfiles.natural.dual.comp f))
    (hWU : W ≤ conjugateSpanBy (localModule T M) Mc)
    (hW'U : W' ≤ conjugateSpanBy (localModule T M) Mc)
    (hAH : i.conjugate (conjugateSpanBy (localModule T M) Mc) ≤
      Mc ⊓ normalizer (W : Set G))
    (hZD : centralInvolutions T ≤ conjugateSpanBy (localModule T M) Mc ⊓
      i.conjugate (Mc.pCoreIn 2))
    (hindex : (conjugateSpanBy (localModule T M) Mc ⊓ i.conjugate (Mc.pCoreIn 2)).relIndex
      (conjugateSpanBy (localModule T M) Mc) ≤ 2)
    (hrank : 2 ≤ Representation.BinaryOffender.rank
      (((i.conjugate (conjugateSpanBy (localModule T M) Mc)).subgroupOf
        (Mc ⊓ normalizer (W : Set G))).map f)) : False := by
  let U := conjugateSpanBy (localModule T M) Mc
  let D := U ⊓ i.conjugate (Mc.pCoreIn 2)
  have hm := BinaryConjugationSection.moves_one_of_dual_hyperplanes
    (Mc ⊓ normalizer (W : Set G)) U (centralInvolutions T) (i.conjugate U) D W W'
    LowRankProfiles.natural LowRankProfiles.natural_injective f c cdual
    hWU hW'U hZD hindex hrank
  rcases hm with hm | hm
  · exact source_false_of_moving_denominator_support hG T hempty hM hunique hmany
      hcard e hab W W' f hf c s hs hsW u huW hu i W (Or.inl rfl)
      (hAH.trans c.normalized) hm
  · exact source_false_of_moving_denominator_support hG T hempty hM hunique hmany
      hcard e hab W W' f hf c s hs hsW u huW hu i W' (Or.inr rfl)
      (hAH.trans cdual.normalized) hm

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.OrbitMatching

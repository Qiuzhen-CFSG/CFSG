module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroNormalizerAction
public import CFSG.Quasithin.Chapter10.SourceA5ZeroNormalizerEndgame
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralEnlargements
public import Theory.GroupTheory.DihedralFourElementaryAmbient
public import Theory.SpecificGroups.SymmetricFour.CorePreimageAction
/-!
# Normalizer control in the original zero-center alternating-five branch

The original Baumann subgroup is a product of four dihedral groups. Its
canonical central enlargements give a permutation action with Sylow image
of order eight. The kernel fixes the original module, and an escaping
normalizer would therefore induce S₄. The Sylow preimage of its normal
four-group fixes only two maximum elementary subgroups. Sylow index and
Frattini then force the full normalizer to fix the original module, a
contradiction. Every marking, order and geometric premise is discharged
from the original fundamental setup.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher DihedralProductCanonical
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false
/-- The zero-center branch of the original A₅ Baumann normalizer theorem. -/
theorem source_a5_zero_baumann_normalizer_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal := by
  by_contra hout
  let S := ChapterB.baumann (T : Subgroup G)
  let N := normalizer (S : Set G)
  obtain ⟨eR,_,_,hTF,hcard,hspan,_⟩ := source_a5_zero_central_enlargements D e hn hout hz
  let F := ambientGamma S eR
  let f := normalizerFactorAction S eR
  have hTN : (T : Subgroup G) ≤ N := (T : Subgroup G).le_normalizer.trans
    (normalizer_le_normalizer_baumann (T : Subgroup G))
  have hc : ∀ i, Nat.card (D.moduleSubgroup ⊓ F i : Subgroup G) =
      4 * Nat.card (Remainder i) := by
    intro i
    rw [remainder_card]
    exact hcard i
  have himage : Nat.card (((T : Subgroup G).subgroupOf N).map f) = 8 :=
    source_a5_zero_factorAction_image_card D e hn hout hz eR
  have hsurj : Function.Surjective f := source_a5_zero_normalizer_action_surjective D
    e hn hout hz F Remainder (ambientGammaEquiv S eR) hTF hc hspan f
    (map_ambientGamma S eR) himage
  let Rn := ((T : Subgroup G).subgroupOf N) ⊓ (pCore 2 (Equiv.Perm (Fin 4))).comap f
  let R := Rn.map N.subtype
  have hRT : R ≤ (T : Subgroup G) := by
    rintro _ ⟨n,hn,rfl⟩
    exact hn.1
  have hRN : R ≤ normalizer (S : Set G) := hRT.trans hTN
  have htrans : ∀ i j : Fin 4, ∃ r : R,
      normalizerFactorAction S eR (inclusion hRN r) i = j := by
    intro i j
    obtain ⟨n,hn,he⟩ := sylow_core_preimage_transitive (T.subtype hTN) f hsurj i j
    exact ⟨⟨n,⟨n,hn,rfl⟩⟩,he⟩
  have hV := source_a5_zero_module_maximum_elementary D e hn hout hz
  obtain ⟨A,_,_,_,hpair⟩ := DihedralFourChoices.two_normalized_maximum_subgroups
    S R D.moduleSubgroup eR hRN htrans hV (hRT.trans D.sylow_normalizes_module)
  exact source_a5_zero_normalizer_contradiction_of_gamma_geometry D e hn hout hz
    F Remainder (ambientGammaEquiv S eR) hTF hc hspan f (map_ambientGamma S eR)
    himage hV A hpair
end CFSG.Quasithin.Chapter10

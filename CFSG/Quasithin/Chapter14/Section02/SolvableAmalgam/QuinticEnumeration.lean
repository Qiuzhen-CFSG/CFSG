module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FullReeExclusion
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.IndexFiveStructure
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalRigidity.Tits
public import Theory.GroupTheory.Amalgam.EndpointRecognition

/-!
# Assembling the marked quintic pair from its endpoint identifications

The original source identifies the whole intersection H ∩ YT with T.
Sylow conjugacy therefore constructs the middle-group isomorphism from
the endpoint isomorphisms. The proved Tits restriction calculation removes
the overlap twist and supplies both commuting inclusion squares.

The full Ree first endpoint is already excluded by the original centralizer
argument, independently of the second endpoint. Thus final enumeration
requires two structural inputs: the first endpoint alternatives, and the
cubic endpoint identification conditional on the surviving Tits first one.
Those inputs remain explicit here; this module does not yet establish
the unconditional F.1.12 enumeration.

Source: Aschbacher--Smith F.1.11--12, pp.262--264, and14.2.20--21,
pp.988--989. The Tits quotient is the corrected Sz(2).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original Sylow overlap and two endpoint identifications suffice for
the compatible Tits marking, including both whole-intersection maps. -/
theorem source_quintic_tits_of_endpoint_equivalences
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : Tits.ExceptionalParabolics.first ≃* H)
    (eX : Tits.ExceptionalParabolics.second ≃*
      (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G)) :
    ChapterF.GreenBook.IsAtlasTitsAmalgam
      (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
        (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right) := by
  have hq := source_index_five_models hG T hempty hM hu hmany hcard e H hH.1 hi
  have hsmall : SmallSolvableModel (H ⧸ pCore 2 H) :=
    hq.elim Or.inl (fun h => Or.inr (Or.inl h))
  have hpair := source_hypothesis_F_1_1 hG T hempty hM hu hmany hcard e H hH hsmall
  have hα := RankTwoAmalgam.sylowEmbedded_ofSubgroups T H _ _
    inf_le_left inf_le_right hpair.2.1
  have hβ := RankTwoAmalgam.sylowEmbedded_ofSubgroups Tits.atlas1600SylowTwo
    _ _ _ inf_le_left inf_le_right
    (Tits.ExceptionalParabolics.overlap_eq_sylow.trans Tits.atlas1600SylowTwo_coe.symm)
  obtain ⟨p⟩ := RankTwoAmalgam.parabolicEquiv_of_endpoints hα hβ eH.symm eX.symm
  exact ChapterF.GreenBook.ExceptionalRigidity.tits_of_parabolicEquiv hα p

/-- First-endpoint enumeration and the conditional second-endpoint theorem
give the exact requested marked alternatives. Their structural premises
are separate outstanding obligations, rather than a marked-enumeration field. -/
theorem source_quintic_enumeration_of_endpoint_identifications
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hfirst : Nonempty (Tits.ExceptionalParabolics.FullRee.first ≃* H) ∨
      Nonempty (Tits.ExceptionalParabolics.first ≃* H))
    (hsecond : Nonempty (Tits.ExceptionalParabolics.first ≃* H) →
      Nonempty (Tits.ExceptionalParabolics.second ≃*
        (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G))) :
    ChapterF.GreenBook.IsBinaryReeAmalgam
      (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
        (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right) ∨
    ChapterF.GreenBook.IsAtlasTitsAmalgam
      (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
        (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right) := by
  rcases hfirst with hfull | htits
  · exact (source_full_ree_parabolic_exclusion hG T hempty hM hu hmany hcard e
      H hH hfull).elim
  · obtain ⟨eX⟩ := hsecond htits
    exact Or.inr (source_quintic_tits_of_endpoint_equivalences hG T hempty hM hu
      hmany hcard e H hH hi htits.some eX)

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam

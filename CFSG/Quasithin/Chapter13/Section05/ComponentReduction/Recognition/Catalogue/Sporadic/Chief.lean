module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.Sporadic
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.Sections

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 3000000
set_option linter.style.haveILetI false

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open Sporadic.Mathieu
open CFSG.Quasithin.Chapter13.Section08.Source
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source

namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue

universe u v

variable {G : Type u} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (K : Subgroup G)

variable (h : D.Hypothesis)
  [hN : (D.V₁.subgroupOf D.UH).Normal] [hEA : IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- Application of the code-row exclusion to the literal chief section.  The
marked element is the original actor element `v`; `actionHom` records its
passage to the faithful action image, while `p` and `hseed` retain the source
marked plane and quotient section. -/
theorem chief_m22_code_row_contradiction
    (s : Selected D K)
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (v : actor D K) (hv : zpowers (v : Hstar D.H) = starImage D.H D.V)
    (hv2 : v ^ 2 = 1)
    (p : MovedPlane (representation D K h) (localActor D K) v)
    (hseed : p.plane.toSubmodule = Action.seedSpace D)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (action : ActionEquiv
      ((imageRepresentation (chiefRepresentation D K h U N)).comp
        (generalizedFitting (actionImage (chiefRepresentation D K h U N))).subtype)
      MathieuCode.m22CodeRepresentation)
    (ambient : Nonempty (Representation.Equiv
      (imageRepresentation (chiefRepresentation D K h U N))
      (simpleCodeAmbientRepresentation
        (generalizedFitting (actionImage (chiefRepresentation D K h U N)))
        action.groupEquiv inferInstance))) : False := by
  let σ := chiefRepresentation D K h U N
  let ρ := imageRepresentation σ
  let t := actionHom σ v
  have hdisp0 := (noncentral_section_plane D K h s hcard heven v hv p hseed U N hn).2.1
  have hdisp : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) = 2 := by
    change Module.finrank (ZMod 2)
      (LinearMap.range (imageRepresentation σ (actionHom σ v) - 1)) = 2
    rw [imageRepresentation_actionHom]
    exact hdisp0
  have ht : t ^ 2 = 1 := by
    change (actionHom σ v) ^ 2 = 1
    calc
      (actionHom σ v) ^ 2 = actionHom σ (v ^ 2) := (map_pow (actionHom σ) v 2).symm
      _ = actionHom σ 1 := by rw [hv2]
      _ = 1 := map_one (actionHom σ)
  obtain ⟨ambient⟩ := ambient
  exact m22_code_row_contradiction ρ
    (generalizedFitting (actionImage σ)) action.groupEquiv
    (imageRepresentation_injective σ) ambient t ht hdisp

/-- Application of the genuine triple-cover exclusion to the literal chief
section.  The center and quotient maps are the row's actual data; the local
section maps and selected component remain unchanged. -/
theorem chief_triple_m22_row_contradiction
    {𝒦 : GroupClass.{u}}
    (s : Selected D K)
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (v : actor D K) (hv : zpowers (v : Hstar D.H) = starImage D.H D.V)
    (hv2 : v ^ 2 = 1)
    (p : MovedPlane (representation D K h) (localActor D K) v)
    (hseed : p.plane.toSubmodule = Action.seedSpace D)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (hB4 : B4Hypotheses 𝒦 (imageRepresentation (chiefRepresentation D K h U N)))
    (centerEquiv : center (generalizedFitting
      (actionImage (chiefRepresentation D K h U N))) ≃* Multiplicative (ZMod 3))
    (quotientEquiv :
      (generalizedFitting (actionImage (chiefRepresentation D K h U N)) ⧸
        center (generalizedFitting (actionImage (chiefRepresentation D K h U N)))) ≃* M22)
    (hd : Module.finrank (ZMod 2)
      (N.toSubmodule ⧸ (sectionLower (representation D K h) U N).toSubmodule) = 12) : False := by
  let σ := chiefRepresentation D K h U N
  let ρ := imageRepresentation σ
  let L := generalizedFitting (actionImage σ)
  let t := actionHom σ v
  haveI : L.Normal := inferInstance
  haveI : Finite L := inferInstance
  haveI : Fintype L := Fintype.ofFinite L
  haveI : Fintype (center L) := Fintype.ofFinite (center L)
  haveI : IsQuasisimple L := hB4.quasisimple
  haveI : Representation.IsIrreducible (ρ.comp L.subtype) := hB4.irreducible
  have hdisp0 := (noncentral_section_plane D K h s hcard heven v hv p hseed U N hn).2.1
  have hdisp : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) = 2 := by
    change Module.finrank (ZMod 2)
      (LinearMap.range (imageRepresentation σ (actionHom σ v) - 1)) = 2
    rw [imageRepresentation_actionHom]
    exact hdisp0
  have ht : t ^ 2 = 1 := by
    change (actionHom σ v) ^ 2 = 1
    calc
      (actionHom σ v) ^ 2 = actionHom σ (v ^ 2) := (map_pow (actionHom σ) v 2).symm
      _ = actionHom σ 1 := by rw [hv2]
      _ = 1 := map_one (actionHom σ)
  have hfaith : Function.Injective ρ := imageRepresentation_injective σ
  have hc : Nat.card (center L) = 3 := by
    have hc' := Nat.card_congr centerEquiv.toEquiv
    simpa [L] using hc'
  obtain ⟨e⟩ := M22TripleCover.nonempty_mulEquiv hc ⟨quotientEquiv⟩
  exact triple_m22_row_contradiction ρ L e hfaith
    hd t ht hdisp


end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue

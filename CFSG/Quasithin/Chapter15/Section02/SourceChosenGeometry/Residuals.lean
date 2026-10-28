module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Inputs
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Wreath
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.PrimeComplement
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.KernelIdentity
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Orbit
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Components

/-!
# Residual recognition and centralization for the chosen source plane

The actual wreath quotient proves membership of the embedded O²(H) in Xi.
The original ambient Sylow then supplies the full local embedding input in
Mc. Component detection identifies the actual Mc-normal closure, including
relative normality and the same complement's commutator identity.

Every detected component belongs to L* by original 14.1.6 and centralizes
the original central involutions. Its T-orbit does too. Thus centralization
of Kc is proved even before the additional invariant model sieve and the
ambient Held exclusion. The adequate intrinsic alternatives deliberately
retain Held; they are not claimed as the short list in 15.2.12(2).
The prime-complement residual equality and proper-support exclusion also
remain separate mathematical obligations.

Source: Aschbacher--Smith 15.2.12, printed p.1111, using 1.3.4 and
14.1.6, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Chapter1 Chapter1.XiEmbedding Section01 Section03.InitialSource ChapterA.Section05To06
open Section03 ChapterD ChapterD.UniqueFactor
open Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- The distinguished partner really contains the original full Sylow. -/
theorem partner_mem_overgroups (h : ChosenSmallSource T M Mc V) :
    Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G) := by
  have hm : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton Mc
  refine ⟨hm.1, le_trans ?_ hm.2⟩
  intro t ht z hz
  exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 t ht).symm

/-- The actual source family equality, with universal A and C discharged. -/
theorem source_component_families (h : ChosenSmallSource T M Mc V) :
    LStar G (T : Subgroup G) = cComponentsIn Mc :=
  maximal_local_components_eq
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    h.ambient T h.empty (partner_mem_overgroups h) h.partner

/-- The literal chosen outside residual satisfies every clause of Xi. -/
theorem ResidualInput.mem_Xi {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) : residual H ∈ Xi G (T : Subgroup G) := by
  obtain ⟨e⟩ := d.quotient
  exact residual_mem_Xi_of_wreath d.outside.1.1.2 d.outside.1.1.1 e

/-- The original H is the join of its residual and the fixed Sylow. -/
theorem ResidualInput.residual_join {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) : residual H ⊔ (T : Subgroup G) = H := by
  have hTH : (T : Subgroup G) ≤ H := d.outside.1.1.2
  have he := congrArg (map H.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [Subgroup.map_sup, Sylow.coe_subtype,
    map_subgroupOf_eq_of_le hTH, ← MonoidHom.range_eq_map, range_subtype] at he
  exact he

/-- The actual offender intersection lies in the original Sylow subgroup. -/
theorem ResidualInput.offender_le_sylow {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) : B ≤ (T : Subgroup G) := by
  have hTH : (T : Subgroup G) ≤ H := d.outside.1.1.2
  have hQ : twoCoreIn H ≤ (T : Subgroup G) := by
    have hm := map_mono (f := H.subtype)
      (pCore_isPGroup.le_sylow_of_normal (T.subtype hTH))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
      ChapterD.twoCoreIn] using hm
  obtain ⟨A,_,rfl⟩ := d.offender.1
  exact inf_le_right.trans hQ

/-- The literal commutator plane lies in the chosen module. -/
theorem ResidualInput.plane_le {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) : ⁅V,B⁆ ≤ V :=
  le_normalizer_iff_commutator_le_left.mp
    (d.offender_le_sylow.trans (h.maximal.1.2.trans h.prepared.normalized))

/-- Original 15.2.12(3), for the constructed commutator plane. -/
theorem ResidualInput.plane_normalizer {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) :
    normalizer ((⁅V,B⁆ : Subgroup G) : Set G) ≤ Mc := by
  let : IsElementaryAbelian 2 V := h.prepared.elementary
  let : IsElementaryAbelian 2 (⁅V,B⁆ : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion d.plane_le) (inclusion_injective d.plane_le)
  exact source_chosen_plane_normalizer d.outside d.two_overgroups
    d.plane_card d.plane_normalized

/-- All relative normality, complement, and quotient-action inputs for
1.3.4 are constructed on K inside the actual Mc. -/
theorem ResidualInput.localInput {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) :
    ∃ P : Subgroup G, LocalInput 3 (T : Subgroup G) (residual H) P Mc := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨e⟩ := d.quotient
  let P : Sylow 3 (residual H) := Classical.arbitrary _
  have hHM : H ≤ Mc :=
    (source_centralizing_HStar_le_seed_centralizer h.ambient T h.maximal
      d.outside h.centralizing).trans (centralizer_le_partner T h.partner)
  have hTM : IsSylowIn 2 (T : Subgroup G) Mc :=
    ⟨T.subtype (partner_mem_overgroups h).2,
      map_subgroupOf_eq_of_le (partner_mem_overgroups h).2⟩
  exact ⟨(P : Subgroup (residual H)).map (residual H).subtype,
    localInput_of_mem_Xi d.mem_Xi hTM (d.residual_join.le.trans hHM)
      (by decide) (residual_odd_quotient_of_wreath H e) P⟩

/-- The actual component-orbit normal closure. The remaining Held row is
visible, rather than silently discarded from the intrinsic theorem. -/
theorem ResidualInput.component_orbit {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) :
    partnerSpan H Mc = residual H ∨ ∃ (P L : Subgroup G),
      LocalInput 3 (T : Subgroup G) (residual H) P Mc ∧
      L ∈ cComponentsIn Mc ∧ L ∈ LStar G (T : Subgroup G) ∧
      IsQuasisimple (XiQuotient L) ∧
      ((componentOrbit L (T : Subgroup G)).subgroupOf Mc).Normal ∧
      ⁅componentOrbit L (T : Subgroup G), P⁆ = componentOrbit L (T : Subgroup G) ∧
      P ≤ componentOrbit L (T : Subgroup G) ∧
      partnerSpan H Mc = componentOrbit L (T : Subgroup G) ∧
      (Alternatives 3 (T : Subgroup G) P L ∨ HeldAlternative 3 (T : Subgroup G) P L) := by
  obtain ⟨P,hP⟩ := d.localInput
  have hT : IsSylowIn 2 (T : Subgroup G) Mc :=
    ⟨T.subtype (partner_mem_overgroups h).2,
      map_subgroupOf_eq_of_le (partner_mem_overgroups h).2⟩
  rcases adequate_three_normalClosure hP
      (h.ambient.twoLocal_sqtk (partner_mem_overgroups h).1.1) hT with
    he | ⟨L,hL,hq,hn,hcomm,hPL,he,halt⟩
  · exact Or.inl he
  · exact Or.inr ⟨P,L,hP,hL,(source_component_families h).symm ▸ hL,
      hq,hn,hcomm,hPL,he,halt⟩

/-- The centralization in 15.2.12(4) needs neither the missing short model
list nor the O^{3'} equality: all adequate component rows centralize Z. -/
theorem ResidualInput.centralizes {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) :
    partnerSpan H Mc ≤ centralizer (centralInvolutions T : Set G) := by
  rcases d.component_orbit with he | ⟨P,L,_,_,hL,_,_,_,_,he,_⟩
  · rw [he]
    exact (map_subtype_le _).trans
      (source_centralizing_HStar_le_seed_centralizer h.ambient T h.maximal
        d.outside h.centralizing)
  · rw [he]
    have hc : L ≤ centralizer (centralInvolutions T : Set G) :=
      local_component_le_centralizer_Z
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
        h.ambient T h.empty hL.1
    apply iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) _ hc
    apply le_trans ?_ (centralizer (centralInvolutions T : Set G)).le_normalizer
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 t ht).symm

/-- The source intersection consequence now retains only the still-needed
prime-complement residual equality, not a centralization callback. -/
theorem ResidualInput.intersection_centralizes {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (he : partnerSpan H Mc = threePrimeResidual Mc) :
    threePrimeResidual (M ⊓ Mc) ≤ M ⊓ centralizer (centralInvolutions T : Set G) :=
  source_chosen_intersection_residual_centralizes T M Mc H he d.centralizes

/-- Application of the convention bridge to the actual chosen source. -/
theorem ResidualInput.residual_equality_of_index {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B)
    (hi : Nat.Coprime 3 ((partnerSpan H Mc).subgroupOf Mc).index) :
    partnerSpan H Mc = threePrimeResidual Mc := by
  obtain ⟨e⟩ := d.quotient
  exact partnerSpan_eq_threePrimeResidual_of_index
    ((source_centralizing_HStar_le_seed_centralizer h.ambient T h.maximal
      d.outside h.centralizing).trans (centralizer_le_partner T h.partner)) e hi

/-- The parent geometry consumer needs only the remaining full-support
deduction; the literal commutator supplies all plane inputs. -/
theorem ResidualInput.geometry_of_full {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (hfull : V = localModule T M) :
    ChosenPlaneGeometry h H ⁅V,B⁆ :=
  source_chosen_geometry_of_plane h d.outside d.two_overgroups d.quotient
    hfull d.plane_le d.plane_card d.plane_normalized

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry

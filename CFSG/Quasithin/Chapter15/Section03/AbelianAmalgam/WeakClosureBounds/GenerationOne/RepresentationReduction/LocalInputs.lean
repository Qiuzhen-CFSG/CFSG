module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.FixedSpace
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# From the earlier local centralization to Borel seed fixation

The subgroup M₀ = M ∩ O²(H) is normal in M ∩ H. Thus the ambient Sylow
subgroup T contains an embedded Sylow subgroup of M₀. Since O²(M₀) lies in
O²(M ∩ H), the earlier centralization of V and T-fixation of the literal seed
imply M₀-fixation by the residual/Sylow supplement theorem. The same supplement
inside H proves that the residual and T generate the actual quotient actor.

The final theorem combines these proved inputs with the explicitly supplied
B.2.14 decomposition and the remaining calculation on the commutator subspace.
It is a conditional intermediate result: the latter calculation must follow
from the source representation restrictions before 15.3.65 is complete.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.49(1) and the final paragraph of 15.3.65, printed p.1152.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow subgroup containing T∩B can be chosen inside the supplied T
when B is normal in an overgroup D of T. Normality is only relative to D. -/
theorem exists_sylow_map_le_of_relative_normal {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) {D B : Subgroup G} (hTD : (T : Subgroup G) ≤ D)
    (hBD : B ≤ D) (hB : (B.subgroupOf D).Normal) :
    ∃ S : Sylow p B, (S : Subgroup B).map B.subtype ≤ T := by
  let := hB
  obtain ⟨Q, hQ⟩ := (T.subtype hTD).exists_subgroupOf_eq_of_normal (B.subgroupOf D)
  let e := subgroupOfEquivOfLe hBD
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro x ⟨b, hb, rfl⟩
  change b ∈ (Q : Subgroup (B.subgroupOf D)).map e.toMonoidHom at hb
  obtain ⟨q, hq, rfl⟩ := hb
  rw [hQ] at hq
  exact hq

omit [Finite G] in
/-- The actual Borel M∩O²(H) is normal in M∩H. -/
theorem normal_borel_overlap (M H : Subgroup G) :
    ((M ⊓ residual H).subgroupOf (M ⊓ H)).Normal := by
  have hR : ((residual H).subgroupOf H).Normal := by
    apply normal_embedded_pResidual_subgroupOf 2 (le_refl H)
    rw [subgroupOf_self]
    infer_instance
  let := hR
  exact inf_subgroupOf_inf_normal_of_right M (residual H) H

/-- Seed fixation by M₀ from 15.3.49(1), the given T-fixation and Sylow
restriction. No Borel or H-fixation is an input. -/
theorem seedSpace_le_borel_of_local_inputs
    {H U Z ZS M V : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hZU : ZS ≤ U) (hZV : ZS ≤ V)
    (hres : residual (M ⊓ H) ≤ centralizer (V : Set G))
    (hT : seedSpace a ZS ≤ fixedSpace a.representation (actorImage H T)) :
    seedSpace a ZS ≤ fixedSpace a.representation (borelImage H M) := by
  have hBD : M ⊓ residual H ≤ M ⊓ H := inf_le_inf_left M (residual_le H)
  obtain ⟨S, hS⟩ := exists_sylow_map_le_of_relative_normal T
    (le_inf hTM hTH) hBD (normal_borel_overlap M H)
  apply seedSpace_le_borel_of_residual_and_sylow a hZU
    (hBD.trans inf_le_right) hTH S hS _ hT
  have hr : residual (M ⊓ residual H) ≤ centralizer (ZS : Set G) :=
    (embedded_pResidual_mono 2 hBD).trans
      (hres.trans (centralizer_le hZV))
  exact (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hr)).le.trans
    bot_le

/-- The residual and the image of the supplied Sylow subgroup generate
the actual actor H/O₂(H). -/
theorem actorImage_residual_sup_sylow {H : Subgroup G} (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) :
    actorImage H (residual H) ⊔ actorImage H T = ⊤ := by
  have hs := congrArg (fun K : Subgroup H => K.map H.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hs
  change residual H ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype = H at hs
  rw [map_subgroupOf_eq_of_le hTH] at hs
  rw [actorImage, actorImage, ← Subgroup.map_sup,
    ← subgroupOf_sup (residual_le H) hTH, hs, subgroupOf_self]
  exact (MonoidHom.range_eq_map _).symm.trans
    (MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _))

/-- Final linear assembly from the preceding local group inputs. The only
remaining linear premises are the explicit B.2.14 decomposition and the
calculation on [U/Z,O²(H)]; neither Borel nor H-fixation is assumed. -/
theorem seedSpace_le_fixedSpace_of_local_inputs
    {H U Z ZS M V : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hZU : ZS ≤ U) (hZV : ZS ≤ V)
    (hres : residual (M ⊓ H) ≤ centralizer (V : Set G))
    (hT : seedSpace a ZS ≤ fixedSpace a.representation (actorImage H T))
    (hdecomp : subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ⊔
      fixedSpace a.representation ⊤ = ⊤)
    (hcalc : subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ⊓
      fixedSpace a.representation (borelImage H M) ≤
        fixedSpace a.representation (actorImage H (residual H))) :
    seedSpace a ZS ≤ fixedSpace a.representation ⊤ :=
  seedSpace_le_fixedSpace_of_borel_calculation a
    (actorImage_residual_sup_sylow T hTH) hdecomp hcalc
    (seedSpace_le_borel_of_local_inputs a T hTM hTH hZU hZV hres hT) hT

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction

module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.MovedPlane
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Span.FixedSpaces
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.PairingAction.FourGroupKernel

/-!
# Normalization on the original rank-three section

The earlier 14.7.65 fixed-space identity makes R₁ fix the image of E
modulo the original V₁. Saturation through that kernel gives normalization
of E; no normalization of the selected opposite point is required.

For the moved-plane contradiction the exact source bound is N_H(F₀) ≤ T.
The cubic lies in the image of the original point centralizer, so a lift
of order three is unnecessary. The action and the normalizer bound are
constructed separately and consumed by the rank-three source assembly.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.65 and proof of 14.7.70, printed pp.1070,1074.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree

open Subgroup Representation Chapter12.Section08 Preparation Preparation.MarkedSpans
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {d : Data T L V F W} {c : CriticalPath (L := L) F}

namespace Preliminary
variable (h : Preliminary d c)
include h

/-- The earlier fixed-space action normalizes E with its original point kernel. -/
theorem R₁_normalizes_E (s : d.ActionDescent) (mark : UpperMarking d)
    (sep : d.ModuleSeparation) (actors : LocalActors d) :
    F.Ri L 1 ≤ normalizer (E c : Set G) := by
  have hfixed : tilde d (Fcomm c) ≤ Representation.invariants
      (d.action.comp ((F.Ri L 1).subgroupOf F.H).subtype) := by
    rw [Span.original_R₁_fixed d s mark sep actors,
      ← upper_eq_seed_sup_kernel d s mark sep actors,
      ← commutator_spans d s c h.earlier mark sep actors h.star_card]
    exact le_sup_left
  apply le_normalizer_iff.mpr
  intro r hr a ha
  let rH : F.H := ⟨r, F.invariant 1 (R₁_le_T hr)⟩
  let aU : F.U := ⟨a, h.E_le_intersection ha |>.1⟩
  let b : F.U := ⟨r * a * r⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized rH.property) a).mp aU.property⟩
  apply (coordinate_mem_iff d (E c) le_sup_left b).mp
  have hw : (d.conjugationSection.coordinates aU).toAdd ∈ tilde d (Fcomm c) :=
    (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨aU, h.E_le_commutator ha, rfl⟩
  rw [d.conjugationSection.equivariant rH aU]
  have hf := hfixed hw (⟨rH, hr⟩ : (F.Ri L 1).subgroupOf F.H)
  change d.action rH (d.conjugationSection.coordinates aU).toAdd =
    (d.conjugationSection.coordinates aU).toAdd at hf
  rw [hf]
  exact (coordinate_mem_iff d (E c) le_sup_left aU).mpr ha

omit [Finite G] [AddCommGroup W] [Module (ZMod 2) W] h in
/-- Relative normality supplied by A.1.14 transfers T-normalization to O²(Y_E). -/
theorem T_normalizes_residual
    (hYE : YE c ≤ normalizer (E c : Set G))
    (hn : ((YE c).subgroupOf (normalizer (E c : Set G))).Normal)
    (hT : (T : Subgroup G) ≤ normalizer (E c : Set G)) :
    (T : Subgroup G) ≤ normalizer (Y c : Set G) := by
  have hN : normalizer (E c : Set G) ≤ normalizer (YE c : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYE).mp hn
  exact (hT.trans hN).trans
    (normalizer_le_normalizer_characteristic_image (YE c) (pResidual 2 (YE c)))

end Preliminary

namespace MovedPlane

/-- The source contradiction uses only the relative normalizer bound.
It does not require that T centralize the original flag plane V₂. -/
theorem cubic_contradiction_of_normalizer_bound (h : Preliminary d c)
    (hN : F.H ⊓ normalizer (Fcomm c : Set G) ≤ (T : Subgroup G))
    (t : G) (action : ThreeAxisAction d c h t) : False := by
  let C : Subgroup action.carrier :=
    (centralizer ({d.z} : Set G)).comap action.carrier.subtype
  have hCT : IsPGroup 2 C := by
    let f : C →* T :=
      { toFun := fun x =>
          ⟨(x : G), hN ⟨action.centralizer_to_H x x.property,
            action.carrier_normalizes x.1.property⟩⟩
        map_one' := by rfl
        map_mul' := by intro x y; rfl }
    apply T.isPGroup'.of_injective f
    intro x y hxy
    have hG : (x : G) = (y : G) := congrArg (fun q : T => (q : G)) hxy
    exact Subtype.ext (Subtype.ext hG)
  obtain ⟨a, ha, hza⟩ := action.cubic
  exact no_cubic_of_two_group hCT (action.action.comp C.subtype) ⟨⟨a, hza⟩, ha⟩

end MovedPlane

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree

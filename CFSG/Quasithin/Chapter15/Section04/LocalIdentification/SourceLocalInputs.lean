module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.SourceData
public import CFSG.Quasithin.Defs
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# SQTK inputs for the two source local amalgams

The actual 1.1.5 input in `Source.LocalData` already records membership of
each generated group I in the source family H. A nonidentity element of the
order-four group Z selects that input. Thus O₂(I) is nontrivial, its ambient
normalizer is a genuine two-local, and the simple QTKE hypothesis supplies
SQTK first for that normalizer and then for I through its literal inclusion.

This discharges the SQTK input for the 15.4.21–22 classification, uniformly
for both X-factors and the same Y-factor. It does not identify the arbitrary
field `d.J` with J(T), prove either classification, or construct LocalData.
The source witnesses for LocalData remain with the local-setup owner.

Source: Aschbacher–Smith, 15.4.17–20 and the setup preceding 15.4.21,
printed pp.1162–1164; `Lemma115Hypotheses.mem_H` retains the relevant input.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section04.Source

universe u
variable {G : Type u} [Group G] [Finite G] {d : Geometry G}
    {κ : GroupClass.{u}}

/-- One genuine 1.1.5 input witnesses membership in H for each selected pair. -/
theorem LocalData.I_mem_H (h : LocalData d) (i j : Bool) :
    d.I i j ∈ Chapter1.H G := by
  have hZ : d.Z ≠ ⊥ :=
    d.Z.one_lt_card_iff_ne_bot.mp (by rw [h.Z_card]; decide)
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  obtain ⟨M, hM⟩ := h.local115 i j (z : G) z.property
    (fun he => hz (Subtype.ext he))
  exact hM.mem_H

omit [Finite G] in
/-- Every source I normalizes its own embedded two-core. -/
theorem LocalData.I_le_coreNormalizer (_h : LocalData d) (i j : Bool) :
    d.I i j ≤ normalizer ((d.I i j).pCoreIn 2 : Set G) :=
  (d.I i j).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (d.I i j) (pCore 2 (d.I i j)))

/-- The core normalizer is a two-local using the nontrivial core already in LocalData. -/
theorem LocalData.I_coreNormalizer_isTwoLocal (h : LocalData d) (i j : Bool) :
    IsTwoLocal (normalizer ((d.I i j).pCoreIn 2 : Set G)) :=
  ⟨(d.I i j).pCoreIn 2, h.I_mem_H i j, isPGroup_pCoreIn 2 (d.I i j), rfl⟩

/-- Simple QTKE supplies the actual SQTK overgroup, without an additional local premise. -/
theorem LocalData.I_coreNormalizer_sqtk (h : LocalData d)
    (hG : IsSimpleQTKE κ G) (i j : Bool) :
    IsSQTK κ (normalizer ((d.I i j).pCoreIn 2 : Set G)) :=
  hG.twoLocal_sqtk (h.I_coreNormalizer_isTwoLocal i j)

/-- Restriction from the literal core normalizer gives the source SQTK input for I. -/
theorem LocalData.I_sqtk (h : LocalData d)
    (hG : IsSimpleQTKE κ G) (i j : Bool) : IsSQTK κ (d.I i j) := by
  exact (IsSQTK.equiv (subgroupOfEquivOfLe (h.I_le_coreNormalizer i j))).mp
    ((h.I_coreNormalizer_sqtk hG i j).subgroup _)

/-- Exchanging the X-factor keeps the same actual SQTK presentation and Y-choice. -/
theorem LocalData.alternateI_sqtk (h : LocalData d)
    (hG : IsSimpleQTKE κ G) (i j : Bool) : IsSQTK κ (d.alternateI i j) :=
  h.I_sqtk hG (!i) j

/-- The literal known-simple input for both classifier applications with one Y-factor. -/
theorem LocalData.source_local_identification_sqtk (h : LocalData d)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (j : Bool) :
    IsSQTK KnownSimple.IsKnownSimple (d.I false j) ∧
      IsSQTK KnownSimple.IsKnownSimple (d.I true j) :=
  ⟨h.I_sqtk hG false j, h.I_sqtk hG true j⟩

end CFSG.Quasithin.Chapter15.Section04.Source

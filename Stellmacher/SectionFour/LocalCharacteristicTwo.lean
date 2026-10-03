module

public import Stellmacher.SectionsOneToFourDefs

/-!
# Characteristic 2 for members of the local family

Under the Section 4 hypotheses, every `P ∈ PSet ⊤ S` has characteristic 2.
This supplies a standing hypothesis for the local groups in the Section 2
arguments applied during the proof of (4.6).

Let `N = N_G(O₂(P))`. Its normalized subgroup is nontrivial, so `N` is
2-local, contains `S`, and has characteristic 2 by hypothesis. Since `S`
is Sylow in `N`, `O₂(N) ≤ S ≤ P`; restriction of normality then gives
`O₂(N) ≤ O₂(P)`. An element of `P` centralizing `O₂(P)` centralizes `O₂(N)`,
so characteristic 2 of `N` puts it in `O₂(N) ≤ O₂(P)`.

Source: `refs/latex/stellmacher-n-group.tex`, standing Section 4 hypotheses
and the local setup in the proof of (4.6).
-/

namespace Stellmacher.SectionFour

universe u

/-- The local-family members inherit characteristic 2 from their core normalizers. -/
public theorem characteristicTwo_of_mem_pSet
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S) (P : Subgroup G)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G)) :
    IsCharacteristicTwoType P := by
  have hSP : (S : Subgroup G) ≤ P := by
    obtain ⟨T, hT⟩ := hP.1.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le _
  let N := Subgroup.normalizer (twoCoreAmbient P : Set G)
  have hPN : P ≤ N := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le (pCore 2 P))).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hSN : (S : Subgroup G) ≤ N := hSP.trans hPN
  have hNlocal : IsTwoLocal N :=
    ⟨twoCoreAmbient P, hP.1.2.2.1,
      (pCore_isPGroup (p := 2) (G := P)).map P.subtype, rfl⟩
  have hNchar : IsCharacteristicTwoType N :=
    (h.local_solvable_characteristicTwo N hNlocal hSN).2
  have hcoreS : twoCoreAmbient N ≤ (S : Subgroup G) := by
    let T : Sylow 2 N := S.subtype hSN
    have hTmap : (T : Subgroup N).map N.subtype = (S : Subgroup G) := by
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSN]
    rw [← hTmap]
    exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := N)).le_sylow_of_normal T)
  have hcoreP : twoCoreAmbient N ≤ P := hcoreS.trans hSP
  have hnormalN : ((twoCoreAmbient N).subgroupOf N).Normal := by
    rw [twoCoreAmbient, subgroupOf_map_subtype_eq]
    infer_instance
  have hnorm : N ≤ Subgroup.normalizer (twoCoreAmbient N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp hnormalN
  have hnormalP : ((twoCoreAmbient N).subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcoreP).mpr (hPN.trans hnorm)
  have hpP : IsPGroup 2 ((twoCoreAmbient N).subgroupOf P) :=
    ((pCore_isPGroup (p := 2) (G := N)).map N.subtype).of_equiv
      (Subgroup.subgroupOfEquivOfLe hcoreP).symm
  have hcores : twoCoreAmbient N ≤ twoCoreAmbient P := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hcoreP]
    exact Subgroup.map_mono (le_sSup ⟨hnormalP, hpP⟩)
  intro x hx
  let xN : N := ⟨x, hPN x.property⟩
  have hxN : xN ∈ Subgroup.centralizer (pCore 2 N : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyP : (y : G) ∈ twoCoreAmbient P := hcores ⟨y, hy, rfl⟩
    obtain ⟨yP, hyPcore, heq⟩ := hyP
    apply Subtype.ext
    have hcomm := Subgroup.mem_centralizer_iff.mp hx yP hyPcore
    have hcoe := congrArg (fun z : P ↦ (z : G)) hcomm
    change (yP : G) = (y : G) at heq
    change (y : G) * (x : G) = (x : G) * (y : G)
    change (yP : G) * (x : G) = (x : G) * (yP : G) at hcoe
    rwa [heq] at hcoe
  have hxcore : (x : G) ∈ twoCoreAmbient P := hcores ⟨xN, hNchar hxN, rfl⟩
  obtain ⟨xP, hxP, heq⟩ := hxcore
  have hxx : xP = x := P.subtype_injective heq
  simpa [hxx] using hxP

end Stellmacher.SectionFour

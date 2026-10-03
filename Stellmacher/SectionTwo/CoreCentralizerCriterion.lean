module

public import Stellmacher.SectionsOneToFourDefs

/-!
# The core-centralizer hypothesis for Stellmacher (2.3)

For a Sylow 2-subgroup `S`, suppose `V ≤ vSubgroup S` and `O₂(G)`
is Sylow in `C_G(V)`. Then `O₂(G) = C_S(vSubgroup S)`, the extra
hypothesis in (2.3). This criterion isolates the transfer used in (4.6)
after comparing normal closures in the two ambient local groups.

The core always centralizes `vSubgroup S = ⟨Ω₁(Z(S))^G⟩`: it lies in
`S`, and its normal centralizer contains the central involutions of
`S`. Conversely, `C_S(vSubgroup S)` is a 2-subgroup of `C_G(V)`,
whose normal Sylow subgroup is the core. No solvability or
characteristic-two assumption is needed for this criterion itself.

Source: `refs/latex/stellmacher-n-group.tex`, (2.3) and its application
in the second paragraph of (4.6).
-/

namespace Stellmacher.SectionTwo

/-- Sylow control in a larger centralizer implies the core equality required in (2.3). -/
public theorem twoCore_eq_sylow_centralizer_of_sylow_control
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (V : Subgroup G)
    (hV : V ≤ vSubgroup S)
    (hSyl : ∃ T : Sylow 2 (Subgroup.centralizer (V : Set G)),
      (T : Subgroup (Subgroup.centralizer (V : Set G))).map
        (Subgroup.centralizer (V : Set G)).subtype = pCore 2 G) :
    pCore 2 G = (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G) := by
  have hcoreS : pCore 2 G ≤ (S : Subgroup G) :=
    (pCore_isPGroup (p := 2) (G := G)).le_sylow_of_normal S
  have hZcentCore : zSubgroup S ≤ Subgroup.centralizer (pCore 2 G : Set G) := by
    intro z hz
    obtain ⟨zS, ⟨zC, _hzC, rfl⟩, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg (fun s : S ↦ (s : G))
      ((Subgroup.mem_center_iff.mp zC.property) ⟨q, hcoreS hq⟩)
  have hVcentCore : vSubgroup S ≤ Subgroup.centralizer (pCore 2 G : Set G) :=
    Subgroup.normalClosure_le_normal hZcentCore
  have hcoreCent : pCore 2 G ≤ Subgroup.centralizer (vSubgroup S : Set G) :=
    Subgroup.le_centralizer_iff.mp hVcentCore
  apply le_antisymm (le_inf hcoreS hcoreCent)
  let R : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G)
  let C : Subgroup G := Subgroup.centralizer (V : Set G)
  obtain ⟨T, hT⟩ := hSyl
  have hRC : R ≤ C := inf_le_right.trans (Subgroup.centralizer_le hV)
  have hRp : IsPGroup 2 (R.subgroupOf C) :=
    (S.isPGroup'.to_le (inf_le_left : R ≤ (S : Subgroup G))).comap_of_injective
      C.subtype C.subtype_injective
  have hTnormal : (T : Subgroup C).Normal := by
    have hEq : (T : Subgroup C) = (pCore 2 G).subgroupOf C := by
      rw [← hT]
      exact (Subgroup.comap_map_eq_self_of_injective C.subtype_injective _).symm
    rw [hEq]
    infer_instance
  have hRT : R.subgroupOf C ≤ (T : Subgroup C) := by
    let _ : (T : Subgroup C).Normal := hTnormal
    have heq := T.is_maximal'
      (hRp.to_sup_of_normal_right T.isPGroup') le_sup_right
    exact (le_sup_left : R.subgroupOf C ≤ R.subgroupOf C ⊔ (T : Subgroup C)).trans heq.le
  change R ≤ pCore 2 G
  rw [← hT, ← Subgroup.map_subgroupOf_eq_of_le hRC]
  exact Subgroup.map_mono hRT

end Stellmacher.SectionTwo

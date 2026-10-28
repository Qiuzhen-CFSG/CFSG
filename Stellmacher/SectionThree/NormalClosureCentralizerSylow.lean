module

public import Stellmacher.SectionThree.NormalSubgroupCoreSylow

/-!
# Sylow control in a normal-closure centralizer

For a solvable member `P` of the Section Three family, a subgroup `Z ≤ S`
centralized by `S` but not by `P` has normal-closure centralizer with Sylow
2-subgroup `O₂(P)`. This isolates the application of (3.3) in the proof of
Stellmacher's (4.6), where `Z = Ω₁(Z(S))`.

The centralizer is normal in `P`, and its product with `S` is proper because
both factors centralize `Z`. The 2-core lies in that centralizer: it lies in
`S` and centralizes `Z`, and its normal centralizer therefore contains the
normal closure of `Z`. The normal-subgroup Sylow theorem then applies.
-/

namespace Stellmacher.SectionThree

universe u

/-- The 2-core is Sylow in the centralizer of the normal closure of a subgroup
centralized by the fixed Sylow subgroup but not by the whole family member. -/
public theorem twoCore_sylow_normalClosure_centralizer
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P Z : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) (hZS : Z ≤ S)
    (hSZ : S ≤ Subgroup.centralizer (Z : Set G))
    (hnot : ¬ P ≤ Subgroup.centralizer (Z : Set G)) :
    IsSylowSubgroupIn (twoCoreAmbient P)
      ((Subgroup.centralizer
        (Subgroup.normalClosure (Z.subgroupOf P : Set P) : Set P)).map P.subtype) := by
  let W : Subgroup P := Subgroup.normalClosure (Z.subgroupOf P : Set P)
  let K0 : Subgroup P := Subgroup.centralizer (W : Set P)
  let K : Subgroup G := K0.map P.subtype
  have hSP : S ≤ P := by
    obtain ⟨T, hT⟩ := hP.1.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le _
  have hZP : Z ≤ P := hZS.trans hSP
  have hKP : K ≤ P := Subgroup.map_subtype_le _
  have hKN : (K.subgroupOf P).Normal := by
    rw [show K = K0.map P.subtype from rfl, subgroupOf_map_subtype_eq]
    infer_instance
  have hKZ : K ≤ Subgroup.centralizer (Z : Set G) := by
    intro k hk
    obtain ⟨kP, hkP, rfl⟩ := hk
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    let zP : P := ⟨z, hZP hz⟩
    have hzW : zP ∈ W := Subgroup.le_normalClosure hz
    exact congrArg (fun a : P ↦ (a : G))
      (Subgroup.mem_centralizer_iff.mp hkP zP hzW)
  have hnotKS : ¬ P ≤ K ⊔ S := by
    intro hle
    exact hnot (hle.trans (sup_le hKZ hSZ))
  have hcoreS : twoCoreAmbient P ≤ S := by
    obtain ⟨T, hT⟩ := hP.1.2.1
    rw [← hT]
    exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := P)).le_sylow_of_normal T)
  have hZcentCore : Z.subgroupOf P ≤ Subgroup.centralizer (pCore 2 P : Set P) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqS : (q : G) ∈ S := hcoreS ⟨q, hq, rfl⟩
    have hqz := Subgroup.mem_centralizer_iff.mp (hSZ hqS) (z : G) hz
    apply Subtype.ext
    exact hqz.symm
  have hWcentCore : W ≤ Subgroup.centralizer (pCore 2 P : Set P) :=
    Subgroup.normalClosure_le_normal hZcentCore
  have hcoreK0 : pCore 2 P ≤ K0 :=
    Subgroup.le_centralizer_iff.mp hWcentCore
  have hcoreK : twoCoreAmbient P ≤ K := Subgroup.map_mono hcoreK0
  exact twoCore_sylow_of_normal_not_generate S h P K hP hsolv hKP hKN hnotKS hcoreK

end Stellmacher.SectionThree

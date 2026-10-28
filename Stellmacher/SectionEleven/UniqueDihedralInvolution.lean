module

public import Stellmacher.LaterDefs
public import Theory.GroupTheory.SymmetricFourSylowInvolution
public import Mathlib.GroupTheory.Nilpotent

/-!
# Extraction of a core involution

For a finite group, an S4 subgroup whose two-core has precisely that subgroup
as normalizer supplies a noncentral core involution in any ambient Sylow
two-subgroup containing its Sylow two-subgroup. The involution centralizer
has order four.

The local symmetric-four calculation supplies the involution and its local
centralizer, together with core order four and local Sylow order eight.
Sylow maximality computes the intersection with the core normalizer.
The normalizer condition inside the involution centralizer then promotes
the local centralizer to the ambient Sylow subgroup. Its order four, compared
with the local Sylow order eight, also proves noncentrality; identifying
the center of the ambient Sylow subgroup is unnecessary.
Source: refs/latex/stellmacher-n-group.tex, lines 2082–2087.
-/

namespace Stellmacher.SectionEleven

open SectionsFiveToSeven Later

universe u

private theorem sylow_intersection
    {H : Type u} [Group H] {S0 : Sylow 2 H} {S P : Subgroup H}
    (hS0 : S ≤ (S0 : Subgroup H)) (hSylow : IsSylowTwoIn S P) :
    (S0 : Subgroup H) ⊓ P = S := by
  obtain ⟨hSP, T, hTmap⟩ := hSylow
  let X : Subgroup H := (S0 : Subgroup H) ⊓ P
  have hXP : X ≤ P := inf_le_right
  have hSX : S ≤ X := le_inf hS0 hSP
  have hXp : IsPGroup 2 X := S0.isPGroup'.to_le inf_le_left
  let XP : Subgroup P := X.subgroupOf P
  have hXPp : IsPGroup 2 XP :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXP).symm
  have hTX : (T : Subgroup P) ≤ XP := by
    apply Subgroup.map_subtype_le_map_subtype.mp
    rw [hTmap, Subgroup.map_subgroupOf_eq_of_le hXP]
    exact hSX
  have hXP_eq : XP = (T : Subgroup P) := T.is_maximal' hXPp hTX
  calc
    X = XP.map P.subtype := (Subgroup.map_subgroupOf_eq_of_le hXP).symm
    _ = (T : Subgroup P).map P.subtype := congrArg (fun U => U.map P.subtype) hXP_eq
    _ = S := hTmap

private theorem centralizer_eq_of_normalizer_intersection
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (Q : Subgroup G) (x : G)
    (hQC : Q ≤ Subgroup.centralizer ({x} : Set G))
    (hNC : Subgroup.normalizer (Q : Set G) ⊓
      Subgroup.centralizer ({x} : Set G) ≤ Q) :
    Subgroup.centralizer ({x} : Set G) = Q := by
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let : Group.IsNilpotent C := (hG.to_subgroup C).isNilpotent
  have hself : Subgroup.normalizer (Q.subgroupOf C : Set C) = Q.subgroupOf C := by
    apply le_antisymm
    · rw [← Subgroup.subgroupOf_normalizer_eq hQC]
      intro y hy
      exact hNC ⟨hy, y.property⟩
    · exact Subgroup.le_normalizer
  have htop : Q.subgroupOf C = ⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent _ hself
  exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hQC

public theorem exists_core_involution_centralizer_four
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P : Subgroup H)
    (hS : S ≤ (S0 : Subgroup H)) (hSylow : IsSylowTwoIn S P)
    (hModel : IsModel P S4)
    (hNormalizer : Subgroup.normalizer (twoCoreIn P : Set H) = P) :
    ∃ x : S0, (x : H) ∈ twoCoreIn P ∧ orderOf x = 2 ∧
      x ∉ Subgroup.center S0 ∧
      Nat.card (Subgroup.centralizer ({x} : Set S0)) = 4 := by
  have hinter := sylow_intersection hS hSylow
  obtain ⟨_, T, hTmap⟩ := hSylow
  obtain ⟨x, hxQ, hxorder, hxC, hQcard, hTcard⟩ :=
    symmetric_four_sylow_core_involution T hModel
  have hcoreT : pCore 2 P ≤ (T : Subgroup P) :=
    (pCore_isPGroup (G := P) (p := 2)).le_sylow_of_normal T
  have hcoreS : twoCoreIn P ≤ S := by
    rw [← hTmap]
    exact Subgroup.map_mono hcoreT
  have hcoreS0 : twoCoreIn P ≤ (S0 : Subgroup H) := hcoreS.trans hS
  have hxQH : (x : H) ∈ twoCoreIn P := ⟨x, hxQ, rfl⟩
  let x0 : S0 := ⟨x, hcoreS0 hxQH⟩
  let Q : Subgroup S0 := (twoCoreIn P).subgroupOf S0
  have hQC : Q ≤ Subgroup.centralizer ({x0} : Set S0) := by
    intro y hy
    obtain ⟨yp, hyp, heq⟩ := hy
    have hyC : yp ∈ Subgroup.centralizer ({x} : Set P) := by
      exact (show yp ∈ Subgroup.centralizer ({x} : Set P) ⊓
        (T : Subgroup P) from hxC ▸ hyp).1
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    have hcomm := congrArg (fun z : P => (z : H))
      (Subgroup.mem_centralizer_singleton_iff.mp hyC)
    change (yp : H) = (y : H) at heq
    change (yp : H) * (x : H) = (x : H) * (yp : H) at hcomm
    change (y : H) * (x : H) = (x : H) * (y : H)
    simpa only [heq] using hcomm
  have hNC : Subgroup.normalizer (Q : Set S0) ⊓
      Subgroup.centralizer ({x0} : Set S0) ≤ Q := by
    intro y hy
    have hyN : (y : H) ∈ Subgroup.normalizer (twoCoreIn P : Set H) := by
      have hnormal := Subgroup.subgroupOf_normalizer_eq hcoreS0
      exact (show y ∈ (Subgroup.normalizer (twoCoreIn P : Set H)).subgroupOf S0
        from hnormal ▸ hy.1)
    have hyP : (y : H) ∈ P := hNormalizer ▸ hyN
    have hyS : (y : H) ∈ S := hinter ▸ ⟨y.property, hyP⟩
    let yp : P := ⟨y, hyP⟩
    have hyT : yp ∈ (T : Subgroup P) := by
      have hymap : (y : H) ∈ (T : Subgroup P).map P.subtype := hTmap ▸ hyS
      obtain ⟨yt, hyt, heq⟩ := hymap
      have heq' : yt = yp := Subtype.ext heq
      exact heq' ▸ hyt
    have hyC : yp ∈ Subgroup.centralizer ({x} : Set P) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      exact congrArg (fun z : S0 => (z : H))
        (Subgroup.mem_centralizer_singleton_iff.mp hy.2)
    have hycore : yp ∈ pCore 2 P := hxC ▸ ⟨hyC, hyT⟩
    exact ⟨yp, hycore, rfl⟩
  have hCeq := centralizer_eq_of_normalizer_intersection S0.isPGroup' Q x0 hQC hNC
  have hQHcard : Nat.card (twoCoreIn P) = 4 := by
    exact (Subgroup.card_map_of_injective P.subtype_injective).trans hQcard
  have hQ0card : Nat.card Q = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcoreS0).toEquiv).trans hQHcard
  have hCcard : Nat.card (Subgroup.centralizer ({x0} : Set S0)) = 4 := by
    rw [hCeq, hQ0card]
  have hScard : Nat.card S = 8 := by
    rw [← hTmap]
    exact (Subgroup.card_map_of_injective P.subtype_injective).trans hTcard
  have hxnotcenter : x0 ∉ Subgroup.center S0 := by
    intro hxZ
    have hS0Q : (S0 : Subgroup H) ≤ twoCoreIn P := by
      intro y hy
      have hyC : (⟨y, hy⟩ : S0) ∈ Subgroup.centralizer ({x0} : Set S0) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_center_iff.mp hxZ _)
      exact (show (⟨y, hy⟩ : S0) ∈ Q from hCeq ▸ hyC)
    have hbound := Subgroup.card_le_of_le (hS.trans hS0Q)
    rw [hScard, hQHcard] at hbound
    omega
  refine ⟨x0, hxQH, ?_, hxnotcenter, hCcard⟩
  calc
    orderOf x0 = orderOf (x : H) :=
      (orderOf_injective (S0 : Subgroup H).subtype Subtype.coe_injective x0).symm
    _ = orderOf x := orderOf_injective P.subtype P.subtype_injective x
    _ = 2 := hxorder


end Stellmacher.SectionEleven

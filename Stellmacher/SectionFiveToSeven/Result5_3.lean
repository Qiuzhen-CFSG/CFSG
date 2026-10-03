module

public import Stellmacher.SectionFiveToSeven.Defs

/-!
# Stellmacher (5.3): local properties of the amalgam members

Under Hypothesis 2, each amalgam member `Pᵢ` is solvable and of
characteristic 2 type. Its nontrivial 2-core defines the 2-local subgroup
`N = N_H(O₂(Pᵢ))`; (5.1) makes `S` a Sylow 2-subgroup of `N`, and the
Baumann subgroup lies in `N`, so Hypothesis 2 gives the corresponding
properties of `N`.  Alternative (c)'s additional two-local `J`-stability
field is orthogonal here; the proof continues to use only its two displayed
Sylow-normalizer fields.

Solvability passes to `Pᵢ ≤ N`. For characteristic 2, the Sylow condition
gives `O₂(N) ≤ S ≤ Pᵢ`, and normality gives `O₂(N) ≤ O₂(Pᵢ)`. An element
of `Pᵢ` centralizing `O₂(Pᵢ)` therefore centralizes `O₂(N)`; the
characteristic-2 property of `N` places it in `O₂(Pᵢ)`.

Source: `refs/latex/stellmacher-n-group.tex`, Hypothesis 2 and (5.3).
-/

open scoped Pointwise

universe u

namespace Stellmacher.SectionsFiveToSeven

variable {H : Type u} [Group H] [Finite H]

omit [Finite H] in
private theorem twoCoreIn_normal_subgroupOf (P : Subgroup H) :
    ((twoCoreIn P).subgroupOf P).Normal := by
  rw [← Subgroup.comap_subtype, twoCoreIn,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  exact (inferInstance : (pCore 2 P).Normal)

omit [Finite H] in
private theorem twoCoreIn_isPGroup (P : Subgroup H) :
    IsPGroup 2 (twoCoreIn P) :=
  (pCore_isPGroup (p := 2) (G := P)).map P.subtype

omit [Finite H] in
private theorem normal_pSubgroup_le_twoCoreIn
    (Q P : Subgroup H) (hQP : Q ≤ P)
    (hQp : IsPGroup 2 Q) (hQnormal : (Q.subgroupOf P).Normal) :
    Q ≤ twoCoreIn P := by
  have hQpP : IsPGroup 2 (Q.subgroupOf P) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have hle : Q.subgroupOf P ≤ pCore 2 P := le_sSup ⟨hQnormal, hQpP⟩
  calc
    Q = (Q.subgroupOf P).map P.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQP).symm
    _ ≤ (pCore 2 P).map P.subtype := Subgroup.map_mono hle
    _ = twoCoreIn P := rfl

omit [Finite H] in
private theorem mem_pCore_of_mem_twoCoreIn
    (P : Subgroup H) (x : P) (hx : (x : H) ∈ twoCoreIn P) :
    x ∈ pCore 2 P := by
  rcases hx with ⟨y, hy, hyx⟩
  have : y = x := P.subtype_injective hyx
  simpa [this] using hy

omit [Finite H] in
private theorem twoCoreIn_le_of_sylowTwoIn
    (S N : Subgroup H) (hSN : IsSylowTwoIn S N) :
    twoCoreIn N ≤ S := by
  obtain ⟨-, T, hT⟩ := hSN
  calc
    twoCoreIn N = (pCore 2 N).map N.subtype := rfl
    _ ≤ (T : Subgroup N).map N.subtype := Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := N)).le_sylow_of_normal T)
    _ = S := hT

omit [Finite H] in
private theorem sylowTwoIn_of_eq_globalSylow
    (S0 : Sylow 2 H) (S N : Subgroup H)
    (hS : S = (S0 : Subgroup H)) (hSN : S ≤ N) :
    IsSylowTwoIn S N := by
  subst S
  refine ⟨hSN, S0.subtype hSN, ?_⟩
  exact Subgroup.map_subgroupOf_eq_of_le hSN

private theorem local_properties
    (S0 : Sylow 2 H) (S P : Subgroup H)
    {P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hP : P ∈ PFamily (⊤ : Subgroup H) S)
    (hSylowN : IsSylowTwoIn S
      (Subgroup.normalizer (twoCoreIn P : Set H))) :
    Group.IsSolvable P ∧ Stellmacher.IsCharacteristicTwoType P := by
  let Q : Subgroup H := twoCoreIn P
  let N : Subgroup H := Subgroup.normalizer (Q : Set H)
  have hSP : S ≤ P := hP.1.2.1.1
  have hQne : Q ≠ ⊥ := hP.1.2.2.1
  have hQp : IsPGroup 2 Q := twoCoreIn_isPGroup P
  have hPN : P ≤ N := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le (pCore 2 P))).mp
        (twoCoreIn_normal_subgroupOf P)
  have hSN : S ≤ N := hSP.trans hPN
  have hNlocal : IsTwoLocal N := ⟨Q, hQne, hQp, rfl⟩
  have hBN : baumannIn S ≤ N :=
    (inf_le_left : baumannIn S ≤ S).trans hSN
  obtain ⟨hNsolvable, hNchar⟩ := h.local_B N hNlocal hBN
  have hPsolvable : Group.IsSolvable P := by
    let _ : Group.IsSolvable N := hNsolvable
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective hPN)
  refine ⟨hPsolvable, ?_⟩
  have hCoreNleS : twoCoreIn N ≤ S := by
    exact twoCoreIn_le_of_sylowTwoIn S N hSylowN
  have hCoreNleP : twoCoreIn N ≤ P := hCoreNleS.trans hSP
  have hCoreNnormalP : ((twoCoreIn N).subgroupOf P).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hCoreNleP).mpr
    apply hPN.trans
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le (pCore 2 N))).mp
        (twoCoreIn_normal_subgroupOf N)
  have hCoreNleCoreP : twoCoreIn N ≤ twoCoreIn P :=
    normal_pSubgroup_le_twoCoreIn (twoCoreIn N) P hCoreNleP
      (twoCoreIn_isPGroup N) hCoreNnormalP
  intro x hx
  have hxN : Subgroup.inclusion hPN x ∈
      Subgroup.centralizer (pCore 2 N : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyCoreNAmbient : (y : H) ∈ twoCoreIn N :=
      Subgroup.mem_map_of_mem N.subtype hy
    let yP : P := ⟨(y : H), hCoreNleP hyCoreNAmbient⟩
    have hyCoreP : yP ∈ pCore 2 P :=
      mem_pCore_of_mem_twoCoreIn P yP
        (hCoreNleCoreP hyCoreNAmbient)
    have hcomm := Subgroup.mem_centralizer_iff.mp hx yP hyCoreP
    apply Subtype.ext
    change (y : H) * (x : H) = (x : H) * (y : H)
    exact congrArg (fun z : P => (z : H)) hcomm
  have hxCoreNAmbient : (x : H) ∈ twoCoreIn N :=
    Subgroup.mem_map_of_mem N.subtype (hNchar hxN)
  exact mem_pCore_of_mem_twoCoreIn P x (hCoreNleCoreP hxCoreNAmbient)

/-- **Stellmacher (5.3).** Under Hypothesis 2 both members of the amalgam
are solvable and of characteristic 2 type. -/
public theorem lemma_five_three
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) :
    Group.IsSolvable P1 ∧ Stellmacher.IsCharacteristicTwoType P1 ∧
      Group.IsSolvable P2 ∧ Stellmacher.IsCharacteristicTwoType P2 := by
  have hP1N : P1 ≤ Subgroup.normalizer (twoCoreIn P1 : Set H) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le (pCore 2 P1))).mp
        (twoCoreIn_normal_subgroupOf P1)
  have hP2N : P2 ≤ Subgroup.normalizer (twoCoreIn P2 : Set H) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le (pCore 2 P2))).mp
        (twoCoreIn_normal_subgroupOf P2)
  have hSP1 : S ≤ P1 := h.fiveOne.P1_mem.1.2.1.1
  have hSP2 : S ≤ P2 := h.fiveOne.P2_mem.1.2.1.1
  have hSN1 : S ≤ Subgroup.normalizer (twoCoreIn P1 : Set H) :=
    hSP1.trans hP1N
  have hSN2 : S ≤ Subgroup.normalizer (twoCoreIn P2 : Set H) :=
    hSP2.trans hP2N
  have hSylowN1 : IsSylowTwoIn S
      (Subgroup.normalizer (twoCoreIn P1 : Set H)) := by
    cases h.fiveOne.alternative with
    | a hS _ _ =>
        exact sylowTwoIn_of_eq_globalSylow S0 S _ hS hSN1
    | b hS _ =>
        exact sylowTwoIn_of_eq_globalSylow S0 S _ hS hSN1
    | c _ _ _ _ _ _ _ _ _ hSylow _ _ _ => exact hSylow
  have hSylowN2 : IsSylowTwoIn S
      (Subgroup.normalizer (twoCoreIn P2 : Set H)) := by
    cases h.fiveOne.alternative with
    | a hS _ _ =>
        exact sylowTwoIn_of_eq_globalSylow S0 S _ hS hSN2
    | b hS _ =>
        exact sylowTwoIn_of_eq_globalSylow S0 S _ hS hSN2
    | c _ _ _ _ _ _ _ _ _ _ hSylow _ _ => exact hSylow
  obtain ⟨hP1solvable, hP1char⟩ :=
    local_properties S0 S P1 h h.fiveOne.P1_mem hSylowN1
  obtain ⟨hP2solvable, hP2char⟩ :=
    local_properties S0 S P2 h h.fiveOne.P2_mem hSylowN2
  exact ⟨hP1solvable, hP1char, hP2solvable, hP2char⟩

end Stellmacher.SectionsFiveToSeven

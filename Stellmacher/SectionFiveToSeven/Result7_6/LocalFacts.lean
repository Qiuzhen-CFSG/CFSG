module

public import Stellmacher.SectionFiveToSeven.Result7_6.CoreFacts

/-!
# Local Sylow and center facts at a critical edge

The two endpoint stabilizers are the given local groups, so their solvability,
characteristic-two hypotheses, and common Sylow subgroup transport to the
first edge. Their 2-cores lie in that Sylow subgroup. The Sylow witnesses also
supply the exact Section 3 hypotheses. Omega-center subgroups are elementary
abelian and central; the neighbor-center dichotomy of (7.3) transfers this
to vertex centers. These facts support both length branches of (7.6).

Source: B. Stellmacher, Journal of Algebra 190 (1997), Lemma (7.6),
pp. 35–36; `refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven.SevenSix

open CosetGraphContext

universe u v

public theorem edge_local_data
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    (stabilizer Gamma cp.a ∈ PFamily (⊤ : Subgroup G) S ∧
      Group.IsSolvable (stabilizer Gamma cp.a)) ∧
    (stabilizer Gamma cp.firstStep ∈ PFamily (⊤ : Subgroup G) S ∧
      Group.IsSolvable (stabilizer Gamma cp.firstStep)) := by
  rcases cp.edge_stabilizers_are_P with hedge | hedge
  · rw [hedge.1, hedge.2]
    exact ⟨⟨h.P1_mem, h.P1_solvable⟩, h.P2_mem, h.P2_solvable⟩
  · rw [hedge.1, hedge.2]
    exact ⟨⟨h.P2_mem, h.P2_solvable⟩, h.P1_mem, h.P1_solvable⟩

public theorem edge_characteristic_data
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    Stellmacher.IsCharacteristicTwoType (stabilizer Gamma cp.a) ∧
      Stellmacher.IsCharacteristicTwoType
        (stabilizer Gamma cp.firstStep) := by
  rcases cp.edge_stabilizers_are_P with hedge | hedge
  · rw [hedge.1, hedge.2]
    exact ⟨h.P1_characteristicTwo, h.P2_characteristicTwo⟩
  · rw [hedge.1, hedge.2]
    exact ⟨h.P2_characteristicTwo, h.P1_characteristicTwo⟩

private theorem sectionSeven_even_order
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2) :
    Even (Nat.card G) := by
  have hSp : IsPGroup 2 S := by
    obtain ⟨_, T, hTmap⟩ := h.P1_mem.1.2.1
    rw [← hTmap]
    exact T.isPGroup'.map P1.subtype
  let _ : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 h.S_nontrivial
  obtain ⟨n, hn, hcard⟩ := hSp.nontrivial_iff_card.mp inferInstance
  apply even_iff_two_dvd.mpr
  apply (show 2 ∣ Nat.card S by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)).trans
  exact Subgroup.card_subgroup_dvd_card S

public theorem sectionThreeHypotheses
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2) :
    Stellmacher.SectionThree.Hypotheses G S := by
  have hSp : IsPGroup 2 S := by
    obtain ⟨_, T, hTmap⟩ := h.P1_mem.1.2.1
    rw [← hTmap]
    exact T.isPGroup'.map P1.subtype
  exact
    { even_order := sectionSeven_even_order h
      nontrivial_two_subgroup := ⟨h.S_nontrivial, hSp⟩ }

public theorem omegaOneCenter_le_centerAmbient
    {G : Type u} [Group G] (A : Subgroup G) :
    omegaOneCenter A ≤ (Subgroup.center A).map A.subtype := by
  unfold omegaOneCenter
  exact Subgroup.map_mono (Subgroup.map_subtype_le _)

public theorem centerAmbient_le_centralizer
    {G : Type u} [Group G] (A : Subgroup G) :
    (Subgroup.center A).map A.subtype ≤
      Subgroup.centralizer (A : Set G) := by
  intro x hx
  obtain ⟨xc, hxc, rfl⟩ := hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let ya : A := ⟨y, hy⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ya)

private theorem omegaOneCenter_isElementaryAbelian
    {G : Type u} [Group G] (A : Subgroup G) :
    IsElementaryAbelian 2 (omegaOneCenter A) := by
  unfold omegaOneCenter
  exact ((IsElementaryAbelian.omega₁_of_isMulCommutative
    (p := 2) (Subgroup.center A)).map
      (Subgroup.center A).subtype).map A.subtype

public theorem z_isElementaryAbelian_of_neighbor
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2)
    {d l : Gamma.Vertex} (hl : l ∈ neighborhood Gamma d) :
    IsElementaryAbelian 2 (z Gamma d) := by
  let A := omegaOneCenter (q Gamma d)
  have hle : z Gamma d ≤ A :=
    (lemma_seven_three h Gamma).center_core d l hl
  have hA : IsElementaryAbelian 2 A :=
    omegaOneCenter_isElementaryAbelian (q Gamma d)
  let _ : IsElementaryAbelian 2 A := hA
  exact
    { toIsMulCommutative :=
        ⟨⟨fun x y ↦ Subtype.ext
          (show (x : G) * (y : G) = (y : G) * (x : G) from
            congrArg Subtype.val
              ((IsMulCommutative.is_comm (M := A)).comm
                ⟨x, hle x.property⟩ ⟨y, hle y.property⟩))⟩⟩
      exponent_dvd_p := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro x
        apply Subtype.ext
        have ha := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A)
          ⟨(x : G), hle x.property⟩
        exact congrArg (fun a : A ↦ (a : G)) ha }

public theorem conjugateClosure_le_map_normalClosure
    {G : Type u} [Group G] (X A : Subgroup G) (hXA : X ≤ A) :
    conjugateClosure X A ≤
      (Subgroup.normalClosure ((X.subgroupOf A : Subgroup A) : Set A)).map
        A.subtype := by
  rw [conjugateClosure]
  apply (Subgroup.closure_le _).2
  rintro x ⟨a, y, rfl⟩
  let yA : A := ⟨(y : G), hXA y.property⟩
  have hy : yA ∈ Subgroup.normalClosure
      ((X.subgroupOf A : Subgroup A) : Set A) :=
    Subgroup.subset_normalClosure y.property
  have hconj : a * yA * a⁻¹ ∈ Subgroup.normalClosure
      ((X.subgroupOf A : Subgroup A) : Set A) :=
    Subgroup.normalClosure_normal.conj_mem yA hy a
  exact Subgroup.mem_map_of_mem A.subtype hconj

public theorem local_cores_le_edge_sylow
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ) :
    q Γ cp.a ≤ S ∧ q Γ cp.firstStep ≤ S := by
  rcases cp.edge_stabilizers_are_P with hstabs | hstabs
  · have hS1 : IsSylowTwoIn S P1 := h.P1_mem.1.2.1
    have hS2 : IsSylowTwoIn S P2 := h.P2_mem.1.2.1
    rcases hS1.2 with ⟨T1, hT1⟩
    rcases hS2.2 with ⟨T2, hT2⟩
    constructor
    · rw [q, Γ.twoCoreAt_def]
      change twoCoreIn (stabilizer Γ cp.a) ≤ S
      rw [hstabs.1, twoCoreIn]
      rw [← hT1]
      exact Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal T1)
    · rw [q, Γ.twoCoreAt_def]
      change twoCoreIn (stabilizer Γ cp.firstStep) ≤ S
      rw [hstabs.2, twoCoreIn]
      rw [← hT2]
      exact Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal T2)
  · have hS1 : IsSylowTwoIn S P1 := h.P1_mem.1.2.1
    have hS2 : IsSylowTwoIn S P2 := h.P2_mem.1.2.1
    rcases hS1.2 with ⟨T1, hT1⟩
    rcases hS2.2 with ⟨T2, hT2⟩
    constructor
    · rw [q, Γ.twoCoreAt_def]
      change twoCoreIn (stabilizer Γ cp.a) ≤ S
      rw [hstabs.1, twoCoreIn]
      rw [← hT2]
      exact Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal T2)
    · rw [q, Γ.twoCoreAt_def]
      change twoCoreIn (stabilizer Γ cp.firstStep) ≤ S
      rw [hstabs.2, twoCoreIn]
      rw [← hT1]
      exact Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal T1)

public theorem edge_sylow_data
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    IsSylowTwoIn S (stabilizer Gamma cp.a) ∧
      IsSylowTwoIn S (stabilizer Gamma cp.firstStep) := by
  rcases cp.edge_stabilizers_are_P with hedge | hedge
  · rw [hedge.1, hedge.2]
    exact ⟨h.P1_mem.1.2.1, h.P2_mem.1.2.1⟩
  · rw [hedge.1, hedge.2]
    exact ⟨h.P2_mem.1.2.1, h.P1_mem.1.2.1⟩

end Stellmacher.SectionsFiveToSeven.SevenSix


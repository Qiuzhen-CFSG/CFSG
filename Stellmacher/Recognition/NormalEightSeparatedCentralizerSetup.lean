module

public import Stellmacher.Recognition.NormalEightSeparatedCentralizerData
public import Stellmacher.MainDefs
public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.NormalEightCentralizerCharacteristic
public import Theory.GroupTheory.IndexTwoInvolutionCentralizer
public import Theory.GroupTheory.SolvableCentralOmegaSupplement
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# The separated involution-centralizer setup

For a separated noncentral involution of the normal four, its Sylow
centralizer has index two and is Sylow in its full centralizer. The central
omega of this subgroup is the four: it is characteristic in the normal
four-centralizer, so a larger central omega would give a normal elementary
eight in the original Sylow subgroup.

Solvability of the involution centralizer then supplies a normalizer
supplement to its odd core in which the four's normal closure is elementary
and lies in the chosen Sylow. No bound on the closure's cardinality or on
nonnormal elementary subgroups is used.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, pp.387–388,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedCentralizers
open Subgroup NormalEightSeparatedFusion
open scoped IsMulCommutative
private theorem centralizer_eq_four_centralizer
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (i : P) (hiW : i ∈ W) (hiC : i ∉ center P) :
    centralizer ({i} : Set P) = centralizer (W : Set P) := by
  have hle : centralizer (W : Set P) ≤ centralizer ({i} : Set P) :=
    centralizer_le (Set.singleton_subset_iff.mpr hiW)
  have hidx := centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
    hP hZ W hW
  have hd : (centralizer ({i} : Set P)).index ∣ 2 :=
    hidx ▸ index_dvd_of_le hle
  have hiidx : (centralizer ({i} : Set P)).index = 2 :=
    (Nat.prime_two.eq_one_or_self_of_dvd _ hd).resolve_left (by
      intro h
      exact hiC ((centralizer_eq_top_iff_subset.mp (index_eq_one.mp h)) (Set.mem_singleton i)))
  apply (eq_of_le_of_card_ge hle ?_).symm
  have hc := (centralizer ({i} : Set P)).card_mul_index
  have hw := (centralizer (W : Set P)).card_mul_index
  rw [hiidx] at hc
  rw [hidx] at hw
  omega

private theorem mem_centralOmega_iff
    {P : Type*} [Group P] (Q : Subgroup P) (x : P) :
    x ∈ ((omega₁ (center Q) (p := 2)).map (center Q).subtype).map Q.subtype ↔
      x ∈ Q ∧ x ∈ centralizer (Q : Set P) ∧ x ^ 2 = 1 := by
  let : IsElementaryAbelian 2 (omega₁ (center Q) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨(z : Q).property, ?_, ?_⟩
    · intro q hq
      exact congrArg Subtype.val (mem_center_iff.mp z.property ⟨q, hq⟩)
    · exact congrArg (fun a : center Q => ((a : Q) : P))
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz)
  · rintro ⟨hx, hc, hs⟩
    have hcenter : (⟨x, hx⟩ : Q) ∈ center Q :=
      mem_center_iff.mpr (fun q => Subtype.ext (hc q q.property))
    refine ⟨⟨x, hx⟩, ⟨⟨⟨x, hx⟩, hcenter⟩, subset_closure ?_, rfl⟩, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hs

private theorem centralizer_omega_center_eq
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (i : S) (hiW : i ∈ W) (hiC : i ∉ center S)
    (T : Sylow 2 (centralizer ({(i : G)} : Set G)))
    (hT : (T : Subgroup (centralizer ({(i : G)} : Set G))) =
      (S : Subgroup G).subgroupOf (centralizer ({(i : G)} : Set G))) :
    ((omega₁ (center T) (p := 2)).map (center T).subtype).map
      (T : Subgroup (centralizer ({(i : G)} : Set G))).subtype =
    (W.map (S : Subgroup G).subtype).subgroupOf (centralizer ({(i : G)} : Set G)) := by
  let C := centralizer ({(i : G)} : Set G)
  let D := centralizer (W : Set S)
  have hD : centralizer ({i} : Set S) = D :=
    centralizer_eq_four_centralizer S.isPGroup' hZ W hW i hiW hiC
  have hDc (s : S) : (s : G) ∈ C ↔ s ∈ D := by
    rw [← hD]
    simp only [C, mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hO := omega_one_center_centralizer_eq_normal_four hno W hW
  ext x
  rw [mem_centralOmega_iff]
  constructor
  · rintro ⟨hxT, hc, hs⟩
    have hxS : (x : G) ∈ S := by rw [hT] at hxT; exact hxT
    let s : S := ⟨x, hxS⟩
    have hsW : s ∈ W := by
      rw [← hO]
      apply (mem_centralOmega_iff D s).mpr
      refine ⟨(hDc s).mp x.property, ?_, ?_⟩
      · intro t ht
        have htC := (hDc t).mpr ht
        have htT : (⟨t, htC⟩ : C) ∈ T := by
          change (⟨t, htC⟩ : C) ∈ (T : Subgroup C)
          rw [hT]
          exact t.property
        exact Subtype.ext (congrArg (fun a : C => (a : G)) (hc ⟨t, htC⟩ htT))
      · exact Subtype.ext (congrArg (fun a : C => (a : G)) hs)
    exact mem_map_of_mem (S : Subgroup G).subtype hsW
  · intro hx
    obtain ⟨s, hsW, hsx⟩ := hx
    change (s : G) = (x : G) at hsx
    have hsO : s ∈ ((omega₁ (center D) (p := 2)).map (center D).subtype).map D.subtype :=
      hO ▸ hsW
    obtain ⟨hsD, hsc, hs2⟩ := (mem_centralOmega_iff D s).mp hsO
    have hxS : (x : G) ∈ S := by change (s : G) = (x : G) at hsx; rw [← hsx]; exact s.property
    refine ⟨?_, ?_, ?_⟩
    · rw [hT]
      exact hxS
    · intro t ht
      have htS : (t : G) ∈ S := by rw [hT] at ht; exact ht
      let u : S := ⟨t, htS⟩
      have huD := (hDc u).mp t.property
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, hsx, u] using congrArg (fun a : S => (a : G)) (hsc u huD)
    · apply Subtype.ext
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, hsx] using congrArg (fun a : S => (a : G)) hs2

/-- The local data for the normal-closure argument in the separated case.
The uniqueness of the normal four, elementary-rank lower bound, and normality
of its image in the omega-normalizer quotient are not needed for this step. -/
public theorem exists_centralizerSetup
    {G : Type*} [Group G] [Finite G]
    (hN : Stellmacher.IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hsep : Separated S W z)
    (i : S) (hiW : i ∈ W) (hi : orderOf i = 2) (hiC : i ∉ center S) :
    Nonempty (CentralizerSetup S W i) := by
  have hidx : (centralizer ({i} : Set S)).index = 2 := by
    rw [centralizer_eq_four_centralizer S.isPGroup' hZ W hW i hiW hiC]
    exact NormalFourCentralOmegaTwo.centralizer_index_two S hZ W hW
  have hiZ : ¬ IsConj (i : G) (z : G) := by
    intro h
    exact hiC ((hsep i hiW h.symm).symm ▸ hzC)
  obtain ⟨T, hT⟩ := S.exists_sylow_centralizer_eq_of_index_two_of_not_isConj
    hZ z hzC hz i hi hiZ hidx
  have hOmega := centralizer_omega_center_eq S hno hZ W hW i hiW hiC T hT
  let C := centralizer ({(i : G)} : Set G)
  let E := (W.map (S : Subgroup G).subtype).subgroupOf C
  have hWC : W.map (S : Subgroup G).subtype ≤ C := by
    let : IsElementaryAbelian 2 (W.map (S : Subgroup G).subtype) :=
      IsElementaryAbelian.map_subtype
    intro w hw
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm
      (⟨w, hw⟩ : W.map (S : Subgroup G).subtype)
      (⟨(i : G), mem_map_of_mem _ hiW⟩ : W.map (S : Subgroup G).subtype))
  let : IsElementaryAbelian 2 (W.map (S : Subgroup G).subtype) :=
    IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hWC
  have hET : E ≤ (T : Subgroup C) := by
    rw [hT]
    exact fun _ hx => map_subtype_le W hx
  have hEc : E ≤ centralizer (T : Set C) := by
    intro x hx
    have hxO : x ∈ ((omega₁ (center T) (p := 2)).map (center T).subtype).map
        (T : Subgroup C).subtype := by rw [hOmega]; exact hx
    exact ((mem_centralOmega_iff (T : Subgroup C) x).mp hxO).2.1
  have hsol : Group.IsSolvable C := hN C
    (Theory.GroupTheory.isTwoLocal_involution_centralizer ((orderOf_coe i).trans hi))
  obtain ⟨H, hTH, hEH, hsupp, helem, hcl⟩ :=
    exists_supplement_of_central_elementary_subgroup hsol T E hET hEc
  exact ⟨{
    T := T
    sylow_eq := hT
    omega_center_eq := hOmega
    H := H
    sylow_le := hTH
    four_le := hEH
    supplement := hsupp
    elementary := helem
    closure_le := hcl }⟩

end Stellmacher.Recognition.NormalEightSeparatedCentralizers

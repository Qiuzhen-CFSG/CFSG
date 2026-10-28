module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.OrdinarySource.Marking
public import Theory.GroupTheory.InnerInvolutionSylowCenter
/-!
# Centralizer placement for the original inner component actions

An inner involution fixing the component's actual Sylow subgroup has a
conjugator in that Sylow center, even for a central two-cover. Hence the
centralizer of Z(S_L) centralizes the original ambient involution and lies
in the specified M_L. All subgroup and Sylow transports retain the component
chosen by15.1.19 and the original1.1.5 action.

Applying the complete earlier classifier leaves only the marked A₆ and A₇
outer-action alternatives as possible exceptions to this placement. Their
triple covers are excluded by the proved two-group center. This is placement,
not the narrower15.1.20 model catalogue or a maximal-parabolic identity.

Source: Aschbacher–Smith15.1.20(3), first paragraph, pp.1095–1096, and1.1.5(3).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Chapter15.Section03.Candidates.ComponentStructure
open Chapter15.Section03 Chapter15.Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The actual inner marked involution places the Sylow-center centralizer in M_L. -/
theorem ordinary_inner_centralizer_le (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hsyl : Chapter1.IsSylowIn 2 d.S d.G1)
    (hodd : pPrimeCore 2 d.G1 = ⊥)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {z : G} (hz : z ∈ centralInvolutions T) (hne : z ≠ 1)
    (α : MulAut (d.L.subgroupOf d.G1))
    (ha : ∀ x : d.L.subgroupOf d.G1, ((α x : d.G1) : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := d.L.subgroupOf d.G1)).range) :
    d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) ≤ d.ML := by
  let K := d.L.subgroupOf d.G1
  obtain ⟨P,hP,h115⟩ := d.ordinary_involution_inputs hG hu h hsyl
  have hz115 := h115 z hz hne
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal K hL.1
  have hSQ (x : K) : x ∈ Q ↔ (x : G) ∈ d.SL := by
    change x ∈ (Q : Subgroup K) ↔ (x : G) ∈ d.SL
    rw [hQ]
    change (x : d.G1) ∈ P ↔ (x : G) ∈ d.S ∧ (x : G) ∈ d.L
    constructor
    · intro hx
      exact ⟨hP ▸ mem_map_of_mem d.G1.subtype hx,x.property⟩
    · intro hx
      have hh : (x : G) ∈ (P : Subgroup d.G1).map d.G1.subtype := hP.symm ▸ hx.1
      obtain ⟨y,hy,he⟩ := hh
      exact d.G1.subtype_injective he ▸ hy
  have hfix : ∀ x ∈ Q, α x = x := by
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    rw [ha]
    exact mul_inv_eq_iff_eq_mul.mpr
      (hz115.central (x : G) (hP.symm ▸ ((hSQ x).mp hx).1)).symm
  have hα2 : α ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change ((α (α x) : d.G1) : G) = x
    rw [ha,ha]
    have hz2 : z*z=1 := by
      simpa only [hz115.involution,pow_two] using pow_orderOf_eq_one z
    calc
      z * (z * (x : G) * z⁻¹) * z⁻¹ = (z*z) * x * (z*z)⁻¹ := by group
      _ = x := by rw [hz2]; simp
  let := hL.2
  have hZK : IsPGroup 2 (center K) := by
    have ho := Subgroup.IsSubnormal.pPrimeCore_eq_bot hodd K hL.1
    rw [IsQuasisimple.center_eq_pCore ho]
    exact pCore_isPGroup
  obtain ⟨a,haZ,haα⟩ := MulAut.exists_center_sylow_conjugator_of_inner_involution
    Q α hα2 hi hfix hZK
  have haSL : ((a : K) : G) ∈ d.SL := (hSQ a).mp a.property
  let b : d.SL := ⟨a,haSL⟩
  have hbZ : b ∈ center d.SL := by
    apply mem_center_iff.mpr
    intro x
    let xK : K := ⟨⟨x,d.L_component.1 x.property.2⟩,x.property.2⟩
    let xQ : Q := ⟨xK,(hSQ xK).mpr x.property⟩
    exact Subtype.ext (congrArg (fun y : Q => (((y : K) : d.G1) : G))
      (mem_center_iff.mp haZ xQ))
  rintro x ⟨hxL,hxc⟩
  refine ⟨⟨d.L_component.1 hxL,?_⟩,hxL⟩
  apply hz115.centralizer_le
  apply mem_centralizer_singleton_iff.mpr
  let xK : K := ⟨⟨x,d.L_component.1 hxL⟩,hxL⟩
  have hax : α xK = xK := by
    rw [←haα]
    apply Subtype.ext
    apply Subtype.ext
    change (b : G)*x*(b : G)⁻¹=x
    exact mul_inv_eq_iff_eq_mul.mpr (hxc b (mem_map_of_mem d.SL.subtype hbZ))
  have hh := ha xK
  rw [hax] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
private theorem alternating_action_of_two_center
    {K : Type*} [Group K] (hZ : IsPGroup 2 (center K))
    {α : MulAut K} {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : AlternatingAction α n σ) :
    ∃ e : K ≃* alternatingGroup (Fin n),
      ∀ x : K, (e (α x) : Equiv.Perm (Fin n)) = σ * e x * σ⁻¹ := by
  rcases h with hh | ⟨_,⟨e⟩,_⟩
  · exact hh
  · have hc : Nat.card (center K) = 3 := by
      simpa using Nat.card_congr e.toEquiv
    rcases hZ.card_eq_or_dvd with hone | htwo
    · omega
    · norm_num [hc] at htwo

/-- The original central involution either gives the required centralizer
placement or has one of the two exact alternating actions. No other earlier
model branch can obstruct that placement. -/
theorem ordinary_centralizer_placement_or_alternating (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hsyl : Chapter1.IsSylowIn 2 d.S d.G1)
    (hodd : pPrimeCore 2 d.G1 = ⊥)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {z : G} (hz : z ∈ centralInvolutions T) (hne : z ≠ 1) :
    d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) ≤ d.ML ∨
      ∃ α : MulAut (d.L.subgroupOf d.G1),
        (∀ x : d.L.subgroupOf d.G1, ((α x : d.G1) : G) = z * (x : G) * z⁻¹) ∧
        ((∃ (σ : Equiv.Perm (Fin 6)) (e : d.L.subgroupOf d.G1 ≃* alternatingGroup (Fin 6)),
          σ.IsSwap ∧ ∀ x, (e (α x) : Equiv.Perm (Fin 6)) = σ * e x * σ⁻¹) ∨
         (∃ (σ : Equiv.Perm (Fin 7)) (e : d.L.subgroupOf d.G1 ≃* alternatingGroup (Fin 7)),
          σ.cycleType = {2,2,2} ∧ ∀ x, (e (α x) : Equiv.Perm (Fin 7)) = σ * e x * σ⁻¹)) := by
  obtain ⟨α,ha,hm⟩ := ((d.ordinary_marked_actions hG hu h hsyl hL).2.2 z hz hne).2
  have hi := d.ordinary_inner_centralizer_le hG hu h hsyl hodd hL hz hne α ha
  let := hL.2
  have hZ : IsPGroup 2 (center (d.L.subgroupOf d.G1)) := by
    have ho := Subgroup.IsSubnormal.pPrimeCore_eq_bot hodd (d.L.subgroupOf d.G1) hL.1
    rw [IsQuasisimple.center_eq_pCore ho]
    exact pCore_isPGroup
  cases hm with
  | lie hs hm hin => exact Or.inl (hi hin)
  | two_cover hn hc hm hin => exact Or.inl (hi hin)
  | six σ hs haσ =>
    obtain ⟨e,he⟩ := alternating_action_of_two_center hZ haσ
    exact Or.inr ⟨α,ha,Or.inl ⟨σ,e,hs,he⟩⟩
  | seven σ hs haσ =>
    obtain ⟨e,he⟩ := alternating_action_of_two_center hZ haσ
    exact Or.inr ⟨α,ha,Or.inr ⟨σ,e,hs,he⟩⟩
  | odd hm hin => exact Or.inl (hi hin)
  | sporadic name hn hm hact => exact Or.inl (hi hact.1)
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

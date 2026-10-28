module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.LocalSource
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.PlaneCubic
public import Theory.GroupAction.SubgroupCentralizerCongruence
/-!
# The reflected cubic lies in its original elementary-plane normalizer

The prescribed Sylow nine has a nontrivial stabilizer of the plane's core
eight.  The source reflection belongs to the plane and normalizes the nine,
so the coprime commutator intersection identifies that stabilizer with C_X(t).
Orbit counting modulo three then gives a fixed four in the plane: z is fixed,
and self-centralization of the sixteen excludes a trivial cubic action.
The final consumer constructs the marking and plane from the original source.

Source: Aschbacher, *Sporadic Groups* (1994),45.6–45.7,printed pp.244–245.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G : Type*} [Group G] [Finite G] {z:G}

private theorem exists_original_cubic_plane_stabilizer (R:RootPair z) (h:IsType z)
    (X:Subgroup G) (hX:Nat.card X=9) (hXH:X≤centralizer z)
    (A:Subgroup G) (hA:A≤R.T ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16) :
    ∃a∈X⊓normalizer (A:Set G),orderOf a=3 := by
  let := hA.2.1
  let d:=h.toCentralizerHypothesis.factorData
  have hB:Nonempty (d.leftCore≃*QuaternionGroup 2) := ⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC:Nonempty (d.rightCore≃*QuaternionGroup 2) := ⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi:Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=2 := by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hc:∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b := fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  have hself:Subgroup.centralizer ((d.leftCore⊔d.rightCore:Subgroup G):Set G)≤d.leftCore⊔d.rightCore := by
    rw [d.core_span h.involution,h.toCentralizerHypothesis.centralizer_core]
    exact h.toCentralizerHypothesis.line_le_core
  have hn:centralizer z≤normalizer ((d.leftCore⊔d.rightCore:Subgroup G):Set G) := by
    rw [d.core_span h.involution]
    exact CentralizerHypothesis.centralizer_normalizes_core
  obtain ⟨actors,ha⟩:=independent_cubics_of_nine_subgroup d.leftCore d.rightCore X hB hC hi hc hself hX (hXH.trans hn)
  let C:=A⊓core z
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion (show C≤A from inf_le_left)) (inclusion_injective _)
  have hCcard:Nat.card C=8 := R.plane_inf_core_card h A hA
  have hCQ:C≤d.leftCore⊔d.rightCore := (d.core_span h.involution) ▸ inf_le_right
  obtain ⟨a,hane,han⟩:=actors.exists_nontrivial_normalizing hB hC hi hc C hCcard hCQ
  have hanA:(a:G)∈normalizer (A:Set G) := by
    rw [←R.plane_core_eight_centralizer h A hA]
    exact normalizer_le_normalizer_centralizer C han
  let := actors.elementary
  have ha3:(a:G)^3=1 := elemPow_eq_one_of_isElementaryAbelian (a:G) a.property
  refine ⟨a,⟨ha ▸ a.property,hanA⟩,orderOf_eq_prime ha3 ?_⟩
  exact fun he=>hane (Subtype.ext he)

theorem reflected_line_plane_position (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (A:Subgroup G) (hA:A≤R.T ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16)
    (htA:m.t∈A) :
    let X := (P:Subgroup (centralizer z)).map (centralizer z).subtype
    let U := X⊓Subgroup.centralizer ({m.t}:Set G)
    X⊓normalizer (A:Set G)=U ∧ U≤normalizer (A:Set G) ∧
      Nat.card (A⊓Subgroup.centralizer (U:Set G):Subgroup G)=4 := by
  let X := (P:Subgroup (centralizer z)).map (centralizer z).subtype
  let U := X⊓Subgroup.centralizer ({m.t}:Set G)
  have hX:Nat.card X=9 := h.cubic_sylow_image_card P
  have hXH:X≤centralizer z := map_subtype_le _
  have hd : A⊓X=⊥ := (disjoint_of_coprime_natCard (by rw [hA.2.2,hX];decide)).eq_bot
  have hle : X⊓normalizer (A:Set G)≤U := by
    intro a ha
    refine ⟨ha.1,mem_centralizer_singleton_iff.mpr ?_⟩
    have hbA : ⁅a,m.t⁆∈A := by
      rw [commutatorElement_def]
      exact A.mul_mem ((ha.2 m.t).mp htA) (A.inv_mem htA)
    have hbX : ⁅a,m.t⁆∈X := by
      simpa only [commutatorElement_def,mul_assoc] using
        X.mul_mem ha.1 ((m.t_normalizes a⁻¹).mp (X.inv_mem ha.1))
    exact commutatorElement_eq_one_iff_mul_comm.mp (mem_bot.mp
      (hd ▸ (show ⁅a,m.t⁆∈A⊓X from ⟨hbA,hbX⟩)))
  obtain ⟨a,ha,ha3⟩ := R.exists_original_cubic_plane_stabilizer h X hX hXH A hA
  have hU : Nat.card U=3 := m.common_fixed_card
  have he : X⊓normalizer (A:Set G)=U := eq_of_le_of_card_ge hle (by
    have hc:=card_le_of_le (zpowers_le.mpr ha)
    rw [Nat.card_zpowers,ha3] at hc
    rwa [hU])
  have hUA : U≤normalizer (A:Set G) := he.symm ▸ inf_le_right
  refine ⟨he,hUA,?_⟩
  let F:=A⊓Subgroup.centralizer (U:Set G)
  have hFmod:=card_modEq_card_inf_centralizer U A (IsPGroup.of_card (p:=3) (n:=1) hU) hUA
  have hzA:z∈A := R.E_le_plane h A hA R.z_mem_E
  have hzC:z∈Subgroup.centralizer (U:Set G) := fun u hu=>mem_centralizer_singleton_iff.mp (hXH hu.1)
  have h2F : 2≤Nat.card F := by
    have hc:=card_le_of_le (zpowers_le.mpr (show z∈F from ⟨hzA,hzC⟩))
    simpa only [Nat.card_zpowers,h.involution] using hc
  have hFdiv : Nat.card F∣16 := hA.2.2 ▸ card_dvd_of_le (show F≤A from inf_le_left)
  have hFne : Nat.card F≠16 := by
    intro hh
    have hFA:F=A := eq_of_le_of_card_ge inf_le_left (by rw [hA.2.2,hh])
    have hAC : A≤Subgroup.centralizer (U:Set G) := hFA ▸ inf_le_right
    have hUinA : U≤A := by
      rw [←R.plane_centralizer h A hA]
      exact le_centralizer_iff.mp hAC
    have hc:=card_dvd_of_le hUinA
    rw [hU,hA.2.2] at hc
    norm_num at hc
  have hcases : Nat.card F=1∨Nat.card F=2∨Nat.card F=4∨Nat.card F=8∨Nat.card F=16 := by
    have hh:=Nat.mem_divisors.mpr ⟨hFdiv,(by decide:16≠0)⟩
    have he:Nat.divisors 16={1,2,4,8,16} := by decide
    simpa only [he,Finset.mem_insert,Finset.mem_singleton] using hh
  rw [hA.2.2,Nat.ModEq] at hFmod
  change Nat.card F=4
  change 16%3=Nat.card F%3 at hFmod
  omega
/-- Original-source simultaneous line/plane placement, with local normalizer control. -/
theorem exists_reflected_line_source_geometry (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z)) :
    let X := (P:Subgroup (centralizer z)).map (centralizer z).subtype
    ∃m:CubicNormalizer.ReflectedMarking z X, ∃A:Subgroup G,
      (A≤R.T ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16) ∧
      m.t∈A ∧ m.t∈R.cubicSylow X ∧ m.s∈R.cubicSylow X ∧
      R.cubicSylow X≤normalizer (A:Set G) ∧
      core z ⊓ Subgroup.centralizer
        ((X⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G)=zpowers z ∧
      centralizer z ⊓ Subgroup.centralizer
        ((X⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G)≤normalizer (X:Set G) ∧
      centralizer z ⊓ normalizer
        ((X⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G)=
          centralizer z ⊓ normalizer (X:Set G) ∧
      Nat.card (centralizer z ⊓ normalizer
        ((X⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G):Subgroup G)=72 ∧
      (X⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G)≤normalizer (A:Set G) ∧
      Nat.card (A⊓Subgroup.centralizer
        ((X⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G):Subgroup G)=4 := by
  dsimp only
  obtain ⟨m,A,hA,htA,ht,hs,hTN,hcore,hcent,hnorm,hcard⟩ := R.exists_reflected_line_local_geometry h P
  obtain ⟨_,hUN,hfixed⟩ := R.reflected_line_plane_position h P m A hA htA
  exact ⟨m,A,hA,htA,ht,hs,hTN,hcore,hcent,hnorm,hcard,hUN,hfixed⟩

end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair

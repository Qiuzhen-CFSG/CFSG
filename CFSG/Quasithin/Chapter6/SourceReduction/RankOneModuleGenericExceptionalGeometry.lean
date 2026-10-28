module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericCartan
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.GroupTheory.PResidual.PerfectCover
public import Stellmacher.OmegaOneCenterMap

/-!
# Residual geometry in the exceptional rank-one branch

The Sylow supplement identifies centralization of the central omega subgroup
by the embedded residual with centralization by H. If H has unique maximal
two-local overgroup N_G(O²(H)), a central involution then places the full
omega centralizer inside that normalizer. Thus a quasisimple two-core
quotient makes the literal residual a C-component of the omega centralizer.

The quotient transport uses the actual residual inclusion and relative
subgroup equivalence. No normality in G is asserted. These implications
supply the geometric assembly of the L₃(4) row of 5.2.3(1); the source
centralization and uniqueness assertions of 5.1.14 remain inputs.
Source: Aschbacher--Smith, 5.1.14(1--2), 5.2.3(1), pp.638--639,649.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {H : Subgroup G}

/-- The literal centralizer of Ω₁(Z(T)) in G. -/
abbrev omegaCentralizer (T : Sylow 2 G) : Subgroup G :=
  centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)

omit [Finite G] in
/-- Every element of T centralizes its central omega subgroup. -/
theorem sylow_le_omegaCentralizer : (T : Subgroup G) ≤ omegaCentralizer T := by
  intro t ht z hz
  exact (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm

/-- T already centralizes Ω₁(Z(T)), so only its residual supplement matters. -/
theorem residual_le_omegaCentralizer_iff (hTH : (T : Subgroup G) ≤ H) :
    residual H ≤ omegaCentralizer T ↔ H ≤ omegaCentralizer T := by
  constructor
  · intro hR
    rw [← residual_sup_sylow T H hTH]
    exact sup_le hR sylow_le_omegaCentralizer
  · exact fun hH => (map_subtype_le _).trans hH

/-- Centralization by a uniqueness subgroup bounds the whole omega centralizer. -/
theorem omegaCentralizer_le_of_unique
    (hT : (T : Subgroup G) ≠ ⊥) (hHC : H ≤ omegaCentralizer T)
    {M : Subgroup G}
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N → N = M) :
    omegaCentralizer T ≤ M := by
  let : Nontrivial (T : Subgroup G) := (nontrivial_iff_ne_bot _).mpr hT
  let : Nontrivial (center (T : Subgroup G)) := T.isPGroup'.center_nontrivial
  have hpc := T.isPGroup'.to_subgroup (center (T : Subgroup G))
  obtain ⟨n, hn, he⟩ := hpc.nontrivial_iff_card.mp inferInstance
  have hd : 2 ∣ Nat.card (center (T : Subgroup G)) := by
    rw [he]
    exact dvd_pow_self 2 (Nat.ne_of_gt hn)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hd
  have hz2 : (z : G) ^ 2 = 1 := by
    have hh : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
    exact congrArg (fun x : center (T : Subgroup G) => (x : G)) hh
  have hz1 : (z : G) ≠ 1 := by
    intro heq
    have hh : z = 1 := Subtype.ext (Subtype.ext heq)
    simp only [hh, orderOf_one] at hz
    omega
  have hzZ : (z : G) ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨z.val.property, hz2, ?_⟩
    intro t ht
    exact congrArg (fun x : (T : Subgroup G) => (x : G))
      ((mem_center_iff.mp z.property) ⟨t, ht⟩)
  have hCC : omegaCentralizer T ≤ centralizer ({(z : G)} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr hzZ)
  obtain ⟨N, hCN, hN⟩ := Finite.exists_le_maximal
    (isTwoLocal_involution_centralizer (orderOf_eq_prime hz2 hz1))
  exact (hu N hN (hHC.trans (hCC.trans hCN))) ▸ hCC.trans hCN

/-- Relative normality and the actual quasisimple quotient give the C-component. -/
theorem residual_component_in_omegaCentralizer
    (hRC : residual H ≤ omegaCentralizer T)
    (hCN : omegaCentralizer T ≤ normalizer (residual H : Set G))
    [IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H))] :
    ((residual H).subgroupOf (omegaCentralizer T)).IsCComponent := by
  let e := ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (subgroupOfEquivOfLe hRC).symm
  let eqv := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : IsQuasisimple (((residual H).subgroupOf (omegaCentralizer T)) ⧸
      pCore 2 ((residual H).subgroupOf (omegaCentralizer T))) :=
    IsQuasisimple.of_mulEquiv eqv
  have hn : ((residual H).subgroupOf (omegaCentralizer T)).Normal :=
    normal_subgroupOf_of_le_normalizer hCN
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient hn.isSubnormal
    ((isPPerfect_pResidual 2).of_surjective e.toMonoidHom e.surjective)

/-- Assemble the geometric L₃(4) row from the earlier source centralization
and uniqueness conclusions; the residual embedding is unchanged. -/
theorem linear_residual_component_of_unique
    (hT : (T : Subgroup G) ≠ ⊥) (hTH : (T : Subgroup G) ≤ H)
    (hRC : residual H ≤ omegaCentralizer T)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N →
      N = normalizer (residual H : Set G))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    ∃ KZ : Subgroup (omegaCentralizer T), KZ.IsCComponent ∧
      residual H = KZ.map (omegaCentralizer T).subtype := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hlinear
  let : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
    IsQuasisimple.of_mulEquiv e.symm
  refine ⟨(residual H).subgroupOf (omegaCentralizer T), ?_,
    (map_subgroupOf_eq_of_le hRC).symm⟩
  exact residual_component_in_omegaCentralizer hRC
    (omegaCentralizer_le_of_unique hT ((residual_le_omegaCentralizer_iff hTH).mp hRC) hu)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

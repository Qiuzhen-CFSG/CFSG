module

public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Stellmacher.TwoResidualSylowSupplement
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

/-!
# Source calculations for Lemma 14.1.18

The source defines `Rc = O₂(M ∩ Mc)` (a core, with subscript), and
`Y = O²(⟨Rc^M⟩)` (a residual, with superscript). `sourceResidual` is this
actual subgroup, constructed internally in `M` and mapped back to `G`.

This extension proves the finite-group calculations used in part (2) and the
centralizer supplement needed by Lemma 14.2.21. A nontrivial two-subgroup of
S₃ has order two, and its normal closure is S₃. Residual functoriality and
the residual–Sylow supplement therefore give `M = Y T C_M(V)`.

These are intermediate results. Noncentrality of the intersection core is
an explicit input, to be supplied by 14.1.17(1); the centralizer containment
and distinctness inputs come from 14.1.12. The source's ordering, residual
splitting, and maximal-overgroup assertions are not claimed here. In
particular, none of the older `TerminalCertificate` fields is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp. 980–981, Lemma 14.1.18. The elementary
S₃ normal-subgroup calculation follows the proof already used in
`Theory.GroupTheory.SpecificGroups.PermThreeNormalKernel`.
-/

namespace CFSG.Quasithin.Chapter14.SourcePreliminaries

open Subgroup Stellmacher

private theorem normal_perm_three_eq_top_of_contains_two
    (K D : Subgroup (Equiv.Perm (Fin 3))) [K.Normal]
    (hD : IsPGroup 2 D) (hDK : D ≤ K) (hne : D ≠ ⊥) : K = ⊤ := by
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hd := D.card_subgroup_dvd_card
  rw [hcard] at hd
  have hcop : Nat.Coprime (Nat.card D) 3 := by
    obtain ⟨n, hn⟩ := hD.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hd2 : Nat.card D ∣ 2 := hcop.dvd_mul_right.mp hd
  have hDcard : Nat.card D = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with hc | hc
    · exact (hne (Subgroup.card_eq_one.mp hc)).elim
    · exact hc
  have hKdvd : Nat.card K ∣ 6 := hcard ▸ K.card_subgroup_dvd_card
  have htwo : 2 ∣ Nat.card K := hDcard ▸ Subgroup.card_dvd_of_le hDK
  have hKsmall : Nat.card K ≤ 6 := Nat.le_of_dvd (by decide) hKdvd
  have hKnot : Nat.card K ≠ 2 := by
    intro heq
    have hcentral := central_of_normal_card_two K heq
    have hsmall : ∀ x : Equiv.Perm (Fin 3), (∀ y, y*x=x*y) → x=1 := by decide +kernel
    have hbot : K = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact hsmall x (mem_center_iff.mp (hcentral hx))
    have hc := card_eq_one.mpr hbot
    omega
  have hKcard : Nat.card K = 6 := by
    interval_cases hn : Nat.card K <;> norm_num at *
  apply eq_top_of_card_eq
  rwa [hcard]

private theorem residual_normalClosure_sup_sylow_sup_ker
    {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (D : Subgroup G) (hD : IsPGroup 2 D) (hne : ¬ D ≤ f.ker)
    (T : Sylow 2 G) :
    (twoResidualAmbient (normalClosure (D : Set G)) ⊔ (T : Subgroup G)) ⊔ f.ker = ⊤ := by
  let N := normalClosure (D : Set G)
  have : (N.map f).Normal := (inferInstance : N.Normal).map f hf
  have hN : N.map f = ⊤ := normal_perm_three_eq_top_of_contains_two
    (N.map f) (D.map f) (hD.map f) (map_mono le_normalClosure)
      (fun hb => hne ((map_eq_bot_iff D).mp hb))
  have hres := map_twoResidualAmbient_of_subgroup_image N f ⊤ hN
  have htop : ((twoResidualAmbient N) ⊔ (T : Subgroup G)).map f = ⊤ := by
    rw [Subgroup.map_sup, hres]
    exact twoResidualAmbient_top_sup_sylow (T.mapSurjective hf)
  have h := congrArg (Subgroup.comap f) htop
  simpa only [comap_map_eq, comap_top] using h

/-- The actual subgroup `O²(⟨O₂(M ∩ Mc)^M⟩)` in the ambient group. -/
@[expose] public noncomputable def sourceResidual {G : Type*} [Group G] (M Mc : Subgroup G) : Subgroup G :=
  (twoResidualAmbient (normalClosure (((M ⊓ Mc).pCoreIn 2).subgroupOf M : Set M))).map M.subtype

/-- The source's residual subgroup lies in `M`. -/
public theorem sourceResidual_le {G : Type*} [Group G] (M Mc : Subgroup G) :
    sourceResidual M Mc ≤ M := map_subtype_le _

/-- The normal two-core of the intersection lies in the fixed Sylow subgroup. -/
public theorem intersectionCore_le_sylow {G : Type*} [Group G] (M Mc : Subgroup G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc) :
    (M ⊓ Mc).pCoreIn 2 ≤ (T : Subgroup G) := by
  have h := pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf hTM hTMc))
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le (le_inf hTM hTMc)] using h

/-- The supplement `M = Y T C_M(V)` follows from the S₃ quotient and
14.1.17(1). Its `.le` direction is the decomposition used in 14.2.21. -/
public theorem decomposition_of_intersectionCore_not_centralizing
    {G : Type*} [Group G] [Finite G]
    (M Mc V : Subgroup G) (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    [((centralizer (V : Set G)).subgroupOf M).Normal]
    (he : Nonempty ((M ⧸ (centralizer (V : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3)))
    (hnoncentral : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G)) :
    M = (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊔ (M ⊓ centralizer (V : Set G)) := by
  obtain ⟨e⟩ := he
  let C := (centralizer (V : Set G)).subgroupOf M
  let f := e.toMonoidHom.comp (QuotientGroup.mk' C)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective C)
  have hker : f.ker = C := by
    ext x
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ C
    rw [← e.map_one, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  let D := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
  have hD : IsPGroup 2 D := (isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype
  have hDM : (M ⊓ Mc).pCoreIn 2 ≤ M := (pCoreIn_le 2 _).trans inf_le_left
  have hne : ¬ D ≤ f.ker := by
    rw [hker]
    intro h
    apply hnoncentral
    intro x hx
    exact h (show (⟨x, hDM hx⟩ : M) ∈ D from hx)
  have h := congrArg (Subgroup.map M.subtype)
    (residual_normalClosure_sup_sylow_sup_ker f hf D hD hne (T.subtype hTM))
  rw [Subgroup.map_sup, Subgroup.map_sup, hker, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM,
    ← MonoidHom.range_eq_map, range_subtype] at h
  have hC : C.map M.subtype = M ⊓ centralizer (V : Set G) := by
    rw [subgroupOf_map_subtype, inf_comm]
  rw [hC] at h
  exact h.symm

private theorem proper_perm_three_eq_of_contains_two
    (K D : Subgroup (Equiv.Perm (Fin 3))) (hK : K ≠ ⊤)
    (hD : IsPGroup 2 D) (hDK : D ≤ K) (hne : D ≠ ⊥) : K = D := by
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hcop : Nat.Coprime (Nat.card D) 3 := by
    obtain ⟨n, hn⟩ := hD.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hd2 : Nat.card D ∣ 2 :=
    hcop.dvd_mul_right.mp (show Nat.card D ∣ 6 by rw [← hcard]; exact D.card_subgroup_dvd_card)
  have hDcard : Nat.card D = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with hc | hc
    · exact (hne (Subgroup.card_eq_one.mp hc)).elim
    · exact hc
  have hKdvd : Nat.card K ∣ 6 := hcard ▸ K.card_subgroup_dvd_card
  have htwo : 2 ∣ Nat.card K := hDcard ▸ Subgroup.card_dvd_of_le hDK
  have hKsmall : Nat.card K ≤ 6 := Nat.le_of_dvd (by decide) hKdvd
  have hKnot : Nat.card K ≠ 6 := fun he => hK (eq_top_of_card_eq K (he.trans hcard.symm))
  have hKcard : Nat.card K = 2 := by
    interval_cases hn : Nat.card K <;> norm_num at *
  exact (eq_of_le_of_card_ge hDK (by omega)).symm

private theorem two_subgroup_perm_three_ne_top
    (D : Subgroup (Equiv.Perm (Fin 3))) (hD : IsPGroup 2 D) : D ≠ ⊤ := by
  have hcop : Nat.Coprime (Nat.card D) 3 := by
    obtain ⟨n, hn⟩ := hD.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  intro h
  rw [h] at hcop
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hcop

private theorem eq_sup_inf_ker_of_map_eq
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (D S : Subgroup G) (hDS : D ≤ S) (heq : D.map f = S.map f) :
    S = D ⊔ (S ⊓ f.ker) := by
  apply le_antisymm ?_ (sup_le hDS inf_le_left)
  intro x hx
  obtain ⟨d, hd, hdx⟩ := (show f x ∈ D.map f by
    rw [heq]; exact mem_map_of_mem f hx)
  have hk : d⁻¹ * x ∈ S ⊓ f.ker := by
    refine ⟨S.mul_mem (S.inv_mem (hDS hd)) hx, ?_⟩
    change f (d⁻¹ * x) = 1
    rw [map_mul, map_inv, hdx, inv_mul_cancel]
  have h := (D ⊔ (S ⊓ f.ker)).mul_mem (mem_sup_left hd) (mem_sup_right hk)
  simpa only [mul_inv_cancel_left] using h

private theorem factorization_in_perm_three_preimage
    {G : Type*} [Group G] (f : G →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f) (D S I : Subgroup G)
    (hD : IsPGroup 2 D) (hS : IsPGroup 2 S)
    (hne : ¬ D ≤ f.ker) (hDS : D ≤ S) (hDI : D ≤ I)
    (hkerI : f.ker ≤ I) (hI : I ≠ ⊤) :
    S = D ⊔ (S ⊓ f.ker) ∧ I = f.ker ⊔ D := by
  have hnebar : D.map f ≠ ⊥ := fun h => hne ((map_eq_bot_iff D).mp h)
  have hSmap : S.map f = D.map f := proper_perm_three_eq_of_contains_two
    _ _ (two_subgroup_perm_three_ne_top _ (hS.map f)) (hD.map f) (map_mono hDS) hnebar
  have hImap : I.map f = D.map f := by
    apply proper_perm_three_eq_of_contains_two _ _ ?_ (hD.map f) (map_mono hDI) hnebar
    intro h
    apply hI
    apply map_injective_of_ker_le f hkerI le_top
    rw [h, map_top_of_surjective f hf]
  refine ⟨eq_sup_inf_ker_of_map_eq f D S hDS hSmap.symm, ?_⟩
  rw [eq_sup_inf_ker_of_map_eq f D I hDI hImap.symm, inf_eq_right.mpr hkerI, sup_comm]

/-- The two join equalities in 14.1.18(2), from the preceding noncentrality,
centralizer-containment, and distinct-overgroup conclusions. The quotient
isomorphism is an actual isomorphism with the centralizer quotient. -/
public theorem intersectionCore_factorizations
    {G : Type*} [Group G] [Finite G]
    (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    [((centralizer (V : Set G)).subgroupOf M).Normal]
    (he : Nonempty ((M ⧸ (centralizer (V : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3)))
    (hnoncentral : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G))
    (hCMc : M ⊓ centralizer (V : Set G) ≤ Mc) (hMMc : ¬ M ≤ Mc) :
    (T : Subgroup G) = (M ⊓ Mc).pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G)) ∧
      M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (M ⊓ Mc).pCoreIn 2 := by
  obtain ⟨e⟩ := he
  let C := (centralizer (V : Set G)).subgroupOf M
  let f := e.toMonoidHom.comp (QuotientGroup.mk' C)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective C)
  have hker : f.ker = C := by
    ext x
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ C
    rw [← e.map_one, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  let D := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
  let S := (T : Subgroup G).subgroupOf M
  let I := Mc.subgroupOf M
  have hDM : (M ⊓ Mc).pCoreIn 2 ≤ M := (pCoreIn_le 2 _).trans inf_le_left
  have hD : IsPGroup 2 D := (isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype
  have hne : ¬ D ≤ f.ker := by
    rw [hker]
    intro h
    apply hnoncentral
    intro x hx
    exact h (show (⟨x, hDM hx⟩ : M) ∈ D from hx)
  have hDS : D ≤ S := fun _ hx => intersectionCore_le_sylow M Mc T hTM hTMc hx
  have hDI : D ≤ I := fun _ hx => (pCoreIn_le 2 (M ⊓ Mc) hx).2
  have hCI : f.ker ≤ I := by
    rw [hker]
    exact fun x hx => hCMc ⟨x.property, hx⟩
  have hI : I ≠ ⊤ := by
    intro hh
    apply hMMc
    intro x hx
    exact (show (⟨x, hx⟩ : M) ∈ I by rw [hh]; trivial)
  obtain ⟨h₁, h₂⟩ := factorization_in_perm_three_preimage f hf D S I hD hS hne hDS hDI hCI hI
  have hd : D.map M.subtype = (M ⊓ Mc).pCoreIn 2 := map_subgroupOf_eq_of_le hDM
  have hs : S.map M.subtype = (T : Subgroup G) := map_subgroupOf_eq_of_le hTM
  have hc : f.ker.map M.subtype = M ⊓ centralizer (V : Set G) := by
    rw [hker, subgroupOf_map_subtype, inf_comm]
  have hi : I.map M.subtype = M ⊓ Mc := by rw [subgroupOf_map_subtype, inf_comm]
  constructor
  · have h := congrArg (Subgroup.map M.subtype) h₁
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ M.subtype_injective, hs, hd, hc] at h
    simpa only [← inf_assoc, inf_eq_left.mpr hTM] using h
  · have h := congrArg (Subgroup.map M.subtype) h₂
    simpa only [Subgroup.map_sup, hi, hc, hd] using h

end CFSG.Quasithin.Chapter14.SourcePreliminaries

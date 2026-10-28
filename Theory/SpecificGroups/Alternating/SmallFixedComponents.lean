module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.Alternating.proposition_5_2_7_8
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.SpecificGroups.Alternating.FiveComponents
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Components of involution fixed subgroups in A₆ and A₇

The A₆ fixed groups are solvable: inner involutions have fixed-group order
eight, natural outer involutions fix S₄, and the exceptional involutions
fix D₁₀. The same exclusion holds for every perfect central cover, because
the quotient action is faithful and the fixed-group map has central kernel.

For A₇ every automorphism is permutation induced. The centralizer in S₇ of
a non-transposition involution has order 48, so its alternating fixed subgroup
is solvable. For a transposition, sign correction on its two moved letters
constructs the actual S₅ fixed-group model. The component calculus in S₅
then gives an isomorphism of each component with A₅. All transports retain
the component itself and its relative subnormality.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the inspection
in E.6.22, printed p.254 (PDF p.265); GLS, Volume 3, Proposition 5.2.7 for
the exceptional A₆ involutions. The sign-correction construction extends the
one in `AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed`.
-/

public section

open Subgroup Equiv Equiv.Perm Theory.GroupTheory GLS3.Chapter5
namespace alternatingGroup.SmallFixedComponents

private abbrev A7 := alternatingGroup (Fin 7)
private abbrev S7 := Perm (Fin 7)
private abbrev act : S7 →* MulAut A7 := MulAut.conjNormal

private theorem solvable_of_card_dvd_48 {G : Type*} [Group G] [Finite G]
    (hc : Nat.card G ∣ 48) : Group.IsSolvable G := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three G
  intro p hp hd
  have hd' : p ∣ 2 ^ 4 * 3 := hd.trans hc
  rcases hp.dvd_mul.mp hd' with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)

private def signPair : ℤˣ →* Perm (Fin 2) where
  toFun s := if s = 1 then 1 else swap 0 1
  map_one' := by simp
  map_mul' a b := by
    rcases Int.units_eq_one_or a with rfl | rfl <;>
      rcases Int.units_eq_one_or b with rfl | rfl <;> decide

private def fiveLetterExtension : Perm (Fin 5) →* S7 :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 5 ⊕ Fin 2 ≃ Fin 7)).toMonoidHom.comp
    ((sumCongrHom (Fin 5) (Fin 2)).comp
      ((MonoidHom.id (Perm (Fin 5))).prod (signPair.comp sign)))

private theorem fiveLetterExtension_even (σ : Perm (Fin 5)) :
    fiveLetterExtension σ ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  change sign ((finSumFinEquiv : Fin 5 ⊕ Fin 2 ≃ Fin 7).permCongr
    (Equiv.sumCongr σ (signPair (sign σ)))) = 1
  rw [sign_permCongr, sign_sumCongr]
  rcases Int.units_eq_one_or (sign σ) with h | h <;> rw [h] <;> decide

private theorem fiveLetterExtension_fixed : ∀ σ,
    swap (5 : Fin 7) 6 * fiveLetterExtension σ * (swap 5 6)⁻¹ =
      fiveLetterExtension σ := by
  decide +kernel

private def standardSwapEmbedding : Perm (Fin 5) →* A7 :=
  fiveLetterExtension.codRestrict _ fiveLetterExtension_even

private theorem standardSwapEmbedding_injective : Function.Injective standardSwapEmbedding := by
  intro σ τ h
  have hp := (Equiv.permCongrHom finSumFinEquiv).injective (congrArg Subtype.val h)
  have hq := sumCongrHom_injective hp
  exact congrArg Prod.fst hq

private def standardSwapFixedHom : Perm (Fin 5) →*
    automorphismFixedSubgroup (act (swap 5 6)) :=
  standardSwapEmbedding.codRestrict _ (fun σ => Subtype.ext (fiveLetterExtension_fixed σ))

private theorem standardSwapFixed_card :
    Nat.card (automorphismFixedSubgroup (act (swap 5 6))) = 120 := by
  let C : Subgroup S7 := centralizer {swap 5 6}
  let χ : C →* ℤˣ := sign.comp C.subtype
  have hc : Nat.card C = 240 := by
    rw [nat_card_centralizer]
    have hs : (swap (5 : Fin 7) 6).cycleType = {2} :=
      isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide))
    rw [hs]
    norm_num [Nat.factorial]
  have hχ : Function.Surjective χ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one χ⟩
    · refine ⟨⟨swap 5 6, mem_centralizer_singleton_iff.mpr rfl⟩, ?_⟩
      exact sign_swap (show (5 : Fin 7) ≠ 6 by decide)
  have hi : χ.ker.index = 2 := by
    rw [index_ker, MonoidHom.range_eq_top.mpr hχ, Nat.card_congr topEquiv.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hk := χ.ker.card_mul_index
  rw [hi, hc] at hk
  have he := Nat.card_congr (alternatingCentralizerSignKernelEquivFixedConjNormal
    (swap (5 : Fin 7) 6)).toEquiv
  change Nat.card χ.ker = _ at he
  change Nat.card χ.ker * 2 = 240 at hk
  rw [← he]
  omega

private noncomputable def standardSwapFixedEquiv :
    automorphismFixedSubgroup (act (swap 5 6)) ≃* Perm (Fin 5) :=
  (MulEquiv.ofBijective standardSwapFixedHom
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨
      fun _ _ h => standardSwapEmbedding_injective (congrArg Subtype.val h), by
        rw [standardSwapFixed_card]
        norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]⟩)).symm

private noncomputable def swapFixedEquiv (σ : S7) (hσ : σ.IsSwap) :
    automorphismFixedSubgroup (act σ) ≃* Perm (Fin 5) := by
  have hc : IsConj σ (swap (5 : Fin 7) 6) :=
    isConj_of_cycleType_eq ((isSwap_iff_cycleType.mp hσ).trans
      (isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide))).symm)
  let p := (isConj_iff.mp hc).choose
  have hp := (isConj_iff.mp hc).choose_spec
  refine (fixedSubgroupMulEquivOfCompat (act p) _ _ ?_).trans standardSwapFixedEquiv
  intro g
  have he : act p * act σ = act (swap 5 6) * act p := by
    rw [← map_mul, ← map_mul]
    exact congrArg act (mul_inv_eq_iff_eq_mul.mp hp)
  exact congrArg (fun a : MulAut A7 => a g) he

private theorem nonswap_solvable (σ : S7) (hσ : orderOf σ = 2) (hn : ¬ σ.IsSwap) :
    Group.IsSolvable (automorphismFixedSubgroup (act σ)) := by
  have hc : Nat.card (centralizer ({σ} : Set S7)) = 48 := by
    obtain ⟨k, hk⟩ := cycleType_prime_order (σ := σ) (hσ ▸ Nat.prime_two)
    rw [hσ] at hk
    have hb := σ.sum_cycleType_le
    rw [hk, Multiset.sum_replicate] at hb
    simp only [smul_eq_mul, Fintype.card_fin] at hb
    have hk2 : k ≤ 2 := by omega
    interval_cases k
    · exact (hn (isSwap_iff_cycleType.mpr (by simpa using hk))).elim
    all_goals rw [nat_card_centralizer, hk]; norm_num [Multiset.replicate_succ, Nat.factorial]
  let C := centralizer ({σ} : Set S7)
  let _ : Group.IsSolvable C := solvable_of_card_dvd_48 (by rw [hc])
  exact Group.isSolvable_of_isSolvable_injective
    (f := (alternatingCentralizerSignKernelEquivFixedConjNormal σ).symm.toMonoidHom)
    (alternatingCentralizerSignKernelEquivFixedConjNormal σ).symm.injective

/-- Every involution of Aut(A₇) fixes either a solvable group or a group isomorphic to S₅. -/
theorem seven_fixed_solvable_or_equiv (a : MulAut (alternatingGroup (Fin 7))) (ha : orderOf a = 2) :
    Group.IsSolvable a.fixedSubgroup ∨ Nonempty (a.fixedSubgroup ≃* Perm (Fin 5)) := by
  obtain ⟨σ, hσ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    7 (by decide) (by decide)).surjective a
  have hs : orderOf σ = 2 := (orderOf_injective act
    (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 7 (by decide)) σ).symm.trans
      (hσ ▸ ha)
  subst a
  have hf : (act σ).fixedSubgroup = automorphismFixedSubgroup (act σ) := by
    ext x
    rw [MulAut.mem_fixedSubgroup]
    rfl
  rw [hf]
  by_cases hn : σ.IsSwap
  · exact Or.inr ⟨swapFixedEquiv σ hn⟩
  · exact Or.inl (nonswap_solvable σ hs hn)

/-- Every involution of Aut(A₆) has solvable fixed subgroup. -/
theorem six_fixed_solvable (a : MulAut (alternatingGroup (Fin 6))) (ha : orderOf a = 2) :
    Group.IsSolvable a.fixedSubgroup := by
  open AlternatingSix.ShadowLocal in
    have hf : a.fixedSubgroup = automorphismFixedSubgroup a := by
      ext x
      rw [MulAut.mem_fixedSubgroup]
      rfl
    rw [hf]
    by_cases hn : a ∈ natural
    · by_cases hi : a ∈ AlternatingSix.ShadowLocal.inner
      · obtain ⟨x, hx⟩ := hi
        have ho : orderOf x = 2 := (orderOf_injective (MulAut.conj : A6 →* AutA6)
          inner_injective x).symm.trans (hx ▸ ha)
        rw [← hx]
        exact solvable_of_card_dvd_48 (by rw [inner_involution_fixed_card x ho]; norm_num)
      · obtain ⟨e⟩ := natural_outer_involution_fixed_equiv_symmetricFour a ha hn hi
        let _ : Group.IsSolvable (Perm (Fin 4)) := solvable_of_card_dvd_48 (by
          norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial])
        exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    · obtain ⟨e⟩ := a6_outsideNatural_involution_fixed_equiv_dihedral a ha hn
      let _ : Group.IsSolvable (DihedralGroup 5) := dihedralGroup_isSolvable 5
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

variable {G : Type*} [Group G]

private theorem not_component_solvable {C D : Subgroup G}
    [Group.IsSolvable C] (hD : IsComponentIn D C) : False := by
  let _ := hD.quasisimple
  let _ : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let _ : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  let _ : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hD.1)
  exact Group.IsPerfect.not_isSolvable D inferInstance

/-- An actual A₆ model has no component in any involution fixed subgroup. -/
theorem six_model_no_component
    (e : G ≃* alternatingGroup (Fin 6))
    (a : MulAut G) (ha : orderOf a = 2) (D : Subgroup G)
    (hD : IsComponentIn D a.fixedSubgroup) : False := by
  let _ := six_fixed_solvable (MulAut.congr e a) ((MulAut.congr e).orderOf_eq a |>.trans ha)
  let _ : Group.IsSolvable a.fixedSubgroup := Group.isSolvable_of_isSolvable_injective
    (f := (MulAut.fixedSubgroupCongr e a).toMonoidHom) (MulAut.fixedSubgroupCongr e a).injective
  exact not_component_solvable hD

/-- Every component in an involution fixed subgroup of an actual A₇ model is A₅. -/
theorem seven_component_equiv
    (e : G ≃* alternatingGroup (Fin 7))
    (a : MulAut G) (ha : orderOf a = 2) (D : Subgroup G)
    (hD : IsComponentIn D a.fixedSubgroup) :
    Nonempty (D ≃* alternatingGroup (Fin 5)) := by
  rcases seven_fixed_solvable_or_equiv (MulAut.congr e a)
    ((MulAut.congr e).orderOf_eq a |>.trans ha) with hs | hf
  · let _ := hs
    let _ : Group.IsSolvable a.fixedSubgroup := Group.isSolvable_of_isSolvable_injective
      (f := (MulAut.fixedSubgroupCongr e a).toMonoidHom) (MulAut.fixedSubgroupCongr e a).injective
    exact (not_component_solvable hD).elim
  · obtain ⟨f⟩ := hf
    let j := (MulAut.fixedSubgroupCongr e a).trans f
    obtain ⟨d⟩ := component_symmetric_five_equiv _ (hD.2.map_equiv j)
    exact ⟨((subgroupOfEquivOfLe hD.1).symm.trans
      (j.subgroupMap (D.subgroupOf a.fixedSubgroup))).trans d⟩

/-- The same exclusion holds in every perfect central cover of A₆. -/
theorem six_cover_no_component [Group.IsPerfect G]
    (e : (G ⧸ center G) ≃* alternatingGroup (Fin 6))
    (a : MulAut G) (ha : orderOf a = 2) (D : Subgroup G)
    (hD : IsComponentIn D a.fixedSubgroup) : False := by
  let b := MulAut.centralQuotientAction e a
  have hb : orderOf b = 2 :=
    (orderOf_injective _ (MulAut.centralQuotientAction_injective e) a).trans ha
  let _ := six_fixed_solvable b hb
  let q : G →* alternatingGroup (Fin 6) := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  let f : a.fixedSubgroup →* b.fixedSubgroup :=
    (q.comp a.fixedSubgroup.subtype).codRestrict _ (by
      intro x
      rw [MulAut.mem_fixedSubgroup]
      change MulAut.centralQuotientAction e a (e (QuotientGroup.mk' (center G) x)) = _
      rw [MulAut.centralQuotientAction_apply, (MulAut.mem_fixedSubgroup _ _).mp x.property]
      rfl)
  have hker (x : f.ker) : (x.val.val : G) ∈ center G := by
    have he : e (QuotientGroup.mk' (center G) x.val.val) = 1 :=
      congrArg Subtype.val x.property
    exact (QuotientGroup.eq_one_iff _).mp (e.map_eq_one_iff.mp he)
  let j : f.ker →* center G :=
    (a.fixedSubgroup.subtype.comp f.ker.subtype).codRestrict _ hker
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : center G => (z : G)) h
  let _ : Group.IsSolvable (center G) := Group.isSolvable_of_comm fun x y =>
    Subtype.ext ((mem_center_iff.mp x.property y).symm)
  let _ : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective (f := j) hj
  let _ : Group.IsSolvable a.fixedSubgroup := Group.isSolvable_of_ker_le_range f.ker.subtype f
    (by simp)
  exact not_component_solvable hD

end alternatingGroup.SmallFixedComponents

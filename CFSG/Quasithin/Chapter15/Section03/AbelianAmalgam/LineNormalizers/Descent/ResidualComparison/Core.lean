module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.ResidualDefinitions
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.LocalCollapse
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction
public import Mathlib.Data.Finite.Perm

/-!
# The common residual in the descent to the original line normalizer

The action on the three cosets of `M_E` kills every element of order prime
to six, without requiring `M_E` to be normal. Such an element therefore
belongs to `M`, and its image in the compatible natural orthogonal action
is trivial: the concrete actor has order 72. Its kernel is the actual
centralizer of `V`. Comparing generators gives the three equal residuals.

Their relative normality and the local characteristic-two obstruction kill
the common residual. Cauchy's theorem and the earlier `3'`-group
centralizer conclusion then make the centralizer a normal two-subgroup
of `M`, contained in the specified Sylow subgroup. All occurrences of
`G_E` retain the original `N_G(E)`.

Inputs are the preceding index-three descent, the compatible action from
15.3.2, `N_G(V) ≤ M`, maximal two-locality and characteristic two,
and the `3'`-group conclusion of 15.3.49(4). No residual collapse or
terminal product is included among the hypotheses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1121–1122, 1142, and the descent paragraph on p.1154
(PDF p.1171). The residual convention is fixed in `ResidualDefinitions`.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent
variable {G : Type*} [Group G] [Finite G]

/-- The faithful orthogonal actor has no nonidentity element of order prime to six. -/
theorem orthogonal_primeToSix_eq_one (a : OrthogonalActor)
    (ha : Nat.Coprime (orderOf a) 6) : a = 1 := by
  have hplane : Nat.card OrthogonalPlaneActor = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hc : Nat.card OrthogonalActor = 72 := by
    rw [RegularWreathProduct.card, hplane]
    norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card]
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (ha.pow_right 3) dvd_rfl
    ((orderOf_dvd_natCard a).trans (hc ▸ (by decide : 72 ∣ 6 ^ 3)))

private theorem mem_of_index_three (H : Subgroup G) (hH : H.index = 3)
    (x : G) (hx : Nat.Coprime (orderOf x) 6) : x ∈ H := by
  let f := MulAction.toPermHom G (G ⧸ H)
  have hc : Nat.card (Equiv.Perm (G ⧸ H)) = 6 := by
    rw [Nat.card_perm, ← H.index_eq_card, hH]
    rfl
  have hd : orderOf (f x) ∣ 6 := hc ▸ orderOf_dvd_natCard (f x)
  have ho : orderOf (f x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hx (orderOf_map_dvd f x) hd
  have hk : x ∈ f.ker := orderOf_eq_one_iff.mp ho
  rw [← H.normalCore_eq_ker] at hk
  exact H.normalCore_le hk

/-- Compare generators through the three cosets and the faithful orthogonal action. -/
theorem residual_equalities (M V E : Subgroup G) (hEV : E ≤ V)
    (hNM : normalizer (V : Set G) ≤ M)
    (d : NaturalOrthogonalAction M V)
    (hi : (lineM M E).relIndex (lineNormalizer E) = 3) :
    twoThreeResidual (lineNormalizer E) = twoThreeResidual (centralizer (V : Set G)) ∧
      twoThreeResidual (centralizer (V : Set G)) = twoThreeResidual M := by
  have hCM : centralizer (V : Set G) ≤ M := (Subgroup.centralizer_le_normalizer _).trans hNM
  have hCG : centralizer (V : Set G) ≤ lineNormalizer E :=
    (centralizer_le hEV).trans (Subgroup.centralizer_le_normalizer _)
  have hgen (x : G) (hx : x ∈ M) (ho : Nat.Coprime (orderOf x) 6) :
      x ∈ centralizer (V : Set G) := by
    have ho' : Nat.Coprime (orderOf (⟨x, hx⟩ : M)) 6 := by
      exact (orderOf_injective M.subtype M.subtype_injective ⟨x, hx⟩) ▸ ho
    have ha := orthogonal_primeToSix_eq_one (d.actor ⟨x, hx⟩) (ho'.of_dvd_left (orderOf_map_dvd _ _))
    have hk : (⟨x, hx⟩ : M) ∈ d.actor.ker := ha
    rw [d.ker_actor] at hk
    exact hk
  have hMC : twoThreeResidual M ≤ twoThreeResidual (centralizer (V : Set G)) := by
    apply (closure_le _).mpr
    intro x hx
    exact subset_closure ⟨hgen x hx.1 hx.2, hx.2⟩
  refine ⟨le_antisymm ?_ (twoThreeResidual_mono hCG),
    le_antisymm (twoThreeResidual_mono hCM) hMC⟩
  apply (closure_le _).mpr
  intro x hx
  have hm : x ∈ lineM M E := by
    have ho : Nat.Coprime (orderOf (⟨x, hx.1⟩ : lineNormalizer E)) 6 := by
      exact (orderOf_injective (lineNormalizer E).subtype
        (lineNormalizer E).subtype_injective ⟨x, hx.1⟩) ▸ hx.2
    exact mem_of_index_three ((lineM M E).subgroupOf (lineNormalizer E)) hi
      ⟨x, hx.1⟩ ho
  exact subset_closure ⟨hgen x hm.1 hx.2, hx.2⟩

private theorem isTwoGroup_of_residual_eq_bot (C : Subgroup G)
    (hres : twoThreeResidual C = ⊥) (h3 : ¬ 3 ∣ Nat.card C) : IsPGroup 2 C := by
  apply isPGroup_iff_card_dvd_pow.mpr
  refine ⟨Nat.card C, (Nat.dvd_pow_self_iff (Nat.card_pos.ne') (by decide)).mpr ?_⟩
  intro q hq
  obtain ⟨hqprime, hqcard, _⟩ := Nat.mem_primeFactors.mp hq
  have hq2 : q = 2 := by
    by_contra hn2
    have hn3 : q ≠ 3 := fun he => h3 (he ▸ hqcard)
    have hq6 : Nat.Coprime q 6 :=
      ((Nat.coprime_primes hqprime Nat.prime_two).mpr hn2).mul_right
        ((Nat.coprime_primes hqprime Nat.prime_three).mpr hn3)
    let : Fact q.Prime := ⟨hqprime⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) q hqcard
    have hxo : orderOf (x : G) = q :=
      (orderOf_injective C.subtype C.subtype_injective x).trans hx
    have hxr : (x : G) ∈ twoThreeResidual C := subset_closure ⟨x.property, hxo ▸ hq6⟩
    rw [hres, mem_bot] at hxr
    have hxone : x = 1 := Subtype.ext hxr
    exact hqprime.ne_one (hx.symm.trans (hxone ▸ orderOf_one))
  simp only [hq2, Nat.mem_primeFactors_of_ne_zero (by decide : 2 ≠ 0)]
  exact ⟨Nat.prime_two, dvd_rfl⟩

/-- The common residual is normal in both original overgroups. -/
theorem common_residual_normal (M V E : Subgroup G) (hEV : E ≤ V)
    (hNM : normalizer (V : Set G) ≤ M) (d : NaturalOrthogonalAction M V)
    (hi : (lineM M E).relIndex (lineNormalizer E) = 3) :
    ((twoThreeResidual (centralizer (V : Set G))).subgroupOf M).Normal ∧
      ((twoThreeResidual (centralizer (V : Set G))).subgroupOf (lineNormalizer E)).Normal := by
  obtain ⟨heG, heM⟩ := residual_equalities M V E hEV hNM d hi
  constructor
  · rw [heM]
    exact twoThreeResidual_normal M
  · rw [← heG]
    exact twoThreeResidual_normal _

/-- Characteristic two and maximal two-locality kill the actual common residual. -/
theorem common_residual_eq_bot (M V E : Subgroup G) (hEV : E ≤ V)
    (hNM : normalizer (V : Set G) ≤ M) (d : NaturalOrthogonalAction M V)
    (hi : (lineM M E).relIndex (lineNormalizer E) = 3)
    (hM : IsMaximalTwoLocal M)
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hout : ¬ lineNormalizer E ≤ M) :
    twoThreeResidual (centralizer (V : Set G)) = ⊥ := by
  have hCM : centralizer (V : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer _).trans hNM
  have hCG : centralizer (V : Set G) ≤ lineNormalizer E :=
    (centralizer_le hEV).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨hnM, hnG⟩ := common_residual_normal M V E hEV hNM d hi
  exact common_normal_eq_bot M (lineNormalizer E) _ hM hchar hout
    ((twoThreeResidual_le _).trans hCM) ((twoThreeResidual_le _).trans hCG) hnM hnG

/-- The full centralizer is the centralizer in the fixed Sylow subgroup. -/
theorem centralizer_eq_sylow_centralizer (M V E : Subgroup G) (hEV : E ≤ V)
    (hNM : normalizer (V : Set G) ≤ M)
    (d : NaturalOrthogonalAction M V)
    (hi : (lineM M E).relIndex (lineNormalizer E) = 3)
    (hM : IsMaximalTwoLocal M)
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hout : ¬ lineNormalizer E ≤ M)
    (h3 : ¬ 3 ∣ Nat.card ↥(M ⊓ centralizer (V : Set G)))
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) :
    centralizer (V : Set G) = (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  let C := centralizer (V : Set G)
  have hCM : C ≤ M := (Subgroup.centralizer_le_normalizer _).trans hNM
  have hr := common_residual_eq_bot M V E hEV hNM d hi hM hchar hout
  have h3' : ¬ 3 ∣ Nat.card C := by
    change ¬ 3 ∣ Nat.card ↥(M ⊓ C) at h3
    rwa [inf_of_le_right hCM] at h3
  have h2 := isTwoGroup_of_residual_eq_bot C hr h3'
  have hnC : (C.subgroupOf M).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hCM).mpr
    exact d.normalizes.trans ((normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (V : Set G))).mp inferInstance)
  let : (C.subgroupOf M).Normal := hnC
  have hCT : C ≤ (T : Subgroup G) := by
    intro x hx
    have h2M : IsPGroup 2 (C.subgroupOf M) := h2.comap_subtype
    exact h2M.le_sylow_of_normal (T.subtype hTM) (show
      (⟨x, hCM hx⟩ : M) ∈ C.subgroupOf M from hx)
  exact (inf_of_le_right hCT).symm

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent

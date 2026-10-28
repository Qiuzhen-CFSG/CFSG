module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.BenderNormalizers
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Residual containment and the Borel lift in the linear-two branch

The three-elements generate a two-perfect group with normal two-subgroup
and three-group quotient. Thus the earlier identity K₀ = O^{3′}(H)
puts L₁ in K₀. A chosen subgroup B₀* of K₀* is lifted inside K₀
through the literal H/O₂(H) map. Its solvability lifts through the actual
two-core kernel. If L₁T normalizes that lift, its solvable join with L₁T
lies in M by the earlier universal conclusion of 13.8.13.

The concrete PSL₂ Cartan divisibility forces an even field exponent.
The final arithmetic deduction forces n = 2 once inversion has made the
Cartan order a three-power. Construction and normalization of the chosen
Borel, the inversion argument, rank three calculation and marked diagonal
subgroups remain source-assembly obligations. B denotes O²(B₀), never O₂(B₀).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.16(1), printed p.952 (PDF p.969).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo
variable {G : Type*} [Group G]

/-- The literal restriction of H → H/O₂(H) to the component orbit. -/
def orbitStarMap (H K₀ : Subgroup G) (hK : K₀ ≤ H) : K₀ →* Source.Hstar H :=
  (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hK)

/-- Lift a Borel inside K₀, not by taking its full preimage in H. -/
def borelLift (H K₀ : Subgroup G) (hK : K₀ ≤ H)
    (Bstar : Subgroup (Source.Hstar H)) : Subgroup G :=
  (Bstar.comap (orbitStarMap H K₀ hK)).map K₀.subtype

theorem borelLift_le (H K₀ : Subgroup G) (hK : K₀ ≤ H)
    (Bstar : Subgroup (Source.Hstar H)) : borelLift H K₀ hK Bstar ≤ K₀ :=
  map_subtype_le _

theorem orbitStarMap_range (H K₀ : Subgroup G) (hK : K₀ ≤ H) :
    (orbitStarMap H K₀ hK).range = Source.starImage H K₀ := by
  rw [orbitStarMap, MonoidHom.range_comp, inclusion_range]
  rfl

/-- The lift maps back to the chosen Borel when it lies in K₀*. -/
theorem borelLift_starImage (H K₀ : Subgroup G) (hK : K₀ ≤ H)
    (Bstar : Subgroup (Source.Hstar H)) (hB : Bstar ≤ Source.starImage H K₀) :
    Source.starImage H (borelLift H K₀ hK Bstar) = Bstar := by
  have hl : borelLift H K₀ hK Bstar ≤ H := (borelLift_le H K₀ hK Bstar).trans hK
  have he : (borelLift H K₀ hK Bstar).subgroupOf H =
      (Bstar.comap (orbitStarMap H K₀ hK)).map (inclusion hK) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hl, map_map]
    rfl
  rw [Source.starImage, he, map_map]
  change (Bstar.comap (orbitStarMap H K₀ hK)).map (orbitStarMap H K₀ hK) = _
  rw [map_comap_eq, orbitStarMap_range, inf_eq_right.mpr hB]

/-- Solvability lifts through the actual two-core kernel. -/
theorem borelLift_solvable [Finite G] (H K₀ : Subgroup G) (hK : K₀ ≤ H)
    (Bstar : Subgroup (Source.Hstar H)) [Group.IsSolvable Bstar] :
    Group.IsSolvable (borelLift H K₀ hK Bstar) := by
  let f := orbitStarMap H K₀ hK
  let j : f.ker →* pCore 2 H :=
    ((inclusion hK).comp f.ker.subtype).codRestrict _ (by
      intro x
      exact (QuotientGroup.eq_one_iff _).mp x.property)
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 H => ((z : H) : G)) h
  let _ := pCore_isNilpotent (p := 2) (G := H)
  let _ : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hj
  let _ : Group.IsSolvable (Bstar.comap f) := isSolvable_comap_of_solvable_ker f Bstar
  exact Group.isSolvable_of_surjective (K₀.subtype.subgroupMap_surjective (Bstar.comap f))

private theorem solvable_join_of_normalizes (A B : Subgroup G)
    [Group.IsSolvable A] [Group.IsSolvable B]
    (hn : B ≤ normalizer (A : Set G)) : Group.IsSolvable (A ⊔ B : Subgroup G) := by
  let A' := A.subgroupOf (A ⊔ B)
  let B' := B.subgroupOf (A ⊔ B)
  let _ : A'.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  let _ : Group.IsSolvable A' := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show A ≤ A ⊔ B from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show A ≤ A ⊔ B from le_sup_left)).injective
  let _ : Group.IsSolvable B' := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show B ≤ A ⊔ B from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ A ⊔ B from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top A' B'
  apply map_injective (A ⊔ B).subtype_injective
  simp [A', B', Subgroup.map_sup, le_sup_left, le_sup_right, ← MonoidHom.range_eq_map]

/-- Apply 13.8.13 to the normalized solvable overgroup B₀L₁T. No
solvability of that overgroup is assumed: it follows from its two factors. -/
theorem borelLift_le_M [Finite G] (H K₀ L₁ T G₁ M : Subgroup G)
    (hK : K₀ ≤ H) (Bstar : Subgroup (Source.Hstar H))
    [Group.IsSolvable Bstar] [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (hn : L₁ ⊔ T ≤ normalizer (borelLift H K₀ hK Bstar : Set G))
    (hKG : K₀ ≤ G₁) (hbase : L₁ ⊔ T ≤ G₁)
    (hex : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M) : borelLift H K₀ hK Bstar ≤ M := by
  let _ := borelLift_solvable H K₀ hK Bstar
  have hs := solvable_join_of_normalizes (borelLift H K₀ hK Bstar) (L₁ ⊔ T) hn
  exact le_sup_left.trans (hex _ le_sup_right
    (sup_le ((borelLift_le H K₀ hK Bstar).trans hKG) hbase) hs)

/-- A two-perfect group with a normal two-subgroup and three-group quotient
is generated by its three-elements. -/
theorem three_generated_of_twoPerfect [Finite G]
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
    (hquot : IsPGroup 3 (G ⧸ R)) (hG : IsPPerfect 2 G) :
    primeToResidual 3 G = ⊤ := by
  let P : Sylow 3 G := Classical.choice inferInstance
  let q := QuotientGroup.mk' R
  let S := P.mapSurjective (QuotientGroup.mk'_surjective R)
  have hmap : (P : Subgroup G).map q = ⊤ :=
    top_unique ((hquot.to_subgroup ⊤).le_sylow_of_normal S)
  have hRP : (P : Subgroup G) ⊔ R = ⊤ := by
    have h := congrArg (fun A : Subgroup (G ⧸ R) => A.comap q) hmap
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using h
  have hPN : (P : Subgroup G) ≤ primeToResidual 3 G := by
    intro x hx
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨x, hx⟩
    exact mem_primeToResidual_of_pow (congrArg Subtype.val hn)
  have hNR : primeToResidual 3 G ⊔ R = ⊤ :=
    top_unique (hRP.symm.le.trans (sup_le_sup_right hPN R))
  exact hG _ inferInstance (isPGroup_quotient_of_sup_eq_top _ R hR hNR)

/-- The residual conclusion of 1.2.2(a) puts every 3-generated marked
subgroup of H inside the component orbit. -/
theorem marked_le_orbit_of_residual (H K₀ L₁ : Subgroup G) (hLH : L₁ ≤ H)
    (hL : primeToResidual 3 L₁ = ⊤)
    (hres : (primeToResidual 3 H).map H.subtype = K₀) : L₁ ≤ K₀ := by
  have hL' : primeToResidual 3 (L₁.subgroupOf H) = ⊤ := by
    have he := map_primeToResidual (p := 3) (subgroupOfEquivOfLe hLH).symm
    rw [hL, map_top_of_surjective _ (subgroupOfEquivOfLe hLH).symm.surjective] at he
    exact he.symm
  have hm := map_mono (f := H.subtype) (le_primeToResidual_of_eq_top 3 (L₁.subgroupOf H) hL')
  rwa [map_subgroupOf_eq_of_le hLH, hres] at hm

/-- L₁ ≤ K₀ from the source residual identity and the marked local
structure, with no containment assumption hidden in the input. -/
theorem marked_le_orbit [Finite G] (H K₀ L₁ : Subgroup G) (hLH : L₁ ≤ H)
    (hL : IsPPerfect 2 L₁) (hq : IsPGroup 3 (L₁ ⧸ pCore 2 L₁))
    (hres : (primeToResidual 3 H).map H.subtype = K₀) : L₁ ≤ K₀ :=
  marked_le_orbit_of_residual H K₀ L₁ hLH
    (three_generated_of_twoPerfect (pCore 2 L₁) pCore_isPGroup hq hL) hres

/-- The actual rank-one Cartan divisibility forces an even field exponent. -/
theorem even_parameter_of_three_subgroup {Q : Type*} [Group Q] [Finite Q]
    {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (S : Sylow 2 (Q × Q)) (A : Subgroup (Q × Q))
    (hA : IsPGroup 3 A) (hne : A ≠ ⊥)
    [Group.IsSolvable (A ⊔ (S : Subgroup (Q × Q)) : Subgroup (Q × Q))] :
    A ≤ normalizer (S : Set (Q × Q)) ∧ Even n := by
  obtain ⟨hle, hm⟩ := Chapter1.XiEmbedding.SwappedSylow.binary_model_prod_restrictions
    hn hmodel (by decide : Odd 3) S A hA hne
  refine ⟨hle, ?_⟩
  have hz : (2 : ZMod 3) ^ n = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff (2 ^ n) 1 3).mpr hm
  have he : (2 : ZMod 3) = -1 := by decide
  rw [he] at hz
  exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp hz
/-- Once inversion forces the odd Cartan order to be a three-power, its
even field exponent is two. -/
theorem parameter_eq_two_of_torus_three_power {n : ℕ} (hn : 2 ≤ n)
    (heven : Even n) (hthree : ∃ a : ℕ, 2 ^ n - 1 = 3 ^ a) : n = 2 := by
  obtain ⟨m, rfl⟩ := heven
  obtain ⟨a, ha⟩ := hthree
  have hm : 1 ≤ m := by omega
  have hq : 2 ≤ 2 ^ m := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm
  have hmul : (2 ^ m - 1) * (2 ^ m + 1) = 3 ^ a := by
    rw [pow_add] at ha
    have hsub : 2 ^ m - 1 + 1 = 2 ^ m := Nat.sub_add_cancel (by omega)
    have hsub₂ : 2 ^ m * 2 ^ m - 1 + 1 = 2 ^ m * 2 ^ m :=
      Nat.sub_add_cancel (by nlinarith)
    nlinarith
  have hlo : 2 ^ m - 1 ∣ 3 ^ a := hmul ▸ dvd_mul_right _ _
  have hhi : 2 ^ m + 1 ∣ 3 ^ a := hmul ▸ dvd_mul_left _ _
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hlo
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hhi
  have hjpos : j ≠ 0 := by intro he; simp [he] at hj
  have hdivhi : 3 ∣ 2 ^ m + 1 := by
    rw [hj]
    exact dvd_pow_self 3 hjpos
  have hiz : i = 0 := by
    by_contra hi0
    have hdivlo : 3 ∣ 2 ^ m - 1 := by
      rw [hi]
      exact dvd_pow_self 3 hi0
    omega
  have hpow : 2 ^ m = 2 := by simp [hiz] at hi; omega
  have hmlt : m < 2 := by
    by_contra hh
    have hge : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hpow] at hge
    norm_num at hge
  omega
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo

end

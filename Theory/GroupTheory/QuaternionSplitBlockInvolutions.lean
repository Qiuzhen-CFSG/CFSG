module

public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionTypes
public import Theory.GroupTheory.QuaternionSwapCommutator
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.ElementaryAbelian.Join

/-!
# Elementary sixteen and complement extension for a quaternion involution

For an outside involution interchanging two commuting quaternion factors,
the actual subgroup A = ⟨a, [U,a]⟩ is elementary abelian of order sixteen.
The proof identifies [U,a] with the elementary fixed diagonal and adjoins a.
The intrinsic version retains the given embeddings of the factors in U.

If a normalizes a complement D to V inside U, then D⟨a⟩ is a genuine
complement to V inside U⟨a⟩. Its intersection with U is exactly D. The
construction uses the actual subgroups, not merely an abstract splitting
or a cardinality assertion. Constructing the invariant D from the marked
a₂ action is a separate calculation; it is not assumed to follow from the
order of A alone.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 14.4.4, printed p.1007. This is the local step before Gaschütz.
-/

open scoped Pointwise commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

private theorem mem_zpowers_of_square_eq_one {a x : G} (ha : a ^ 2 = 1)
    (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  classical
  have hf : IsOfFinOrder a := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, ha⟩
  by_cases h1 : a = 1
  · simpa [h1] using hx
  have ho : orderOf a = 2 := orderOf_eq_prime ha h1
  rw [hf.mem_zpowers_iff_mem_range_orderOf, ho] at hx
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  have hi2 := Finset.mem_range.mp hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · exact Or.inl (by simpa using hix.symm)
  · exact Or.inr (by simpa using hix.symm)

/-- Adjoining an involution outside U does not enlarge a subgroup D inside U
when intersecting back with U, provided the involution normalizes D. -/
public theorem inf_sup_zpowers_of_normalizing_involution (U D : Subgroup G)
    (hDU : D ≤ U) (a : G) (ha : a ^ 2 = 1) (hout : a ∉ U)
    (hn : a ∈ normalizer (D : Set G)) : U ⊓ (D ⊔ zpowers a) = D := by
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (D : Set G) * (zpowers a : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left D (zpowers a) (zpowers_le.mpr hn)]
      exact hx.2
    obtain ⟨d, hd, b, hb, rfl⟩ := hp
    rcases mem_zpowers_of_square_eq_one ha hb with rfl | rfl
    · simpa using hd
    · exact False.elim (hout (by
        have hh := U.mul_mem (U.inv_mem (hDU hd)) hx.1
        simpa only [inv_mul_cancel_left] using hh))
  · exact le_inf hDU le_sup_left

/-- An invariant complement inside an index-two normal subgroup extends by
the chosen outside involution to a genuine complement in the whole group. -/
public theorem isComplement_sup_zpowers_of_invariant [Finite G]
    (U V D : Subgroup G) [U.Normal] [V.Normal]
    (hDU : D ≤ U) (hVD : V ⊔ D = U) (hd : Disjoint V D)
    (a : G) (ha : a ^ 2 = 1) (hout : a ∉ U)
    (hn : a ∈ normalizer (D : Set G)) (hgen : U ⊔ zpowers a = ⊤) :
    V.IsComplement' (D ⊔ zpowers a) := by
  have hVU : V ≤ U := hVD ▸ le_sup_left
  have hdisj : Disjoint V (D ⊔ zpowers a) := disjoint_def.mpr (by
    intro x hxV hx
    have hxD : x ∈ D := (inf_sup_zpowers_of_normalizing_involution U D hDU a ha hout hn) ▸
      (show x ∈ U ⊓ (D ⊔ zpowers a) from ⟨hVU hxV, hx⟩)
    exact disjoint_def.mp hd hxV hxD)
  have hUD : Nat.card U = Nat.card V * Nat.card D := by
    rw [← hVD]
    exact card_sup_eq_mul_of_normalizes_of_disjoint V D
      (by rw [V.normalizer_eq_top]; exact le_top) hd
  have hD : Nat.card (D ⊔ zpowers a : Subgroup G) = 2 * Nat.card D :=
    card_sup_zpowers_of_normalizing_involution D a ha (fun h => hout (hDU h)) hn
  have hG : Nat.card G = 2 * Nat.card U := by
    have h := card_sup_zpowers_of_normalizing_involution U a ha hout
      (by rw [U.normalizer_eq_top]; trivial)
    rwa [hgen, card_top] at h
  apply isComplement'_of_card_mul_and_disjoint ?_ hdisj
  rw [hD, hG, hUD]
  ac_rfl

/-- The source subgroup A is the elementary sixteen obtained by adjoining
the swapping involution to its exact commutator with the quaternion core. -/
public theorem quaternion_swap_elementary_sixteen
    (B C : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (a : G) (ha : a ^ 2 = 1) (hout : a ∉ B ⊔ C)
    (hswap : B.map (MulAut.conj a).toMonoidHom = C) :
    ⁅B ⊔ C, zpowers a⁆ = (B ⊔ C) ⊓ centralizer ({a} : Set G) ∧
    IsElementaryAbelian 2 (zpowers a ⊔ ⁅B ⊔ C, zpowers a⁆ : Subgroup G) ∧
    Nat.card (zpowers a ⊔ ⁅B ⊔ C, zpowers a⁆ : Subgroup G) = 16 := by
  let θ : B ≃* C := (B.equivMapOfInjective (MulAut.conj a).toMonoidHom
    (MulAut.conj a).injective).trans (MulEquiv.subgroupCongr hswap)
  have hθ (b : B) : a * (b : G) * a⁻¹ = (θ b : G) := rfl
  have hf := quaternion_diagonal_eq_inf_centralizer_of_swap B C θ hinter hcomm a ha hθ
  have he := quaternion_diagonal_elementary_eight B C hB.some θ hinter hcomm
  let F := (B ⊔ C) ⊓ centralizer ({a} : Set G)
  have hFe : IsElementaryAbelian 2 F :=
    Eq.mp (congrArg (fun S : Subgroup G => IsElementaryAbelian 2 S) hf.symm) he.1
  have hFc : Nat.card F = 8 := by dsimp [F]; rw [hf]; exact he.2.1
  have hc := commutator_zpowers_eq_fixed_of_quaternion_swap B C hB hinter hcomm a ha hswap
  refine ⟨hc, ?_, ?_⟩
  · rw [hc, sup_comm]
    let := hFe
    let : IsElementaryAbelian 2 (zpowers a) := IsElementaryAbelian.zpowers_of_pow_eq_one ha
    apply IsElementaryAbelian.sup_of_le_centralizer
    apply zpowers_le.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx.2
  · rw [hc, sup_comm]
    change Nat.card (F ⊔ zpowers a : Subgroup G) = 16
    rw [card_sup_zpowers_of_normalizing_involution F a ha
      (fun h => hout h.1) ((centralizer_le_normalizer _) (by
        intro x hx
        exact mem_centralizer_singleton_iff.mp hx.2)), hFc]

/-- Intrinsic version retaining the actual embedded core and its factors. -/
public theorem QuaternionCentralProductData.elementary_sixteen_of_swap
    (U : Subgroup G) (d : QuaternionCentralProductData U)
    (a : G) (ha : a ^ 2 = 1) (hout : a ∉ U)
    (hswap : (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom =
      d.right.map U.subtype) :
    ⁅U, zpowers a⁆ = U ⊓ centralizer ({a} : Set G) ∧
    IsElementaryAbelian 2 (zpowers a ⊔ ⁅U, zpowers a⁆ : Subgroup G) ∧
    Nat.card (zpowers a ⊔ ⁅U, zpowers a⁆ : Subgroup G) = 16 := by
  let B := d.left.map U.subtype
  let C := d.right.map U.subtype
  have hB : Nonempty (B ≃* QuaternionGroup 2) :=
    ⟨(d.left.equivMapOfInjective U.subtype U.subtype_injective).symm.trans d.left_model.some⟩
  have hj : B ⊔ C = U := by
    rw [← map_sup, d.span, ← MonoidHom.range_eq_map, U.range_subtype]
  have hi : Nat.card (B ⊓ C : Subgroup G) = 2 := by
    rw [← map_inf d.left d.right U.subtype U.subtype_injective,
      card_map_of_injective U.subtype_injective, d.intersection_card]
  have hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    exact congrArg U.subtype (d.commute b hb c hc)
  have h := quaternion_swap_elementary_sixteen B C hB hi hcomm a ha
    (by rwa [hj]) hswap
  rwa [hj] at h
end Subgroup

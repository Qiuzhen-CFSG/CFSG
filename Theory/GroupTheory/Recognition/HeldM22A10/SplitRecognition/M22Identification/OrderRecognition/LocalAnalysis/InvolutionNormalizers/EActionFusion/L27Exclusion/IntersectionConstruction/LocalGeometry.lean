module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.ElementarySixteen
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.SylowTransport

/-!
# The four-group intersection in Janko's Case II

The actual intersection V = E ∩ F has order four. Its whole ambient
centralizer has order sixty-four and lies in the coordinate Sylow group T.
An element normalizing E and V therefore sends F to an elementary sixteen
in T. The classification of those sixteens forces it to preserve F.

An order-three element normalizing V acts freely on its three nonidentity
elements: a fixed point would make its action on V trivial, placing the
element in the two-group T. Consequently its fixed subgroup on E is
disjoint from F. These statements require neither actor fusion nor an
identification of N(E)/E. Existence of the element and the order of its
fixed subgroup on E remain separate obligations.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemmas 1 and 6, pp.4 and 7.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
local instance : DecidablePred (· ∈ modelE) := fun x =>
  inferInstanceAs (Decidable (x.right = 1))
local instance : DecidablePred (· ∈ modelF) := fun x =>
  decidable_of_iff (x * d = d * x) mem_centralizer_singleton_iff.symm
local instance : DecidablePred (· ∈ modelT) := fun x =>
  decidable_of_iff (x.right * a.right = a.right * x.right) mem_centralizer_singleton_iff.symm

local instance : DecidablePred (· ∈ (modelE ⊓ modelF : Subgroup TwistedModel)) :=
  fun x => inferInstanceAs (Decidable (x ∈ modelE ∧ x ∈ modelF))

private theorem modelV_card : Nat.card (modelE ⊓ modelF : Subgroup TwistedModel) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem modelV_centralizer_le :
    centralizer ((modelE ⊓ modelF : Subgroup TwistedModel) : Set TwistedModel) ≤ modelT := by
  have h : ∀ x : TwistedModel, x * z 2 = z 2 * x → x ∈ modelT := by decide +kernel
  intro x hx
  exact h x (hx _ ⟨z_mem_modelE 2, modelF_generators.2.1⟩).symm

local instance : DecidablePred (· ∈ centralizer
    ((modelE ⊓ modelF : Subgroup TwistedModel) : Set TwistedModel)) := fun x =>
  decidable_of_iff (∀ y : (modelE ⊓ modelF : Subgroup TwistedModel), (y : TwistedModel) * x = x * y)
    ⟨fun h y hy => h ⟨y, hy⟩, fun h y => h y y.property⟩

private theorem modelV_centralizer_card : Nat.card (centralizer
    ((modelE ⊓ modelF : Subgroup TwistedModel) : Set TwistedModel)) = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

omit [Finite G] in
/-- The intersection of the two actual elementary sixteens is a four-group. -/
public theorem l27_intersection_card : Nat.card (E D k ⊓ F D k : Subgroup G) = 4 := by
  rw [← modelE_map D k, ← modelF_map D k, ← map_inf _ _ _ (into_injective D k),
    ← Nat.card_congr ((modelE ⊓ modelF).equivMapOfInjective (into D k)
      (into_injective D k)).toEquiv]
  exact modelV_card

/-- Its entire ambient centralizer lies in the coordinate Sylow two-subgroup. -/
public theorem l27_intersection_centralizer_le :
    centralizer ((E D k ⊓ F D k : Subgroup G) : Set G) ≤ caseIISylow D k := by
  rw [← modelE_map D k, ← modelF_map D k, ← map_inf _ _ _ (into_injective D k),
    centralizer_map D k (modelE ⊓ modelF) ⟨z_mem_modelE 0, modelF_generators.1⟩]
  exact map_mono modelV_centralizer_le

/-- The pointwise centralizer of the intersection has order sixty-four. -/
public theorem l27_intersection_centralizer_card :
    Nat.card (centralizer ((E D k ⊓ F D k : Subgroup G) : Set G)) = 64 := by
  rw [← modelE_map D k, ← modelF_map D k, ← map_inf _ _ _ (into_injective D k),
    centralizer_map D k (modelE ⊓ modelF) ⟨z_mem_modelE 0, modelF_generators.1⟩,
    card_map_of_injective (into_injective D k)]
  exact modelV_centralizer_card

private theorem elementary_sixteen_in_caseIISylow (A : Subgroup G)
    (hAT : A ≤ caseIISylow D k) (hA : IsElementaryAbelian 2 A)
    (hc : Nat.card A = 16) : A = E D k ∨ A = F D k := by
  let B := A.comap (into D k)
  have hBmap : B.map (into D k) = A := map_comap_eq_self
    (hAT.trans (map_le_range (into D k) modelT))
  have hBT : B ≤ modelT := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hAT hx
    rwa [← into_injective D k he]
  let := hA
  have hB : IsElementaryAbelian 2 B := by
    let : IsMulCommutative B := A.comap_injective_isMulCommutative (into_injective D k)
    refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
    intro x
    apply Subtype.ext
    apply into_injective D k
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (into D k x) x.property
  have hBc : Nat.card B = 16 := by
    rw [← card_map_of_injective (into_injective D k), hBmap, hc]
  rcases model_elementary_sixteen B hBT hB hBc with h | h
  · left
    rw [← hBmap, h, modelE_map]
  · right
    rw [← hBmap, h, modelF_map]

/-- Stabilizing E and its intersection with F also stabilizes F. -/
public theorem l27_normalizes_F_of_normalizes_intersection (q : G)
    (hE : q ∈ normalizer (E D k : Set G))
    (hV : q ∈ normalizer ((E D k ⊓ F D k : Subgroup G) : Set G)) :
    q ∈ normalizer (F D k : Set G) := by
  let e := MulAut.conj q
  let A := (F D k).map e.toMonoidHom
  have hEC : (E D k).map e.toMonoidHom = E D k :=
    mem_normalizer_iff_map_conj_eq.mp hE
  have hFC : F D k ≤ centralizer ((E D k ⊓ F D k : Subgroup G) : Set G) := by
    let := F_elementary D k
    exact (le_centralizer (F D k)).trans (centralizer_le inf_le_right)
  have hAT : A ≤ caseIISylow D k := by
    apply le_trans _ (l27_intersection_centralizer_le D k)
    rintro x ⟨y, hy, rfl⟩ v hv
    have hv' : e.symm v ∈ E D k ⊓ F D k := by
      simpa [e, MulAut.conj_apply] using
        (mem_normalizer_iff.mp ((normalizer _).inv_mem hV) v).mp hv
    have hcomm := congrArg e (hFC hy (e.symm v) hv')
    change v * e y = e y * v
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hcomm
  have hAc : Nat.card A = 16 := by
    rw [card_map_of_injective e.injective, F_card]
  have hAE : IsElementaryAbelian 2 A := by
    let := F_elementary D k
    exact IsElementaryAbelian.map _
  rcases elementary_sixteen_in_caseIISylow D k A hAT hAE hAc with h | h
  · have hFE : F D k = E D k := (map_injective e.injective) (h.trans hEC.symm)
    have hmodel : modelF = modelE := (map_injective (into_injective D k)) (by
      rw [modelF_map, modelE_map, hFE])
    have hd := modelF_generators.2.2.2
    rw [hmodel] at hd
    have hn : d ∉ modelE := by decide +kernel
    exact (hn hd).elim
  · exact mem_normalizer_iff_map_conj_eq.mpr h

private theorem cube_on_four_points : ∀ f : Fin 4 → Fin 4, ∀ i j,
    i ≠ j → f i = i → f j = j → (∀ x, f (f (f x)) = x) → ∀ x, f x = x := by
  decide +kernel

private theorem cube_on_four {X : Type*} [Finite X] (hc : Nat.card X = 4)
    (f : X → X) (hf : ∀ x, f (f (f x)) = x) (i j : X)
    (hij : i ≠ j) (hi : f i = i) (hj : f j = j) : ∀ x, f x = x := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let e := Fintype.equivFinOfCardEq (show Fintype.card X = 4 by simpa using hc)
  let f' : Fin 4 → Fin 4 := fun a => e (f (e.symm a))
  have h := cube_on_four_points f' (e i) (e j) (fun he => hij (e.injective he))
    (by simpa [f'] using congrArg e hi) (by simpa [f'] using congrArg e hj)
    (by intro x; simpa [f'] using congrArg e (hf (e.symm x)))
  intro x
  apply e.injective
  simpa [f'] using h (e x)

/-- An order-three element stabilizing the intersection has no nonidentity
fixed point there, so its fixed subgroup on E meets F trivially. -/
public theorem l27_intersection_fixed_disjoint (q : G)
    (hV : q ∈ normalizer ((E D k ⊓ F D k : Subgroup G) : Set G))
    (ho : orderOf q = 3) :
    Disjoint (E D k ⊓ centralizer ({q} : Set G)) (F D k) := by
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro x hx
  by_contra hn
  have hx1 : x ≠ 1 := hn
  let V := E D k ⊓ F D k
  let n : normalizer (V : Set G) := ⟨q, hV⟩
  let f := V.normalizerMonoidHom n
  have hn3 : n ^ 3 = 1 := by
    apply Subtype.ext
    exact ho ▸ pow_orderOf_eq_one q
  have hf3 : f ^ 3 = 1 := by rw [← map_pow, hn3, map_one]
  have hf : ∀ v : V, f (f (f v)) = v := fun v =>
    congrArg (fun a : MulAut V => a v) hf3
  let v : V := ⟨x, hx.1.1, hx.2⟩
  have hfv : f v = v := by
    apply Subtype.ext
    change q * x * q⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact (mem_centralizer_singleton_iff.mp hx.1.2).symm
  have hid := cube_on_four (l27_intersection_card D k) f hf 1 v
    (fun hv => hx1 (congrArg Subtype.val hv.symm)) (map_one f) hfv
  have hqC : q ∈ centralizer (V : Set G) := by
    intro y hy
    have he := congrArg Subtype.val (hid ⟨y, hy⟩)
    change q * y * q⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hqT := l27_intersection_centralizer_le D k hqC
  have hd := (caseIISylow D k).toSubgroup.orderOf_dvd_natCard hqT
  have hc : Nat.card (caseIISylow D k) = 128 := by
    rw [Sylow.card_eq_multiplicity, ← D.sylow.card_eq_multiplicity, D.sylow_card]
  rw [ho, hc] at hd
  norm_num at hd

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII

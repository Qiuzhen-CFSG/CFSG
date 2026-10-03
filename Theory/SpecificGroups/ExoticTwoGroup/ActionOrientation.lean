module

public import Theory.GroupAction.C4SquareActionDichotomySetup
import Mathlib.GroupTheory.IndexNormal
public import Theory.SpecificGroups.ExoticTwoGroup.ActionCoordinates
import all Theory.SpecificGroups.ExoticTwoGroup.ActionModel
import all Theory.SpecificGroups.ExoticTwoGroup.ActionCoordinates

/-!
# Orienting the order-sixteen action on a C₄-square

The two inner actions and inversion generate an eight-group fixing every
involution. In an order-sixteen overgroup moving an involution this core has
index two. Encode an element outside the core by its two basis images; its
square and conjugation on the core give a finite coordinate certificate.
After zero, one or two cyclic coordinate changes, its core coset contains
either interchange or a quarter-turn. The inner four survives these changes.

The finite calculation is checked by the kernel using `decide` on the
sixteen-element model. The private imports of `ActionModel` and
`ActionCoordinates` are intentional internal dependencies of this computational
certificate: they let the kernel reduce the coordinate maps without exposing
those implementations in the public API. The exported theorem uses only the
existing public actions.

Source: MacWilliams, Trans. AMS 150 (1970), §4 (xiv), printed p.393,
and the outer-action cases on p.399; Janko–Thompson 1.4(c), p.386.
-/

namespace ExoticTwoGroup.ActionModel
open C4SquareExtension Subgroup C4SquareExtension.ActionDichotomy
abbrev orientationCoreBits := Fin 2 × Fin 2 × Fin 2
def orientationCoreWord (q : orientationCoreBits) : MulAut Model :=
  inner₁ ^ q.1.val * inner₂ ^ q.2.1.val * inversion ^ q.2.2.val
theorem orientationCoreWord_injective : Function.Injective orientationCoreWord := by
  intro q r h
  have hh : Function.Injective (fun q : orientationCoreBits => (orientationCoreWord q u, orientationCoreWord q v)) := by decide
  apply hh
  exact congrArg (fun f : MulAut Model => (f u, f v)) h
theorem orientationCoreWord_mem (core : Subgroup (MulAut Model)) (h₁ : inner₁ ∈ core)
    (h₂ : inner₂ ∈ core) (hz : inversion ∈ core) (q : orientationCoreBits) : orientationCoreWord q ∈ core := by
  exact core.mul_mem (core.mul_mem (core.pow_mem h₁ _) (core.pow_mem h₂ _)) (core.pow_mem hz _)
theorem orientationEight_le_core_card (core : Subgroup (MulAut Model))
    (h₁ : inner₁ ∈ core) (h₂ : inner₂ ∈ core) (hz : inversion ∈ core) :
    8 ≤ Nat.card core := by
  let f : orientationCoreBits → core := fun q => ⟨orientationCoreWord q, orientationCoreWord_mem core h₁ h₂ hz q⟩
  have hi : Function.Injective f := fun q r h => orientationCoreWord_injective (congrArg Subtype.val h)
  have hh := Nat.card_le_card_of_injective f hi
  simpa only [Nat.card_prod, Nat.card_fin] using hh
end ExoticTwoGroup.ActionModel
namespace ExoticTwoGroup.ActionModel
open C4SquareExtension Subgroup
theorem orientationInner_fix (f : MulAut Model) :
    (f = inner₁ ∨ f = inner₂ ∨ f = inversion) → ∀ x : Model, x ^ 2 = 1 → f x = x := by
  intro hf
  rcases hf with rfl | rfl | rfl <;> decide
theorem orientationCore_fix (core : Subgroup (MulAut Model))
    (hcore : core = closure ({inner₁, inner₂, inversion} : Set (MulAut Model))) :
    ∀ f ∈ core, ∀ x : Model, x ^ 2 = 1 → f x = x := by
  intro f hf
  rw [hcore] at hf
  induction hf using Subgroup.closure_induction with
  | mem f hf =>
      rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hf) with rfl | rfl | rfl
      · exact orientationInner_fix inner₁ (Or.inl rfl)
      · exact orientationInner_fix inner₂ (Or.inr (Or.inl rfl))
      · exact orientationInner_fix inversion (Or.inr (Or.inr rfl))
  | one => intro x hx; rfl
  | mul f g hf hg hf' hg' =>
      intro x hx
      simp only [MulAut.mul_apply, hg' x hx, hf' x hx]
  | inv f hf hf' =>
      intro x hx
      apply (f.injective)
      calc
        f (f⁻¹ x) = x := by exact f.apply_symm_apply x
        _ = f x := (hf' x hx).symm
end ExoticTwoGroup.ActionModel
namespace ExoticTwoGroup.ActionModel
open C4SquareExtension Subgroup
def orientationCycleAt (k : Fin 3) : MulAut Model :=
  if k = 0 then 1 else if k = 1 then coordinateCycle else coordinateCycle ^ 2
def orientationConjVal (k : Fin 3) (i : orientationCoreBits) (p : Model × Model) (x : Model) : Model :=
  orientationCycleAt k (orientationCoreWord i (C4SquareExtension.ActionDichotomy.outerAct p ((orientationCycleAt k).symm x)))
def orientationOuterValid (p : Model × Model) : Prop :=
  p.1 ^ 2 ≠ 1 ∧ p.2 ^ 2 ≠ 1 ∧ p.1 ^ 2 ≠ p.2 ^ 2 ∧
  (∃ x : Model, x ^ 2 = 1 ∧ C4SquareExtension.ActionDichotomy.outerAct p x ≠ x) ∧
  (∃ z : orientationCoreBits, ∀ x : Model,
      C4SquareExtension.ActionDichotomy.outerAct p
        (C4SquareExtension.ActionDichotomy.outerAct p x) = orientationCoreWord z x) ∧
  (∀ z : orientationCoreBits, ∃ w : orientationCoreBits, ∀ x : Model,
      C4SquareExtension.ActionDichotomy.outerAct p (orientationCoreWord z x) =
        orientationCoreWord w (C4SquareExtension.ActionDichotomy.outerAct p x))
instance (p : Model × Model) : Decidable (orientationOuterValid p) := by unfold orientationOuterValid; infer_instance
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem orientationFiniteClassify : ∀ (i j k l : ZMod 4),
    orientationOuterValid ((Multiplicative.ofAdd i, Multiplicative.ofAdd j),
      (Multiplicative.ofAdd k, Multiplicative.ofAdd l)) →
    ∃ c : Fin 3, ((∃ z : orientationCoreBits, ∀ x : Model,
      orientationConjVal c z ((Multiplicative.ofAdd i, Multiplicative.ofAdd j),
        (Multiplicative.ofAdd k, Multiplicative.ofAdd l)) x = swap x) ∨
      (∃ z : orientationCoreBits, orientationConjVal c z ((Multiplicative.ofAdd i, Multiplicative.ofAdd j),
        (Multiplicative.ofAdd k, Multiplicative.ofAdd l)) u = v ∧
        orientationConjVal c z ((Multiplicative.ofAdd i, Multiplicative.ofAdd j),
          (Multiplicative.ofAdd k, Multiplicative.ofAdd l)) v = u⁻¹)) := by
  intro i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide

theorem orientationInner_mem_cycle_sq (H : Subgroup (MulAut Model))
    (h₁ : inner₁ ∈ H) (h₂ : inner₂ ∈ H) :
    inner₁ ∈ H.map (MulAut.congr (coordinateCycle ^ 2)).toMonoidHom ∧
      inner₂ ∈ H.map (MulAut.congr (coordinateCycle ^ 2)).toMonoidHom := by
  have hfirst := inner_mem_coordinateCycle H h₁ h₂
  have hsecond := inner_mem_coordinateCycle
    (H.map (MulAut.congr coordinateCycle).toMonoidHom) hfirst.1 hfirst.2
  have he : (MulAut.congr (coordinateCycle ^ 2)).toMonoidHom =
      (MulAut.congr coordinateCycle).toMonoidHom.comp
        (MulAut.congr coordinateCycle).toMonoidHom := by
    apply MonoidHom.ext
    intro f
    apply MulEquiv.ext
    intro x
    change (coordinateCycle ^ 2) (f ((coordinateCycle ^ 2)⁻¹ x)) =
      coordinateCycle (coordinateCycle (f (coordinateCycle⁻¹ (coordinateCycle⁻¹ x))))
    simp only [pow_two, mul_inv_rev, MulAut.mul_apply]
  simpa only [Subgroup.map_map, he] using hsecond

/-- An order-sixteen action moving an involution admits coordinates with
both prescribed inner actions and either interchange or a quarter-turn. -/
public theorem exists_oriented_action (H A : Subgroup (MulAut Model))
    (hHA : H ≤ A) (_hH : Nat.card H = 4) (hA : Nat.card A = 16)
    (h₁ : inner₁ ∈ H) (h₂ : inner₂ ∈ H)
    (hmove : ∃ f ∈ A, ∃ x : Model, x ^ 2 = 1 ∧ f x ≠ x) :
    ∃ c : MulAut Model, let F := (MulAut.congr c).toMonoidHom
      inner₁ ∈ H.map F ∧ inner₂ ∈ H.map F ∧
      (swap ∈ A.map F ∨ ∃ q ∈ A.map F, q u = v ∧ q v = u⁻¹) := by
  classical
  let K : Subgroup (MulAut Model) := closure ({inner₁, inner₂, inversion} : Set (MulAut Model))
  have hK1 : inner₁ ∈ K := subset_closure (by simp)
  have hK2 : inner₂ ∈ K := subset_closure (by simp)
  have hKz : inversion ∈ K := subset_closure (by simp)
  have hKleA : K ≤ A := by
    apply (closure_le _).mpr
    intro f hf
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hf) with rfl | rfl | rfl
    · exact hHA h₁
    · exact hHA h₂
    · exact inversion_mem_of_card_sixteen A hA
  have hKlower : 8 ≤ Nat.card K := orientationEight_le_core_card K hK1 hK2 hKz
  obtain ⟨f, hfA, x, hx2, hfx⟩ := hmove
  have hfnot : f ∉ K := by
    intro hfK
    exact hfx (orientationCore_fix K rfl f hfK x hx2)
  have hKle : Nat.card K ≤ 16 := by
    rw [← hA]
    exact Subgroup.card_le_of_le hKleA
  have hKlt : Nat.card K < 16 := by
    by_contra hn
    have heq : Nat.card K = 16 := by omega
    have hKA : K = A := Subgroup.eq_of_le_of_card_ge hKleA (by rw [heq, hA])
    exact hfnot (hKA ▸ hfA)
  have hKdvd : Nat.card K ∣ 16 := by
    rw [← hA]
    exact Subgroup.card_dvd_of_le hKleA
  have hKcard : Nat.card K = 8 := by
    obtain ⟨n, hn⟩ := hKdvd
    have hnpos : 0 < n := by
      by_contra hn0
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst n
      norm_num at hn
    have hnd : n ∣ 16 := by
      refine ⟨Nat.card K, ?_⟩
      simpa [Nat.mul_comm] using hn
    have hnle : n ≤ 16 := Nat.le_of_dvd (by norm_num) hnd
    interval_cases n <;> omega
  let L : Subgroup A := K.subgroupOf A
  have hLcard : Nat.card L = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hKleA).toEquiv]
    exact hKcard
  have hindex : L.index = 2 := by
    have hh := L.card_mul_index
    rw [hLcard, hA] at hh
    omega
  have hf2 : f * f ∈ K := by
    have hh := L.mul_self_mem_of_index_two hindex (⟨f, hfA⟩ : A)
    exact hh
  have hnormal : L.Normal := L.normal_of_index_eq_two hindex
  have hconj (z : orientationCoreBits) : f * orientationCoreWord z * f⁻¹ ∈ K := by
    have hzK := orientationCoreWord_mem K hK1 hK2 hKz z
    let kz : A := ⟨orientationCoreWord z, hKleA hzK⟩
    have hh := hnormal.conj_mem kz (show kz ∈ L by exact hzK) (⟨f, hfA⟩ : A)
    exact hh
  have hexhaust (g : MulAut Model) (hg : g ∈ K) : ∃ z : orientationCoreBits,
      orientationCoreWord z = g := by
    let ff : orientationCoreBits → K := fun z =>
      ⟨orientationCoreWord z, orientationCoreWord_mem K hK1 hK2 hKz z⟩
    have hi : Function.Injective ff := fun z w hz =>
      orientationCoreWord_injective (congrArg Subtype.val hz)
    have hs := ((Nat.bijective_iff_injective_and_card ff).mpr
      ⟨hi, by simpa only [Nat.card_prod, Nat.card_fin] using hKcard.symm⟩).2
    obtain ⟨z, hz⟩ := hs ⟨g, hg⟩
    exact ⟨z, congrArg Subtype.val hz⟩
  have hfouter (y : Model) : f y = C4SquareExtension.ActionDichotomy.outerAct (f u, f v) y := by
    simpa only [u_eq, v_eq, C4SquareExtension.ActionDichotomy.e₁, C4SquareExtension.ActionDichotomy.e₂] using (C4SquareExtension.ActionDichotomy.aut_eq_outerAct f y)
  have hgood : (f u)^2 ≠ 1 ∧ (f v)^2 ≠ 1 ∧ (f u)^2 ≠ (f v)^2 := by
    constructor
    · intro hh; apply (show u^2 ≠ 1 by decide); apply f.injective
      simpa only [map_pow, map_one] using hh
    constructor
    · intro hh; apply (show v^2 ≠ 1 by decide); apply f.injective
      simpa only [map_pow, map_one] using hh
    · intro hh; apply (show u^2 ≠ v^2 by decide); apply f.injective
      simpa only [map_pow] using hh
  have hmove' : ∃ y : Model, y^2 = 1 ∧ C4SquareExtension.ActionDichotomy.outerAct (f u, f v) y ≠ y := by
    refine ⟨x, hx2, ?_⟩
    rw [← hfouter]
    exact hfx
  have hsquare : ∃ z : orientationCoreBits, ∀ y : Model,
      C4SquareExtension.ActionDichotomy.outerAct (f u, f v) (C4SquareExtension.ActionDichotomy.outerAct (f u, f v) y) = orientationCoreWord z y := by
    obtain ⟨z, hz⟩ := hexhaust (f*f) hf2
    refine ⟨z, ?_⟩
    intro y
    rw [← hfouter, ← hfouter]
    exact (congrArg (fun g : MulAut Model => g y) hz).symm
  have hnormal' : ∀ z : orientationCoreBits, ∃ w : orientationCoreBits, ∀ y : Model,
      C4SquareExtension.ActionDichotomy.outerAct (f u, f v) (orientationCoreWord z y) =
        orientationCoreWord w (C4SquareExtension.ActionDichotomy.outerAct (f u, f v) y) := by
    intro z
    obtain ⟨w, hw⟩ := hexhaust (f * orientationCoreWord z * f⁻¹) (hconj z)
    refine ⟨w, ?_⟩
    intro y
    have hh := congrArg (fun g : MulAut Model => g (f y)) hw
    calc
      C4SquareExtension.ActionDichotomy.outerAct (f u, f v) (orientationCoreWord z y) = f (orientationCoreWord z y) :=
        (hfouter _).symm
      _ = orientationCoreWord w (f y) := by
        have hleft : f⁻¹ (f y) = y := f.left_inv y
        simpa only [MulAut.mul_apply, hleft] using hh.symm
      _ = orientationCoreWord w (C4SquareExtension.ActionDichotomy.outerAct (f u, f v) y) := by rw [hfouter]
  let a : ZMod 4 := (f u).1.toAdd
  let b : ZMod 4 := (f u).2.toAdd
  let d : ZMod 4 := (f v).1.toAdd
  let e : ZMod 4 := (f v).2.toAdd
  have hp : (f u, f v) = ((Multiplicative.ofAdd a, Multiplicative.ofAdd b),
      (Multiplicative.ofAdd d, Multiplicative.ofAdd e)) := by ext <;> simp [a,b,d,e]
  have hfin := orientationFiniteClassify a b d e
    (by simpa [hp] using ⟨hgood.1, hgood.2.1, hgood.2.2, hmove', hsquare, hnormal'⟩)
  obtain ⟨k, hk | hk⟩ := hfin
  · refine ⟨orientationCycleAt k, ?_⟩
    let c := orientationCycleAt k
    have hinner : inner₁ ∈ H.map (MulAut.congr c).toMonoidHom ∧
        inner₂ ∈ H.map (MulAut.congr c).toMonoidHom := by
      fin_cases k
      · constructor
        · exact ⟨inner₁, h₁, by apply MulEquiv.ext; intro x; rfl⟩
        · exact ⟨inner₂, h₂, by apply MulEquiv.ext; intro x; rfl⟩
      · simpa [c, orientationCycleAt] using inner_mem_coordinateCycle H h₁ h₂
      · simpa [c, orientationCycleAt] using orientationInner_mem_cycle_sq H h₁ h₂
    refine ⟨hinner.1, hinner.2, ?_⟩
    obtain ⟨z, hz⟩ := hk
    have hqA : orientationCoreWord z * f ∈ A :=
      A.mul_mem (hKleA (orientationCoreWord_mem K hK1 hK2 hKz z)) hfA
    have hev (y : Model) :
        (MulAut.congr c (orientationCoreWord z * f)) y =
          orientationConjVal k z (f u, f v) y := by
      change c ((orientationCoreWord z * f) (c.symm y)) = _
      simp only [MulAut.mul_apply]
      rw [hfouter]
      rfl
    have hz' : ∀ y : Model, orientationConjVal k z (f u, f v) y = swap y := by
      intro y
      rw [hp]
      exact hz y
    have heq : MulAut.congr c (orientationCoreWord z * f) = swap := by
      apply MulEquiv.ext
      intro y
      rw [hev, hz']
    apply Or.inl
    rw [← heq]
    exact mem_map_of_mem _ hqA
  · refine ⟨orientationCycleAt k, ?_⟩
    let c := orientationCycleAt k
    have hinner : inner₁ ∈ H.map (MulAut.congr c).toMonoidHom ∧
        inner₂ ∈ H.map (MulAut.congr c).toMonoidHom := by
      fin_cases k
      · constructor
        · exact ⟨inner₁, h₁, by apply MulEquiv.ext; intro x; rfl⟩
        · exact ⟨inner₂, h₂, by apply MulEquiv.ext; intro x; rfl⟩
      · simpa [c, orientationCycleAt] using inner_mem_coordinateCycle H h₁ h₂
      · simpa [c, orientationCycleAt] using orientationInner_mem_cycle_sq H h₁ h₂
    refine ⟨hinner.1, hinner.2, ?_⟩
    obtain ⟨z, hzu, hzv⟩ := hk
    have hqA : orientationCoreWord z * f ∈ A :=
      A.mul_mem (hKleA (orientationCoreWord_mem K hK1 hK2 hKz z)) hfA
    let q := MulAut.congr c (orientationCoreWord z * f)
    have hqmap : q ∈ A.map (MulAut.congr c).toMonoidHom := mem_map_of_mem _ hqA
    have hev (y : Model) : q y = orientationConjVal k z (f u, f v) y := by
      change c ((orientationCoreWord z * f) (c.symm y)) = _
      simp only [MulAut.mul_apply]
      rw [hfouter]
      rfl
    apply Or.inr
    refine ⟨q, hqmap, ?_, ?_⟩
    · rw [hev]
      rw [hp]
      exact hzu
    · rw [hev]
      rw [hp]
      exact hzv
end ExoticTwoGroup.ActionModel

module
public import ABG.Recognition.ThreeCentralizerCharacters
public import Theory.SpecificGroups.GL2.ThreeLargeSubgroupCenter
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The index-39 obstruction in Wong's linear branch

In a group of order 5616, an overgroup K of an involution centralizer
isomorphic to GL₂(3) cannot have index 39. Such an index would give K order
144 and the centralizer index three in K. Its core has index three or six
by the permutation action on three cosets, hence order 48 or 24. In either
case its center has exactly one nonidentity element, the given involution.
Normality of that center makes K centralize the involution, a contradiction.

This obstruction uses the actual involution centralizer and an arbitrary
overgroup; it requires no simplicity or local recognition data.

Source: Wong (1964), Theorem 6(b), printed p.110.
-/

open Matrix.GeneralLinearGroup
namespace ABG

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_card_three
    (t : G) (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) = 48 := by
  calc
    _ = Nat.card (GL2 3 1) := Nat.card_congr e.toEquiv
    _ = Nat.card (GL (Fin 2) (ZMod 3)) := Nat.card_congr glTwoThreeFieldEquiv.toEquiv
    _ = 48 := by rw [Matrix.card_GL_field]; decide

private theorem core_card_of_index_thirtynine
    (t : G) (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (K : Subgroup G) (hCK : Subgroup.centralizer ({t} : Set G) ≤ K)
    (hG : Nat.card G = 5616) (hK : K.index = 39) :
    let H := (Subgroup.centralizer ({t} : Set G)).subgroupOf K
    Nat.card H.normalCore = 24 ∨ Nat.card H.normalCore = 48 := by
  let C := Subgroup.centralizer ({t} : Set G)
  let H := C.subgroupOf K
  let N := H.normalCore
  have hCcard : Nat.card C = 48 := centralizer_card_three t e
  have hKcard : Nat.card K = 144 := by
    have h := K.card_mul_index
    rw [hK, hG] at h
    omega
  have hHcard : Nat.card H = 48 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv).trans hCcard
  have hHindex : H.index = 3 := by
    have h := H.card_mul_index
    rw [hHcard, hKcard] at h
    omega
  have hNindexDvd : N.index ∣ 6 := by
    have hd : N.index ∣ H.index.factorial := by
      change H.normalCore.index ∣ H.index.factorial
      rw [Subgroup.normalCore_eq_ker, Subgroup.index_ker,
        H.index_eq_card, ← Nat.card_perm]
      exact Subgroup.card_subgroup_dvd_card _
    simpa [hHindex, Nat.factorial] using hd
  have hHindexDvd : 3 ∣ N.index := by
    rw [← hHindex]
    exact Subgroup.index_dvd_of_le H.normalCore_le
  have hNindex : N.index = 3 ∨ N.index = 6 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hNindexDvd
    interval_cases hi : N.index <;> norm_num at *
  have h := N.card_mul_index
  rw [hKcard] at h
  change Nat.card N = 24 ∨ Nat.card N = 48
  rcases hNindex with hi | hi
  · right; rw [hi] at h; omega
  · left; rw [hi] at h; omega

omit [Finite G] in
private theorem overgroup_le_centralizer_of_large_core
    (t : G) (ht : orderOf t = 2)
    (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (K : Subgroup G) (hCK : Subgroup.centralizer ({t} : Set G) ≤ K)
    (hNcard : Nat.card ((Subgroup.centralizer ({t} : Set G)).subgroupOf K).normalCore = 24 ∨
      Nat.card ((Subgroup.centralizer ({t} : Set G)).subgroupOf K).normalCore = 48) :
    K ≤ Subgroup.centralizer ({t} : Set G) := by
  let C := Subgroup.centralizer ({t} : Set G)
  let H := C.subgroupOf K
  let N := H.normalCore
  let z : K := ⟨t, hCK (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩
  let q : H ≃* GL (Fin 2) (ZMod 3) :=
    (Subgroup.subgroupOfEquivOfLe hCK).trans (threeCentralizerEquiv t e)
  let f : N →* GL (Fin 2) (ZMod 3) :=
    q.toMonoidHom.comp (Subgroup.inclusion H.normalCore_le)
  let D := f.range
  have hf_inj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun a : H => (a : K)) (q.injective h)
  have hDcard : Nat.card D = 24 ∨ Nat.card D = 48 := by
    have he : Nat.card D = Nat.card N :=
      (Nat.card_congr (Equiv.ofInjective f hf_inj)).symm
    simpa only [he] using hNcard
  have hD := three_large_subgroup_center D hDcard
  let zH : H := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hzH : q zH = threeCentral := threeCentralizerEquiv_involution t ht e
  obtain ⟨n, hn⟩ := hD.1
  have hnz : (n : K) = z := by
    have he := q.injective (hn.trans hzH.symm)
    exact congrArg Subtype.val he
  have hzN : z ∈ N := hnz ▸ n.property
  let Z := (Subgroup.center N).map N.subtype
  have hzZ : z ∈ Z := by
    refine ⟨⟨z, hzN⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (H.normalCore_le x.property)
  have hZcases : ∀ x : K, x ∈ Z → x = 1 ∨ x = z := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    have haf : (⟨f a, ⟨a, rfl⟩⟩ : D) ∈ Subgroup.center D := by
      apply Subgroup.mem_center_iff.mpr
      intro b
      obtain ⟨b, hb⟩ := b.property
      apply Subtype.ext
      dsimp
      rw [← hb, ← map_mul, ← map_mul]
      exact congrArg f (Subgroup.mem_center_iff.mp ha b)
    rcases (hD.2 _).mp haf with he | he
    · left
      have he' : a = 1 := hf_inj (he.trans f.map_one.symm)
      simp only [he', map_one]
    · right
      exact congrArg Subtype.val (q.injective (he.trans hzH.symm))
  let _ : N.Normal := H.normalCore_normal
  let _ : Z.Normal := inferInstance
  intro k hk
  let k' : K := ⟨k, hk⟩
  have hzconj := (inferInstance : Z.Normal).conj_mem z hzZ k'
  rcases hZcases _ hzconj with he | he
  · have hz1 : z = 1 := by
      have h := congrArg (fun x : K => k'⁻¹ * x * k') he
      simpa [mul_assoc] using h
    have ht1 : t = 1 := congrArg Subtype.val hz1
    rw [ht1, orderOf_one] at ht
    norm_num at ht
  · apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := congrArg (fun x : K => (x : G) * k) he
    simpa [k', z, mul_assoc] using h

/-- No overgroup of a GL₂(3) involution centralizer has index 39 in a group
of order 5616. -/
public theorem index_ne_thirtynine_of_glTwoThree_centralizer
    (hG : Nat.card G = 5616) (t : G) (ht : orderOf t = 2)
    (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (K : Subgroup G) (hCK : Subgroup.centralizer ({t} : Set G) ≤ K) :
    K.index ≠ 39 := by
  intro hK
  have hN := core_card_of_index_thirtynine t e K hCK hG hK
  have hKC := overgroup_le_centralizer_of_large_core t ht e K hCK hN
  have heq : K = Subgroup.centralizer ({t} : Set G) := le_antisymm hKC hCK
  have h := K.card_mul_index
  rw [heq, centralizer_card_three t e] at h
  rw [← heq, hK, hG] at h
  norm_num at h

end ABG

module

public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.Coordinates
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Quaternion involution actions in index-two subgroups of Aut(A₆)

Every subgroup of order 720 in the actual automorphism group contains
Inn(A₆): its quotient has order two and A₆ is simple. In the cyclic-eight
holomorph, every quaternion eight-subgroup is the same explicit subgroup.
An involution centralizing it modulo its center either belongs to it or,
together with the inner dihedral subgroup, generates the whole holomorph.
The latter would place a Sylow subgroup of order 32 in a group of order 720.

The final theorem retains an actual quaternion embedding into an arbitrary
Sylow subgroup. It applies to the marked commutator calculation in
Aschbacher, “A 2-local characterization of M12”, Illinois J. Math. 47
(2003), Lemma 4.10, p.42. The concrete Sylow identification is the existing
`ShadowLocal.Identification`; all small tables are checked by the kernel.
-/

public section

open Subgroup
open scoped commutatorElement
namespace AlternatingSix.ShadowLocal.QuaternionInvolutionAction
open Holomorph
private abbrev qe := M10.LocalGeometry.Coordinates.quaternionEmbedding

set_option maxRecDepth 10000 in
private theorem pair_table (x y : Model) (hx : x ^ 2 ≠ 1)
    (hs : x ^ 2 = y ^ 2) (hi : y * x = x⁻¹ * y) (hn : x * y ≠ y * x) :
    (∃ d, qe d = x) ∧ (∃ d, qe d = y) := by
  revert x y
  decide +kernel

set_option maxRecDepth 10000 in
private theorem involution_table (r : Model) (hr : r ^ 2 = 1)
    (hi : ⁅r, qe (.a 1)⁆ = 1 ∨ ⁅r, qe (.a 1)⁆ = qe (.a 2))
    (hj : ⁅r, qe (.xa 0)⁆ = 1 ∨ ⁅r, qe (.xa 0)⁆ = qe (.a 2)) :
    r = 1 ∨ r = qe (.a 2) ∨
      (∃ (q : QuaternionGroup 2) (d : DihedralGroup 4),
        rotation = qe q * innerEmbedding d * r) ∧
      (∃ (q : QuaternionGroup 2) (d : DihedralGroup 4),
        transposition = qe q * innerEmbedding d * r) := by
  revert r
  decide +kernel

private theorem inner_le (L : Subgroup AutA6) (hL : Nat.card L = 720) : inner ≤ L := by
  have hindex : L.index = 2 := by
    have hc := L.card_mul_index
    rw [hL, card_aut] at hc
    omega
  let : L.Normal := normal_of_index_eq_two hindex
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  let f : A6 →* AutA6 ⧸ L := (QuotientGroup.mk' L).comp MulAut.conj
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hf | hf
  · have hi : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hf
    have hc := Nat.card_le_card_of_injective f hi
    have hq : Nat.card (AutA6 ⧸ L) = 2 := hindex
    rw [card_A6, hq] at hc
    omega
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ f.ker := hf ▸ mem_top x
    exact (QuotientGroup.eq_one_iff _).mp hx

private theorem range_eq (f : QuaternionGroup 2 →* Model) (hf : Function.Injective f) :
    f.range = qe.range := by
  let i : QuaternionGroup 2 := .a 1
  let j : QuaternionGroup 2 := .xa 0
  have hi : f i ^ 2 ≠ 1 := by
    intro he
    have : i ^ 2 = 1 := hf (by simpa only [map_pow, map_one] using he)
    exact (by decide : i ^ 2 ≠ 1) this
  have hs : f i ^ 2 = f j ^ 2 := by
    rw [← map_pow, ← map_pow]
    congr 1
  have hj : f j * f i = (f i)⁻¹ * f j := by
    simpa only [map_mul, map_inv] using congrArg f
      (show j * i = i⁻¹ * j by decide)
  have hn : f i * f j ≠ f j * f i := by
    intro he
    exact (by decide : i * j ≠ j * i) (hf (by simpa only [map_mul] using he))
  obtain ⟨hiQ, hjQ⟩ := pair_table (f i) (f j) hi hs hj hn
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, rfl⟩
    have words : ∀ x : QuaternionGroup 2, ∃ k : Fin 4,
        x = i ^ k.val ∨ x = j * i ^ k.val := by decide
    obtain ⟨k, hk | hk⟩ := words x
    · rw [hk, map_pow]
      exact qe.range.pow_mem hiQ _
    · rw [hk, map_mul, map_pow]
      exact qe.range.mul_mem hjQ (qe.range.pow_mem hiQ _)
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective
        M10.LocalGeometry.Coordinates.quaternionEmbedding_injective).toEquiv]

private theorem center_image (f : QuaternionGroup 2 →* Model) (hf : Function.Injective f) :
    f (.a 2) = qe (.a 2) := by
  have hm : f (.a 2) ∈ qe.range := range_eq f hf ▸ ⟨.a 2, rfl⟩
  obtain ⟨d, hd⟩ := hm
  have hne : qe d ≠ 1 := by
    rw [hd]
    intro he
    exact (by decide : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1)
      (hf (he.trans f.map_one.symm))
  have hs : (qe d) ^ 2 = 1 := by
    rw [hd, ← map_pow]
    exact f.map_one
  have ht : ∀ d : QuaternionGroup 2, qe d ≠ 1 → (qe d) ^ 2 = 1 → qe d = qe (.a 2) :=
    by decide
  exact hd.symm.trans (ht d hne hs)

private theorem model_action (U : Subgroup Model) (hU : U ≠ ⊤)
    (hD : innerD ≤ U) (f : QuaternionGroup 2 →* Model) (hf : Function.Injective f)
    (hfU : f.range ≤ U) (r : Model) (hrU : r ∈ U) (hr : r ^ 2 = 1)
    (hc : ∀ q, ⁅r, f q⁆ = 1 ∨ ⁅r, f q⁆ = f (.a 2)) : r ∈ f.range := by
  have hQ := range_eq f hf
  have hZ := center_image f hf
  have hc' (q : QuaternionGroup 2) :
      ⁅r, qe q⁆ = 1 ∨ ⁅r, qe q⁆ = qe (.a 2) := by
    have hm : qe q ∈ f.range := hQ.symm ▸ ⟨q, rfl⟩
    obtain ⟨d, hd⟩ := hm
    simpa only [hd, hZ] using hc d
  rcases involution_table r hr (hc' (.a 1)) (hc' (.xa 0)) with h | h | ⟨hi, hj⟩
  · exact h ▸ f.range.one_mem
  · rw [h, hQ]
    exact ⟨_, rfl⟩
  · exfalso
    apply hU
    have hQU : qe.range ≤ U := hQ ▸ hfU
    have hiU : rotation ∈ U := by
      obtain ⟨q, d, hd⟩ := hi
      rw [hd]
      exact U.mul_mem (U.mul_mem (hQU (⟨_, rfl⟩))
        (hD ((mem_innerD _).mpr ⟨d, rfl⟩))) hrU
    have hjU : transposition ∈ U := by
      obtain ⟨q, d, hd⟩ := hj
      rw [hd]
      exact U.mul_mem (U.mul_mem (hQU (⟨_, rfl⟩))
        (hD ((mem_innerD _).mpr ⟨d, rfl⟩))) hrU
    apply top_unique
    rw [← Holomorph.generated]
    apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hiU
    · exact hjU
    · exact hD (subset_closure (by simp))


/-- An involution in an index-two subgroup of Aut(A₆) which centralizes a
quaternion subgroup modulo its center belongs to that quaternion subgroup.
All elements and the quaternion embedding lie in the indicated actual Sylow. -/
theorem involution_mem_quaternion (L : Subgroup AutA6) (hL : Nat.card L = 720)
    (T : Sylow 2 AutA6) (f : QuaternionGroup 2 →* T) (hf : Function.Injective f)
    (hfL : ∀ q, (f q : AutA6) ∈ L) (r : T) (hrL : (r : AutA6) ∈ L)
    (hr : r ^ 2 = 1) (hc : ∀ q, ⁅r, f q⁆ = 1 ∨ ⁅r, f q⁆ = f (.a 2)) :
    r ∈ f.range := by
  let e := Identification.sylowEquiv T
  let j : Model →* AutA6 := (T : Subgroup AutA6).subtype.comp e.toMonoidHom
  let U := L.comap j
  have hU : U ≠ ⊤ := by
    intro he
    have hTL : (T : Subgroup AutA6) ≤ L := by
      intro t ht
      obtain ⟨x, hx⟩ := e.surjective ⟨t, ht⟩
      have hxm : x ∈ U := he ▸ mem_top x
      change (e x : AutA6) ∈ L at hxm
      simpa only [hx] using hxm
    have hd := Subgroup.card_dvd_of_le hTL
    rw [sylow_card T, hL] at hd
    norm_num at hd
  have hD : Holomorph.innerD ≤ U := by
    intro x hx
    have hmem : e x ∈ sylowInner T := by
      rw [← Identification.sylowEquiv_innerD T]
      exact mem_map_of_mem e.toMonoidHom hx
    exact inner_le L hL hmem
  let f' : QuaternionGroup 2 →* Model := e.symm.toMonoidHom.comp f
  have hf' : Function.Injective f' := e.symm.injective.comp hf
  have hfU : f'.range ≤ U := by
    rintro _ ⟨q, rfl⟩
    change (e (e.symm (f q)) : AutA6) ∈ L
    simpa only [e.apply_symm_apply] using hfL q
  have hrU : e.symm r ∈ U := by
    change (e (e.symm r) : AutA6) ∈ L
    simpa only [e.apply_symm_apply] using hrL
  have hr' : (e.symm r) ^ 2 = 1 := by simpa only [map_pow, map_one] using congrArg e.symm hr
  have hc' (q : QuaternionGroup 2) : ⁅e.symm r, f' q⁆ = 1 ∨ ⁅e.symm r, f' q⁆ = f' (.a 2) := by
    change ⁅e.symm r, e.symm (f q)⁆ = 1 ∨
      ⁅e.symm r, e.symm (f q)⁆ = e.symm (f (.a 2))
    rcases hc q with h | h
    · exact Or.inl (by simpa only [map_commutatorElement, map_one] using congrArg e.symm h)
    · exact Or.inr (by simpa only [map_commutatorElement] using congrArg e.symm h)
  obtain ⟨q, hq⟩ := model_action U hU hD f' hf' hfU (e.symm r) hrU hr' hc'
  exact ⟨q, e.symm.injective hq⟩

end AlternatingSix.ShadowLocal.QuaternionInvolutionAction

end

module

public import Theory.GroupTheory.CrossedHomTransfer
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Sylow

/-!
# Gaschütz's splitting theorem

An abelian normal subgroup `V` of a finite group `G` has a complement if
it has one in an overgroup `H` whose index is coprime to `|V|`. The local
complement gives a crossed retraction onto `V`. Coset transfer extends it
to a crossed homomorphism on `G` whose restriction to `V` is the power map
`v ↦ v ^ H.index`. That power map is bijective, so the kernel is an actual
subgroup complement to `V`.

For a normal p-subgroup, normality places `V` in every Sylow p-subgroup.
The index of a Sylow subgroup is coprime to `|V|`, giving the full splitting
criterion without a centrality or solvability hypothesis.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.1.39, printed p.31, citing Aschbacher (1986), 10.4 and 12.8.
-/

open scoped IsMulCommutative Pointwise

namespace Subgroup
variable {G : Type*} [Group G] (V K : Subgroup G) [V.Normal] [IsMulCommutative V]

private theorem exists_crossed_retraction (h : V.IsComplement' K) :
    ∃ f : G → V, (∀ x y, f (x * y) = f x * MulAut.conjNormal x (f y)) ∧
      (∀ v : V, f v = v) := by
  refine ⟨fun g => (h.equiv g).1, ?_, ?_⟩
  · intro x y
    calc
      (h.equiv (x * y)).1 = (h.equiv (x * (h.equiv y).1)).1 := by
        conv_lhs => rw [← h.equiv_fst_mul_equiv_snd y, ← mul_assoc, h.equiv_mul_right]
      _ = (h.equiv ((MulAut.conjNormal x (h.equiv y).1 : V) * x)).1 := by
        congr 2
        simp [mul_assoc]
      _ = MulAut.conjNormal x (h.equiv y).1 * (h.equiv x).1 := by
        rw [h.equiv_mul_left]
      _ = (h.equiv x).1 * MulAut.conjNormal x (h.equiv y).1 := mul_comm _ _
  · intro v
    exact h.equiv_fst_eq_self_of_mem_of_one_mem K.one_mem v.property

omit [IsMulCommutative V] in
private theorem exists_complement_of_crossed (f : G → V)
    (hf : ∀ x y, f (x * y) = f x * MulAut.conjNormal x (f y))
    (hbij : Function.Bijective (fun v : V => f v)) :
    ∃ K : Subgroup G, V.IsComplement' K := by
  have hf1 : f 1 = 1 := by
    have he := hf 1 1
    have he' : f 1 = f 1 * f 1 := by simpa using he
    exact mul_eq_left.mp he'.symm
  let K : Subgroup G :=
    { carrier := {x | f x = 1}
      one_mem' := hf1
      mul_mem' := by
        intro x y hx hy
        change f (x * y) = 1
        rw [hf, hx, hy, map_one, one_mul]
      inv_mem' := by
        intro x hx
        have he := hf x⁻¹ x
        rw [inv_mul_cancel, hf1, hx, map_one, mul_one] at he
        exact he.symm }
  refine ⟨K, isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_⟩
  · apply disjoint_def.mpr
    intro x hxV hxK
    have hx : f x = 1 := hxK
    have hv : (⟨x, hxV⟩ : V) = 1 := hbij.1 (hx.trans hf1.symm)
    exact congrArg Subtype.val hv
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨v, hv⟩ := hbij.2 (f x)
    change f (v : G) = f x at hv
    refine ⟨v, v.property, (v : G)⁻¹ * x, ?_, mul_inv_cancel_left _ _⟩
    change f ((v : G)⁻¹ * x) = 1
    have he := hf v ((v : G)⁻¹ * x)
    rw [mul_inv_cancel_left, hv] at he
    have hz : MulAut.conjNormal (v : G) (f ((v : G)⁻¹ * x)) = 1 :=
      mul_eq_left.mp he.symm
    exact (MulAut.conjNormal (v : G)).injective (hz.trans (map_one _).symm)

end Subgroup

namespace Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] {V K H : Subgroup G}

/-- Restrict an actual complement to any subgroup containing its first factor. -/
public theorem IsComplement'.subgroupOf_overgroup (h : V.IsComplement' K) (hVH : V ≤ H) :
    (V.subgroupOf H).IsComplement' (K.subgroupOf H) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · apply disjoint_def.mpr
    intro x hxV hxK
    exact Subtype.ext (disjoint_def.mp h.disjoint hxV hxK)
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨⟨v, k⟩, he⟩ := h.2 (x : G)
    have hkH : (k : G) ∈ H := by
      have he' : (k : G) = (v : G)⁻¹ * (x : G) := by
        rw [← he, inv_mul_cancel_left]
      rw [he']
      exact H.mul_mem (H.inv_mem (hVH v.property)) x.property
    refine ⟨⟨v, hVH v.property⟩, v.property, ⟨k, hkH⟩, k.property, ?_⟩
    exact Subtype.ext he

end Subgroup

namespace Subgroup
open scoped IsMulCommutative
open GroupTheory.CrossedHomTransfer
variable {G : Type*} [Group G] [Finite G]

/-- Splitting over an abelian normal subgroup can be checked in an overgroup
of index coprime to its order. -/
public theorem exists_complement_of_coprime_overgroup
    (V H : Subgroup G) [V.Normal] [IsMulCommutative V]
    (hVH : V ≤ H) (hcoprime : (Nat.card V).Coprime H.index)
    (hsplit : ∃ K : Subgroup H, (V.subgroupOf H).IsComplement' K) :
    ∃ K : Subgroup G, V.IsComplement' K := by
  obtain ⟨K, hK⟩ := hsplit
  let W := V.subgroupOf H
  let e : W ≃* V := subgroupOfEquivOfLe hVH
  have : IsMulCommutative W := ⟨⟨fun a b => by
    apply e.injective
    simp only [map_mul, mul_comm]⟩⟩
  obtain ⟨f₀, hf₀, hf₀V⟩ := exists_crossed_retraction W K hK
  let f : H → V := fun x => e (f₀ x)
  have hf (x y : H) : f (x * y) = f x * MulAut.conjNormal (x : G) (f y) := by
    dsimp [f]
    rw [hf₀, map_mul]
    congr 1
  have hfV (v : V) : f (inclusion hVH v) = v := by
    change e (f₀ (inclusion hVH v)) = v
    have he : inclusion hVH v = ((e.symm v : W) : H) := rfl
    rw [he, hf₀V, e.apply_symm_apply]
  let F : G → V := transfer H MulAut.conjNormal f
  have hF (x y : G) : F (x * y) = F x * MulAut.conjNormal x (F y) :=
    transfer_mul H MulAut.conjNormal f hf x y
  have hFV (v : V) : F v = v ^ H.index :=
    transfer_on_normal V H hVH f hfV v
  apply exists_complement_of_crossed V F hF
  simpa only [hFV, ← powCoprime_apply hcoprime] using (powCoprime hcoprime).bijective

/-- Gaschütz's complement theorem with a coprime-index overgroup. -/
public theorem exists_complement_iff_coprime_overgroup
    (V H : Subgroup G) [V.Normal] [IsMulCommutative V]
    (hVH : V ≤ H) (hcoprime : (Nat.card V).Coprime H.index) :
    (∃ K : Subgroup G, V.IsComplement' K) ↔
      ∃ K : Subgroup H, (V.subgroupOf H).IsComplement' K := by
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K.subgroupOf H, hK.subgroupOf_overgroup hVH⟩
  · exact exists_complement_of_coprime_overgroup V H hVH hcoprime

/-- Gaschütz's splitting theorem for an abelian normal p-subgroup. -/
public theorem exists_complement_iff_sylow
    {p : ℕ} [Fact p.Prime] (V : Subgroup G) [V.Normal] [IsMulCommutative V]
    (hV : IsPGroup p V) (P : Sylow p G) :
    (∃ K : Subgroup G, V.IsComplement' K) ↔
      ∃ K : Subgroup P, (V.subgroupOf (P : Subgroup G)).IsComplement' K := by
  have hVP : V ≤ (P : Subgroup G) := hV.le_sylow_of_normal P
  exact exists_complement_iff_coprime_overgroup V P hVP
    (P.card_coprime_index.coprime_dvd_left (card_dvd_of_le hVP))

end Subgroup

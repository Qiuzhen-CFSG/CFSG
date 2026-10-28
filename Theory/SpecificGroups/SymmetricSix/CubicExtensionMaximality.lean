module
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.Tactic.NormNum

/-!
# Index-fifteen subgroups of cubic extensions of S₆

Simplicity of A₆ excludes subgroups of indices three and five in S₆.
An index-fifteen subgroup in a group of order 3·|S₆| maps onto an
index-fifteen subgroup of S₆: a full image would have order larger than
the source, and the two smaller nontrivial indices are excluded. The
subgroup therefore contains the cubic kernel and is maximal. The cubic
kernel is exactly the kernel of the resulting fifteen-point action.

This supplies the maximality of the Mathieu point–plane flag stabilizer
in Aschbacher, *Sporadic Groups* (1994), 41.1, pp.219–220. The extension
and quotient map remain literal; no complement or action identification
is assumed.
-/

public noncomputable section
open Subgroup
namespace SymmetricSix.CubicExtension
private theorem small_index_dvd_two (H : Subgroup (Equiv.Perm (Fin 6)))
    (hH : H.index ≤ 5) : H.index ∣ 2 := by
  let A := alternatingGroup (Fin 6)
  let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  have hA : H.subgroupOf A = ⊤ := by
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hb : (H.subgroupOf A).index ≤ 5 :=
      (show H.relIndex A ≤ H.index from by
        simpa using relIndex_le_of_le_right (H := H) (show A ≤ ⊤ from le_top)
          (by simpa using (show H.index ≠ 0 from Subgroup.index_ne_zero_of_finite))).trans hH
    have hf := Nat.factorial_le hb
    have hc : Nat.card A = 360 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hc]
    norm_num [Nat.factorial] at hf ⊢
    omega
  have hle : A ≤ H := by
    intro a ha
    exact show (⟨a, ha⟩ : A) ∈ H.subgroupOf A from hA ▸ mem_top _
  simpa only [A, alternatingGroup.index_eq_two] using index_dvd_of_le hle

private theorem divisor_fifteen {n : ℕ} (h : n ∣ 15) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 15 := by
  have := Nat.mem_divisors.mpr ⟨h, (by decide : 15 ≠ 0)⟩
  simpa only [show Nat.divisors 15 = {1, 3, 5, 15} by decide,
    Finset.mem_insert, Finset.mem_singleton] using this

/-- Every index-15 subgroup of S₆ is maximal, by simplicity of A₆. -/
theorem index_fifteen_maximal (H : Subgroup (Equiv.Perm (Fin 6)))
    (hH : H.index = 15) : IsCoatom H := by
  refine ⟨fun he => by simp [he] at hH, ?_⟩
  intro K hK
  have hd := index_dvd_of_le hK.le
  rw [hH] at hd
  have hl := index_strictAnti hK
  rw [hH] at hl
  rcases divisor_fifteen hd with he | he | he | he
  · exact index_eq_one.mp he
  · have := small_index_dvd_two K (by omega)
    rw [he] at this
    norm_num at this
  · have := small_index_dvd_two K (by omega)
    rw [he] at this
    norm_num at this
  · omega

variable {G : Type*} [Group G] [Finite G]

private theorem cubic_image (C H : Subgroup G) [C.Normal]
    (hC : Nat.card C = 3) (e : (G ⧸ C) ≃* Equiv.Perm (Fin 6))
    (hH : H.index = 15) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' C)
    (H.map f).index = 15 ∧ (H.map f).comap f = H := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' C)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective C)
  have hG : Nat.card G = 2160 := by
    rw [card_eq_card_quotient_mul_card_subgroup C, Nat.card_congr e.toEquiv, hC]
    norm_num [Nat.card_perm, Fintype.card_perm, Nat.factorial]
  have hcH : Nat.card H = 144 := by
    have hh := H.card_mul_index
    rw [hH, hG] at hh
    omega
  have hi : (H.map f).index = 15 := by
    have hd := H.index_map_dvd hf
    rw [hH] at hd
    rcases divisor_fifteen hd with he | he | he | he
    · have ht := index_eq_one.mp he
      have hc := card_map_dvd (H := H) f
      rw [ht, Subgroup.card_top, hcH] at hc
      norm_num [Nat.card_perm, Fintype.card_perm, Nat.factorial] at hc
    · have := small_index_dvd_two (H.map f) (by omega)
      rw [he] at this
      norm_num at this
    · have := small_index_dvd_two (H.map f) (by omega)
      rw [he] at this
      norm_num at this
    · exact he
  have heq : (H.map f).comap f = H := by
    apply le_antisymm ?_ (le_comap_map f H)
    by_contra hn
    have hlt : H < (H.map f).comap f := lt_of_le_of_ne (le_comap_map f H)
      (fun he => hn he.ge)
    have hs := index_strictAnti hlt
    rw [index_comap_of_surjective _ hf, hi, hH] at hs
    omega
  exact ⟨hi, heq⟩

/-- A normal cubic kernel does not introduce an intermediate overgroup
of an index-15 subgroup. No splitting of the extension is assumed. -/
theorem index_fifteen_maximal_of_cubic (C H : Subgroup G) [C.Normal]
    (hC : Nat.card C = 3) (e : (G ⧸ C) ≃* Equiv.Perm (Fin 6))
    (hH : H.index = 15) : IsCoatom H := by
  obtain ⟨hi, heq⟩ := cubic_image C H hC e hH
  rw [← heq]
  exact isCoatom_comap_of_surjective
    (e.surjective.comp (QuotientGroup.mk'_surjective C)) (index_fifteen_maximal _ hi)

/-- The index-fifteen permutation action of S₆ is faithful. -/
theorem index_fifteen_normalCore (H : Subgroup (Equiv.Perm (Fin 6)))
    (hH : H.index = 15) : H.normalCore = ⊥ := by
  by_contra hn
  have hnt : Nontrivial H.normalCore := (nontrivial_iff_ne_bot _).mpr hn
  have ha := (Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (by simp) hnt).trans
    H.normalCore_le
  have hd := index_dvd_of_le ha
  rw [hH, alternatingGroup.index_eq_two] at hd
  norm_num at hd

/-- The cubic kernel is exactly the kernel on the fifteen cosets. -/
theorem index_fifteen_normalCore_of_cubic (C H : Subgroup G) [C.Normal]
    (hC : Nat.card C = 3) (e : (G ⧸ C) ≃* Equiv.Perm (Fin 6))
    (hH : H.index = 15) : H.normalCore = C := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' C)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective C)
  obtain ⟨hi, heq⟩ := cubic_image C H hC e hH
  have hk : f.ker = C := by
    ext g
    change e (QuotientGroup.mk g) = 1 ↔ g ∈ C
    rw [e.map_eq_one_iff, QuotientGroup.eq_one_iff]
  apply le_antisymm
  · have : (H.normalCore.map f).Normal := Normal.map inferInstance f hf
    have hm : H.normalCore.map f ≤ (H.map f).normalCore :=
      normal_le_normalCore.mpr (map_mono H.normalCore_le)
    rw [index_fifteen_normalCore _ hi] at hm
    have hn := (map_le_iff_le_comap).mp hm
    rwa [MonoidHom.comap_bot, hk] at hn
  · apply normal_le_normalCore.mpr
    calc
      C = f.ker := hk.symm
      _ ≤ (H.map f).comap f := ker_le_comap f _
      _ = H := heq
end SymmetricSix.CubicExtension

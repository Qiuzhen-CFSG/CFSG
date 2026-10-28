module

public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Faithful SL₂ subgroups through cubic central kernels

A central element of SL₂ has square one. Consequently a central kernel of
exponent three is injective on every actual SL₂ subgroup. An SL₂ over a
finite field of odd order cannot embed in a two-group: its upper root
subgroup has the odd cardinality of the field.

These elementary kernel facts allow the odd involution-centralizer rows to
include prime three, where the SL₂ subgroup is not a component.
Source: Aschbacher--Smith A.3.21(a), printed p.55, used in G.4.1, p.342.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Matrix Subgroup
open scoped MatrixGroups
namespace Theory.GroupTheory
variable {G H F : Type*} [Group G] [Group H] [Field F]

theorem injective_sl2_of_cubic_central_kernel
    (f : G →* H) (hk : f.ker ≤ center G)
    (h3 : ∀ x ∈ f.ker, x ^ 3 = 1) (K : Subgroup G)
    (e : K ≃* SL(2,F)) : Function.Injective (f.subgroupMap K) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hxk : (x : G) ∈ f.ker :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hc : e x ∈ center SL(2,F) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [←map_mul, ←map_mul]
    congr 1
    exact Subtype.ext (mem_center_iff.mp (hk hxk) y)
  obtain ⟨a, ha, hea⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  simp only [Fintype.card_fin] at ha
  have hs : e x ^ 2 = 1 := by
    rcases sq_eq_one_iff.mp ha with rfl | rfl
    · have he : e x = 1 := Subtype.ext (by simpa using hea.symm)
      simp [he]
    · have he : e x = -1 := Subtype.ext (by simpa [←Matrix.diagonal_neg] using hea.symm)
      simp [he]
  have ht : e x ^ 3 = 1 := by
    rw [←map_pow]
    exact (congrArg e (show x ^ 3 = 1 from Subtype.ext (h3 x hxk))).trans (map_one e)
  rw [pow_succ, hs, one_mul] at ht
  exact (e.injective (ht.trans (map_one e).symm) : x = 1)

theorem not_twoGroup_of_sl2_odd_embedding [Finite F]
    (hodd : Odd (Nat.card F)) (f : SL(2,F) →* H) (hf : Function.Injective f) :
    ¬ IsPGroup 2 H := by
  intro hp
  let j := f.comp (SpecialLinearGroup.upperUnipotentHom F)
  have hj : Function.Injective j := hf.comp (SpecialLinearGroup.upperUnipotentHom_injective F)
  have ha := hp.of_injective j hj
  rcases ha.card_eq_or_dvd with hc | hc
  · have he : Nat.card F = 1 := by simpa only [Nat.card_congr Multiplicative.toAdd] using hc
    exact zero_ne_one ((Nat.card_eq_one_iff_unique.mp he).1.elim (0 : F) 1)
  · exact hodd.not_two_dvd_nat (by simpa only [Nat.card_congr Multiplicative.toAdd] using hc)
end Theory.GroupTheory

module

public import Theory.GroupAction.FaithfulSixteen
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card
/-!
# An involution-fusion obstruction to a transitive quotient action

Suppose a finite subgroup H controls fusion of the involutions in a normal
subgroup Q outside the kernel of an equivariant map to a group of order 16.
If the ambient action were transitive on its fifteen nonidentity elements,
the same would hold for H, forcing 3 to divide |H| by orbit--stabilizer.

This is the orbit-counting form of the final Frattini argument in
Aschbacher--Smith 14.2.21, printed p.989. Equivariance refers to conjugation
on Q itself, so an unrelated representation cannot satisfy the interface.
-/

open Subgroup
namespace Theory.GroupAction

/-- Fusion in a group of order prime to three excludes a transitive ambient orbit. -/
public theorem not_transitive_of_involution_fusion
    {H M V : Type*} [Group H] [Finite H] [Group M] [Group V] [Finite V]
    (i : H →* M) (Q : Subgroup M) [Q.Normal]
    (θ : Q →* V) (ρ : M →* MulAut V)
    (hcompat : ∀ (g : M) (q : Q), ρ g (θ q) = θ (MulAut.conjNormal g q))
    (hV : Nat.card V = 16) (hH : ¬ 3 ∣ Nat.card H)
    (j : Q) (hj : j ^ 2 = 1) (hjθ : θ j ≠ 1)
    (hfusion : ∀ x y : Q, x ^ 2 = 1 → y ^ 2 = 1 → θ x ≠ 1 → θ y ≠ 1 →
      ∃ h : H, i h * (x : M) * (i h)⁻¹ = (y : M)) :
    ¬ (∀ y : V, y ≠ 1 → ∃ g : M, ρ g (θ j) = y) := by
  intro htrans
  let : MulDistribMulAction H V := MulDistribMulAction.compHom V (ρ.comp i)
  have horbit : MulAction.orbit H (θ j) = ({1} : Set V)ᶜ := by
    apply Set.ext
    intro y
    constructor
    · rintro ⟨h, rfl⟩ hy
      apply hjθ
      have he := congrArg (fun x : V => h⁻¹ • x) hy
      simpa only [inv_smul_smul, smul_one] using he
    · intro hy
      obtain ⟨g, hg⟩ := htrans y hy
      let x : Q := MulAut.conjNormal g j
      have hx : x ^ 2 = 1 := by
        change (MulAut.conjNormal g j) ^ 2 = 1
        rw [← map_pow, hj, map_one]
      have hxθ : θ x = y := (hcompat g j).symm.trans hg
      obtain ⟨h, hh⟩ := hfusion j x hj hx hjθ (by rwa [hxθ])
      refine ⟨h, ?_⟩
      change ρ (i h) (θ j) = y
      rw [hcompat]
      have he : MulAut.conjNormal (i h) j = x := Subtype.ext hh
      rw [he, hxθ]
  have hc : Nat.card (MulAction.orbit H (θ j)) = 15 := by
    rw [horbit]
    change (({1} : Set V)ᶜ).ncard = 15
    rw [Set.ncard_compl, hV, Set.ncard_singleton]
  have hd : 15 ∣ Nat.card H := by
    have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H (θ j))
    rw [Nat.card_prod, hc] at hh
    exact ⟨_, hh.symm⟩
  exact hH ((by decide : 3 ∣ 15).trans hd)
/-- Injective transport of local involution fusion to the actual normal core. -/
public theorem mapped_involution_fusion {H M V : Type*} [Group H] [Group M] [Group V]
    (i : H →* M) (hi : Function.Injective i)
    (QH FH : Subgroup H) (Q : Subgroup M) (hQ : QH.map i = Q)
    (θ : Q →* V) (hθ : θ.ker = (FH.map i).subgroupOf Q)
    (hfusion : ∀ x y : H, x ∈ QH → y ∈ QH → x ^ 2 = 1 → y ^ 2 = 1 →
      x ∉ FH → y ∉ FH → IsConj x y) :
    ∀ x y : Q, x ^ 2 = 1 → y ^ 2 = 1 → θ x ≠ 1 → θ y ≠ 1 →
      ∃ h : H, i h * (x : M) * (i h)⁻¹ = (y : M) := by
  intro x y hx hy hxθ hyθ
  obtain ⟨a, ha, hea⟩ := hQ.ge x.property
  obtain ⟨b, hb, heb⟩ := hQ.ge y.property
  have hap : a ^ 2 = 1 := hi (by
    rw [map_pow, map_one, hea]
    exact congrArg Subtype.val hx)
  have hbp : b ^ 2 = 1 := hi (by
    rw [map_pow, map_one, heb]
    exact congrArg Subtype.val hy)
  have haF : a ∉ FH := by
    intro h
    apply hxθ
    apply MonoidHom.mem_ker.mp
    rw [hθ]
    change (x : M) ∈ FH.map i
    rw [← hea]
    exact mem_map_of_mem i h
  have hbF : b ∉ FH := by
    intro h
    apply hyθ
    apply MonoidHom.mem_ker.mp
    rw [hθ]
    change (y : M) ∈ FH.map i
    rw [← heb]
    exact mem_map_of_mem i h
  obtain ⟨h, hh⟩ := isConj_iff.mp (hfusion a b ha hb hap hbp haF hbF)
  exact ⟨h, by simpa only [map_mul, map_inv, hea, heb] using congrArg i hh⟩

end Theory.GroupAction

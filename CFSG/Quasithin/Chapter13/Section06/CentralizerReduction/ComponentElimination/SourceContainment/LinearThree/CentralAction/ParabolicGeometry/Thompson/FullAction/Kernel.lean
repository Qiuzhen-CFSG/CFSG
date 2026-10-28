module
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-!
# The kernel argument for the full central-branch action

Faithful actions of a centerless normal factor and a commuting normal
factor remain faithful on their product. If the remaining quotient is a
two-group and the ambient two-core is trivial, the whole action is faithful.
A nontrivial cubic action is faithful; core-free images of groups with
cubic two-core quotient have order dividing three.

These are the group-theoretic steps applied to K+, L_v+ and T_v+ in the
proof of Aschbacher–Smith 13.6.20, printed p.931 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.FullAction.Kernel
variable {D H : Type*} [Group D] [Group H]

/-- A kernel faithful on two commuting factors is a two-group when the
remaining quotient is a two-group. -/
theorem injective_of_commuting_supplement (f : D →* H)
    (K C R : Subgroup D) [K.Normal] [C.Normal]
    (hc : ⁅K, C⁆ = ⊥) (hz : center K = ⊥)
    (hfK : Function.Injective (f.comp K.subtype))
    (hfC : Function.Injective (f.comp C.subtype))
    (hR : IsPGroup 2 R) (hgen : K ⊔ C ⊔ R = ⊤)
    (hcore : pCore 2 D = ⊥) : Function.Injective f := by
  have hk (x : D) (hx : x ∈ K ⊔ C) (hfx : f x = 1) : x = 1 := by
    obtain ⟨k, hk, c, hc', rfl⟩ := mem_sup_of_normal_left.mp hx
    have hfk : f k = (f c)⁻¹ := eq_inv_of_mul_eq_one_left (by rwa [← map_mul])
    have hkz : (⟨k, hk⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro j
      apply hfK
      change f ((j : D) * k) = f (k * (j : D))
      rw [map_mul, map_mul, hfk]
      exact ((show Commute (j : D) c from
        (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hc) j.property) c hc').symm).map f).inv_right.eq
    have hk1 : k = 1 := congrArg Subtype.val (show (⟨k, hk⟩ : K) = 1 from mem_bot.mp (hz ▸ hkz))
    rw [hk1, one_mul] at hfx ⊢
    exact congrArg Subtype.val (hfC (a₁ := ⟨c, hc'⟩) (a₂ := 1) (hfx.trans (map_one _).symm))
  let N := K ⊔ C
  let q : f.ker →* D ⧸ N := (QuotientGroup.mk' N).comp f.ker.subtype
  have hq : Function.Injective q := by
    apply q.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro x hx
    exact Subtype.ext (hk x ((QuotientGroup.eq_one_iff _).mp hx) x.property)
  have hp : IsPGroup 2 f.ker :=
    (isPGroup_quotient_of_sup_eq_top N R hR hgen).of_injective q hq
  apply f.ker_eq_bot_iff.mp
  exact le_bot_iff.mp (hcore ▸ (show f.ker ≤ pCore 2 D from le_sSup ⟨inferInstance, hp⟩))

/-- A nontrivial action of a cubic group is faithful. -/
theorem injective_of_cubic (f : D →* H) (hcard : Nat.card D = 3)
    (hne : f ≠ 1) : Function.Injective f := by
  let : Fact (Nat.card D).Prime := ⟨hcard ▸ Nat.prime_three⟩
  rcases f.ker.eq_bot_or_eq_top_of_prime_card with h | h
  · exact f.ker_eq_bot_iff.mp h
  · apply (hne ?_).elim
    ext x
    exact h.ge (mem_top x)

/-- A core-free image of a group with cubic two-core quotient has order
one or three. -/
theorem card_dvd_cubic_of_corefree_image {A : Type*} [Group A] [Finite A]
    (q : A →* D) (hq : Function.Surjective q) (hcore : pCore 2 D = ⊥)
    (hcard : Nat.card (A ⧸ pCore 2 A) = 3) : Nat.card D ∣ 3 := by
  have hmap : (pCore 2 A).map q ≤ pCore 2 D :=
    le_sSup ⟨Subgroup.Normal.map inferInstance q hq, pCore_isPGroup.map q⟩
  have hk : pCore 2 A ≤ q.ker :=
    (Subgroup.map_eq_bot_iff _).mp (bot_unique (hmap.trans hcore.le))
  let f : A ⧸ pCore 2 A →* D := QuotientGroup.lift _ q hk
  have hf : Function.Surjective f := by
    intro d
    obtain ⟨a, rfl⟩ := hq d
    exact ⟨QuotientGroup.mk' _ a, rfl⟩
  exact hcard ▸ Subgroup.card_dvd_of_surjective f hf

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.FullAction.Kernel

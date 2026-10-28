module

public import Theory.SpecificGroups.SL2.DefiningRank
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Unipotent products from commuting faithful SL₂ subgroups

For commuting faithful SL₂(F) and SL₂(K) maps, their two upper-unipotent
groups have trivial intersection: an element in the intersection centralizes
the first SL₂, whereas a central transvection is the identity. Their product
therefore embeds F × K into the centralizer of the first scalar involution.
No perfectness hypothesis is used, so the result includes SL₂(3).

This is the elementary subgroup used in the odd triality involution
centralizer, with K the cubic extension of F. The corresponding application
retains the actual pinned maps in Triality.Standard.Carrier.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, A.2.17, printed p.39.
-/

public section

open Matrix Subgroup
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup.CommutingUnipotents
variable {F K H : Type*} [Field F] [Field K] [Group H]
variable (f : SL(2,F) →* H) (g : SL(2,K) →* H)
variable (hc : ∀ a b, Commute (f a) (g b))

def pair : Multiplicative F × Multiplicative K →* H :=
  (f.comp (upperUnipotentHom F)).noncommCoprod (g.comp (upperUnipotentHom K))
    (fun _ _ => hc _ _)

theorem pair_injective (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (pair f g hc) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨a,b⟩ hab
  change f (upperUnipotentHom F a) * g (upperUnipotentHom K b) = 1 at hab
  have he : f (upperUnipotentHom F a) = (g (upperUnipotentHom K b))⁻¹ :=
    eq_inv_of_mul_eq_one_left hab
  have haZ : upperUnipotentHom F a ∈ center SL(2,F) := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply hf
    rw [map_mul, map_mul, he]
    exact (hc x (upperUnipotentHom K b)).inv_right.eq
  have ha : a = 1 := (transvection_mem_center_iff zero_ne_one a.toAdd).mp haZ
  have hb : b = 1 := by
    rw [ha, map_one, map_one, one_mul] at hab
    apply upperUnipotentHom_injective K
    apply hg
    simpa only [map_one] using hab
  exact Prod.ext ha hb

local instance : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩

def centralizerPair : Multiplicative F × Multiplicative K →*
    centralizer ({f (-1)} : Set H) :=
  (pair f g hc).codRestrict _ (fun a => by
    apply mem_centralizer_singleton_iff.mpr
    change Commute (f (upperUnipotentHom F a.1) * g (upperUnipotentHom K a.2)) (f (-1))
    apply Commute.mul_left _ ((hc (-1) _).symm)
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul]
    congr 1
    simp)

theorem centralizerPair_injective (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (centralizerPair f g hc) := by
  intro a b hab
  exact pair_injective f g hc hf hg (congrArg Subtype.val hab)

theorem pair_exponent (p : ℕ) [CharP F p] [CharP K p]
    (a : Multiplicative F × Multiplicative K) : a ^ p = 1 := by
  apply Prod.ext
  · change p • a.1.toAdd = 0
    simp [nsmul_eq_mul]
  · change p • a.2.toAdd = 0
    simp [nsmul_eq_mul]

end Matrix.SpecialLinearGroup.CommutingUnipotents

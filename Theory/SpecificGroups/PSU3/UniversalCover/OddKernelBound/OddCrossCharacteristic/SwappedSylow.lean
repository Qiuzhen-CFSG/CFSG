module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection
public import Theory.GroupTheory.CentralExtensionSwap
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow

/-!
# Swapped Sylow torus generators in a projective unitary group

Two commuting generators exchanged by ambient conjugation have commuting
lifts in every central extension when their order is odd. Their full
preimage is therefore abelian. Central Sylow transfer excludes the Sylow
prime from a perfect central-cover kernel.

The witness records actual projective matrices and generation of an actual
Sylow subgroup. Constructing it for the diagonal r-torus, r > 3 dividing
q+1, remains a separate matrix calculation; this module proves its cover
consumer, not that existence statement.

Source: the central-transfer calculation underlying Aschbacher–Smith
I.1.2–I.1.4, printed pp.407–408 (PDF pp.418–419), and GLS3 §6.1.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups PerfectCentralCovering

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- Literal commuting Sylow generators and an ambient element exchanging them. -/
structure SwappedSylow (r : ℕ) where
  sylow : Sylow r (ProjectiveSpecialUnitaryMatrixGroup J)
  x : ProjectiveSpecialUnitaryMatrixGroup J
  y : ProjectiveSpecialUnitaryMatrixGroup J
  swapper : ProjectiveSpecialUnitaryMatrixGroup J
  generates : closure ({x, y} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = sylow
  commute : Commute x y
  swap_x : swapper * x * swapper⁻¹ = y
  swap_y : swapper * y * swapper⁻¹ = x

/-- Apply the swapping equations to the kernel of the given perfect cover. -/
theorem not_dvd_kernel_of_swapped_sylow {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (d : SwappedSylow J r) {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact r.Prime := ⟨hr⟩
  let : Group.IsPerfect E := f.isPerfect
  have hx : d.x ∈ (d.sylow : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    d.generates ▸ subset_closure (by simp)
  obtain ⟨k, hk⟩ := d.sylow.isPGroup'.exists_card_eq
  have hn : (Nat.card d.sylow).Coprime 2 := by
    rw [hk]
    apply Nat.Coprime.pow_left
    apply (Nat.prime_two.coprime_iff_not_dvd.mpr _).symm
    intro hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp hd).symm
  have hxpow : d.x ^ Nat.card d.sylow = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨d.x, hx⟩ : d.sylow)))
  obtain ⟨a, ha⟩ := f.surjective d.x
  obtain ⟨b, hb⟩ := f.surjective d.y
  have hab := CentralExtension.commute_lifts_of_swap f.toMonoidHom f.surjective
    f.ker_le_center d.x d.y d.swapper hn hxpow d.commute d.swap_x d.swap_y a b ha hb
  apply not_dvd_card_kernel_of_abelian_sylow_preimage f.toMonoidHom f.surjective
    f.ker_le_center d.sylow
  exact CentralExtension.isMulCommutative_comap_of_pair_lifts f.toMonoidHom
    f.ker_le_center (d.sylow : Subgroup _) a b hab
    (by simpa only [ha, hb] using d.generates)

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic

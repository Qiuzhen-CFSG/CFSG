module

public import Theory.SpecificGroups.ReeG2.InvolutionProjectiveProduct
public import GorensteinWalter.PSL2DihedralSylow
public import GorensteinWalter.DihedralCore
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Two-rank of the full small Ree matrix group

A Klein four in the genuine projective SL₂ subgroup commutes with the
independent torus involution. Their join is elementary abelian of order eight.
The argument works also at the nonsimple full parameter m=0; its derived
endpoint is a separate carrier.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup
namespace Atlas.ReeG2
open InvolutionProduct
variable (F : Type*) [Field F] [Finite F] [CharP F 3]
/-- The actual full Ree carrier contains an elementary abelian subgroup of order eight. -/
theorem three_le_twoRank (m : ℕ) : 3 ≤ primeRank 2 (Model F m) := by
  classical
  let := Fintype.ofFinite F
  obtain ⟨e, _, he⟩ := FiniteField.card F 3
  have ho : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨3, e, Nat.prime_three, by decide, e.pos, by simpa only [Nat.card_eq_fintype_card] using he⟩
  let P : Sylow 2 (GorensteinWalter.PSL2 F) := Classical.choice inferInstance
  obtain ⟨k, hk, ⟨a⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F ho P
  obtain ⟨V, _, hV⟩ := GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (P : Subgroup (GorensteinWalter.PSL2 F)) hk a
  let : IsKleinFour V := hV
  let : IsElementaryAbelian 2 V := { toIsMulCommutative := IsKleinFour.isMulCommutative, exponent_dvd_p := by simp }
  let E := V.map (projectiveHom (F := F) m)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hc : Nat.card E = 2 ^ 2 := by
    rw [Subgroup.card_map_of_injective (projectiveHom_injective m)]
    simp
  have hz : orderOf (torusInvolution (F := F) m) = 2 :=
    orderOf_eq_prime (torusInvolution_sq m) (torusInvolution_ne_one m)
  have hne : torusInvolution (F := F) m ∉ E := by
    rintro ⟨g, _, hg⟩
    exact projectiveHom_ne_involution m g hg
  have hfix : E ≤ centralizer ({torusInvolution (F := F) m} : Set (Model F m)) := by
    rintro x ⟨g, _, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (projectiveHom_commute m g).eq.symm
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join E _ hz hne hfix hc
end Atlas.ReeG2

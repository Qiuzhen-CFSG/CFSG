module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.PointParabolic
public import Theory.SpecificGroups.PSL3Two.ProperSubgroups

/-!
# Perfect residuals in native max4 point parabolics

The five-point stabilizer is solvable, while every proper subgroup of
SL₃(2) is solvable. Hence a nontrivial perfect subgroup of their product
is exactly the linear factor. A perfect subgroup in the native preimage
which is not a two-group retains a nontrivial image through the actual
two-kernel and therefore has this same literal quotient image.

The original L₁* application, using its full quotient kernel and the same
component equivalence as the parabolic, is in `Normalizers/JankoMax4`.
Source: Aschbacher–Smith, proof of 12.5.3, printed p.818/PDF p.835.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.SymmetricLinear

private theorem point_stabilizer_solvable (j : Fin 5) :
    Group.IsSolvable (MulAction.stabilizer (Equiv.Perm (Fin 5)) j) := by
  let P := MulAction.stabilizer (Equiv.Perm (Fin 5)) j
  have hi : P.index = 5 := by
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ]
    simp
  have hc : Nat.card P = 24 := by
    have hc := P.card_mul_index
    rw [hi, Nat.card_perm, Nat.card_fin] at hc
    change Nat.card P * 5 = 120 at hc
    omega
  let S : Sylow 2 P := default
  let := S.isPGroup'.isNilpotent
  apply (S : Subgroup P).isSolvable_of_index_le_four
  have hS : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity, hc]
    decide +kernel
  have he := (S : Subgroup P).card_mul_index
  rw [hS, hc] at he
  omega

/-- The linear factor is the only nontrivial perfect subgroup of the point product. -/
theorem perfect_quotient_marking (j : Fin 5) (B : Subgroup QuotientModel)
    [Group.IsPerfect B] (hB : B ≠ ⊥)
    (hle : B ≤ (MulAction.stabilizer (Equiv.Perm (Fin 5)) j).prod ⊤) :
    B = (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod ⊤ := by
  let f : QuotientModel →* Equiv.Perm (Fin 5) := MonoidHom.fst _ _
  let g : QuotientModel →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := MonoidHom.snd _ _
  have hf : B.map f = ⊥ := by
    let : Group.IsPerfect (B.map f) := Group.IsPerfect.map f
    let := point_stabilizer_solvable j
    have hl : B.map f ≤ MulAction.stabilizer (Equiv.Perm (Fin 5)) j := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hle hx).1
    let : Group.IsSolvable (B.map f) := Group.isSolvable_of_isSolvable_injective
      (f := inclusion hl) (inclusion_injective hl)
    by_contra hn
    let : Nontrivial (B.map f) := (nontrivial_iff_ne_bot _).mpr hn
    exact Group.IsPerfect.not_isSolvable (B.map f) inferInstance
  have hfst (x : QuotientModel) (hx : x ∈ B) : x.1 = 1 :=
    mem_bot.mp (hf ▸ mem_map_of_mem f hx)
  have hg : B.map g = ⊤ := by
    let : Group.IsPerfect (B.map g) := Group.IsPerfect.map g
    have hn : B.map g ≠ ⊥ := by
      intro he
      apply hB
      apply eq_bot_iff.mpr
      intro x hx
      apply mem_bot.mpr
      exact Prod.ext (hfst x hx) (mem_bot.mp (he ▸ mem_map_of_mem g hx))
    let : Nontrivial (B.map g) := (nontrivial_iff_ne_bot _).mpr hn
    by_contra ht
    exact Group.IsPerfect.not_isSolvable (B.map g)
      (Matrix.PSL3Two.isSolvable_subgroup_SL_of_ne_top _ ht)
  ext x
  constructor
  · intro hx
    exact ⟨hfst x hx, mem_top _⟩
  · rintro ⟨hx, _⟩
    have hm : x.2 ∈ B.map g := hg ▸ mem_top _
    obtain ⟨y, hy, he⟩ := hm
    have heq : y = x := Prod.ext ((hfst y hy).trans hx.symm) he
    exact heq ▸ hy

/-- The native two-kernel does not erase a perfect non-two residual. -/
theorem perfect_native_marking (j : Fin 5) (B : Subgroup max4Subgroup)
    [Group.IsPerfect B] (hB : ¬ IsPGroup 2 B)
    (hle : B ≤ ((MulAction.stabilizer (Equiv.Perm (Fin 5)) j).prod ⊤).comap
      max4Projection) :
    B.map max4Projection = (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod ⊤ := by
  let : Group.IsPerfect (B.map max4Projection) := Group.IsPerfect.map _
  apply perfect_quotient_marking j _
  · intro he
    have hk : B ≤ max4Projection.ker := (Subgroup.map_eq_bot_iff _).mp he
    exact hB (max4Projection_kernel_isTwoGroup.of_injective
      (inclusion hk) (inclusion_injective hk))
  · exact (map_le_iff_le_comap).mpr hle

end Janko4.LocalStructure.SymmetricLinear

module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Outer.Extension
public import Mathlib.GroupTheory.Sylow

/-!
# Outer involutions in every stabilizer Sylow subgroup

Start with the constructed outer involution, place its order-two subgroup in
a Sylow subgroup of the full vector stabilizer, and use Sylow conjugacy inside
that stabilizer. Normality of the inner subgroup preserves outerness. Every
resulting involution supplies the same internal semidirect-product description.

Source: the corrected nonsingular clause of Aschbacher–Smith, H.9.1(4),
printed p.390. The Sylow is a Sylow of the vector stabilizer; there is no claim
that it comes from the earlier pure-vector marking.
-/

public section
namespace BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic
open scoped Pointwise

/-- Every actual Sylow two-subgroup of the full nonsingular stabilizer contains
an outer involution, and that involution complements the inner stabilizer. -/
theorem sylow_exists_outer_involution {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (P : Sylow 2 (fullStabilizer d (x,f))) :
    ∃ s : fullStabilizer d (x,f), s ∈ P ∧
      s.val ∉ MulAut.innerSubgroup (LinearGroup n) ∧ s ^ 2 = 1 ∧
      (innerInFull d (x,f)).IsComplement' (Subgroup.zpowers s) := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : BinaryLinear.OuterCyclic.Space n →
      BinaryLinear.OuterCyclic.Space n)) DFunLike.coe_injective
  let : Finite (MulAut (LinearGroup n)) := Finite.of_injective
    (fun a : MulAut (LinearGroup n) => (a : LinearGroup n → LinearGroup n))
    DFunLike.coe_injective
  obtain ⟨a, ha, hout, hsq⟩ := exists_outer_involution (by omega) d h
  let s : fullStabilizer d (x,f) := ⟨a, ha⟩
  have hsout : s ∉ innerInFull d (x,f) := by simpa [s] using hout
  have hs2 : s ^ 2 = 1 := Subtype.ext hsq
  have hsne : s ≠ 1 := fun he => hsout (he ▸ (innerInFull d (x,f)).one_mem)
  have hp : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hs2 hsne]; rfl)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (fullStabilizer d (x,f)) Q P
  let t := (MulAut.conj g) s
  have htP : t ∈ P := by
    rw [← hg]
    exact ⟨s, hQ (Subgroup.mem_zpowers s), rfl⟩
  have htout : t.val ∉ MulAut.innerSubgroup (LinearGroup n) := by
    intro ht
    have ht' : t ∈ innerInFull d (x,f) := (mem_innerInFull d (x,f) t).mpr ht
    have hc := Subgroup.Normal.conj_mem (innerInFull_normal d (x,f)) t ht' g⁻¹
    have he : g⁻¹ * t * (g⁻¹)⁻¹ = s := by dsimp [t]; group
    exact hsout (he ▸ hc)
  have ht2 : t ^ 2 = 1 := by
    change ((MulAut.conj g) s) ^ 2 = 1
    rw [← map_pow, hs2, map_one]
  exact ⟨t, htP, htout, ht2, outer_isComplement hn d h t htout ht2⟩

end BinaryNaturalDual.VectorStabilizers

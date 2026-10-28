module
public import Theory.Representation.SL2.EightTriple
public import Theory.Representation.SL2.BinarySmallInvolution.TripleFixedSpaces
public import Theory.Representation.PGroupRegularCoordinates
public import Theory.GroupTheory.RegularKernelSplitting
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Splitting extensions by the actual binary eight-dimensional module

The irreducible eight-dimensional action of SL₂(8) is its triple module.
Its Sylow-eight fixed space is a single line, so the original binary module
has regular coordinates on that Sylow subgroup. The regular-kernel splitting
and odd-index Gaschütz argument then complement the full original kernel.
-/

public noncomputable section
open Module Matrix.SpecialLinearGroup Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Representation.SL2.BinarySmall
open Representation.BinaryOffender

/-- The original binary action has regular coordinates on the literal upper
Sylow subgroup; the intertwining identity retains that subgroup's inclusion. -/
theorem eight_irreducible_upper_regular
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,GaloisField 2 3) V) [ρ.IsIrreducible]
    (hd : finrank (ZMod 2) V = 8) :
    ∃ e : V ≃ₗ[ZMod 2] (upperUnipotent (GaloisField 2 3) → ZMod 2),
      ∀ (g : upperUnipotent (GaloisField 2 3)) v x, e (ρ g v) x = e v (g⁻¹ * x) := by
  classical
  let K := GaloisField 2 3
  let U := upperUnipotent K
  let : Fintype U := Fintype.ofFinite _
  have hK : Nat.card K = 8 := GaloisField.card 2 3 (by decide)
  have hUc : Nat.card U = 8 := (card_upperUnipotent K).trans hK
  have hUp : IsPGroup 2 U := (upperUnipotentSylow K 2).isPGroup'
  have hfix := TripleFixedSpaces.binary_fixed_mul_card hK ρ
    (eight_irreducible_isTriple ρ hd) U hUp
  rw [hUc] at hfix
  have hf : finrank (ZMod 2) (fixedSpace ρ U) = 1 := by omega
  obtain ⟨z,hz,hspan⟩ := finrank_eq_one_iff'.mp hf
  apply Representation.TwistedRegular.exists_regular_coordinates (ρ.comp U.subtype)
    (by rw [ringChar.eq (ZMod 2) 2]; decide)
    (by rwa [ringChar.eq (ZMod 2) 2]) (z : V)
    (fun h => hz (Subtype.ext h))
  · intro v hv
    obtain ⟨c,hc⟩ := hspan (⟨v,hv⟩ : fixedSpace ρ U)
    exact ⟨c,(congrArg Subtype.val hc).symm⟩
  · rw [hd,← Nat.card_eq_fintype_card,hUc]

/-- A full elementary kernel with its actual irreducible degree-eight
conjugation action has an actual complement in the original extension. -/
theorem exists_complement_of_eight_irreducible_kernel
    {H : Type*} [Group H] [Finite H]
    (q : H →* SL(2,GaloisField 2 3)) (hq : Function.Surjective q)
    [IsElementaryAbelian 2 q.ker]
    (ρ : Representation (ZMod 2) SL(2,GaloisField 2 3) (Additive q.ker))
    [ρ.IsIrreducible]
    (hd : finrank (ZMod 2) (Additive q.ker) = 8)
    (hρ : ∀ (g : H) (v : q.ker),
      ρ (q g) (Additive.ofMul v) = Additive.ofMul (MulAut.conjNormal g v)) :
    ∃ L : Subgroup H, q.ker.IsComplement' L := by
  classical
  let U := upperUnipotent (GaloisField 2 3)
  obtain ⟨e,he⟩ := eight_irreducible_upper_regular ρ hd
  let em : q.ker ≃* (U → Multiplicative (ZMod 2)) :=
    e.toAddEquiv.toMultiplicative.trans (MulEquiv.funMultiplicative U (ZMod 2))
  apply exists_complement_of_regular_preimage q hq U em
  · intro g v x
    change Multiplicative.ofAdd (e (Additive.ofMul (MulAut.conjNormal (g : H) v)) x) =
      Multiplicative.ofAdd (e (Additive.ofMul v) ((⟨q g,g.property⟩ : U)⁻¹*x))
    rw [← hρ]
    exact congrArg Multiplicative.ofAdd (he ⟨q g,g.property⟩ (Additive.ofMul v) x)
  · rw [U.index_comap_of_surjective hq]
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 q.ker).exists_card_eq
    rw [hn]
    exact (Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two
      (upperUnipotentSylow (GaloisField 2 3) 2).not_dvd_index).symm

end Representation.SL2.BinarySmall

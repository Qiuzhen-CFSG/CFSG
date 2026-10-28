module
public import Theory.GroupTheory.AutomorphismSquareExchangeRank
public import Theory.Representation.BinaryOffender.NormalizerRank
public import Theory.Representation.BinaryOffender.PerfectNormalizer
public import Theory.Representation.Suzuki.TensorExchangeBound
public import Theory.ElementaryAbelian.Injective
public import Theory.SpecificGroups.Suzuki.TwoRank

/-!
# Exchanged elementary actors on an irreducible Suzuki square

Schur's lemma embeds an elementary two-subgroup of the full linear
normalizer in the automorphisms of the faithful Suzuki square. An actual
factor exchange gives rank at most 2r+2. Its displacement is at least
3(2r+1), so the whole actor has fixed codimension strictly greater than
twice its rank. The involution condition follows from elementary abelianness.
The Chapter 10 application retains the original seed and marked quotient.

Source: Aschbacher--Smith D.3.7, printed pp.197--198, exchanged-actor branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Representation.Suzuki
open Representation.BinaryOffender BenderSuzuki.MatrixGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- An elementary normalizer actor containing an exchange has the source's
small rank, with no assumption on the full normalizer quotient. -/
theorem binary_square_exchange_rank_le (r : ℕ) (hr : 0 < r)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup r × SuzukiMatrixGroup r) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (a : linearNormalizer ρ) (ha : a ∈ A)
    (hswap : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
      ρ (g.2,g.1) (normalizerRepresentation ρ a v)) : rank A ≤ 2*r+2 := by
  let S := SuzukiMatrixGroup r
  let : Fact (0 < r) := ⟨hr⟩
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let e := PerfectNormalizer.imageEquiv ρ hf
  let f : linearNormalizer ρ →* MulAut (S × S) :=
    (MulAut.congr e.symm).toMonoidHom.comp (actionImage ρ).normalizerMonoidHom
  have hfi : Function.Injective (f.comp A.subtype) :=
    (MulAut.congr e.symm).injective.comp
      (normalizer_elementary_conjugation_injective ρ hi A)
  let E := (f.comp A.subtype).range
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective
    (f.comp A.subtype).rangeRestrict (f.comp A.subtype).rangeRestrict_surjective
  have hfa : f a = MulEquiv.prodComm := by
    apply MulEquiv.ext
    intro g
    apply e.injective
    apply Subtype.ext
    have he : (e (f a g)).val = a.val * (e g).val * a.val⁻¹ :=
      congrArg Subtype.val (e.apply_symm_apply _)
    rw [he]
    apply Units.ext
    apply LinearMap.ext
    intro v
    change a.val.val (ρ g ((a.val⁻¹).val v)) = ρ (g.2,g.1) v
    have hs := hswap g ((a.val⁻¹).val v)
    change a.val.val (ρ g ((a.val⁻¹).val v)) =
      ρ (g.2,g.1) (a.val.val ((a.val⁻¹).val v)) at hs
    rw [hs]
    congr 1
    change (a.val.val * (a.val⁻¹).val) v = v
    rw [←Units.val_mul,mul_inv_cancel,Units.val_one]
    rfl
  have hE : (MulEquiv.prodComm : MulAut (S × S)) ∈ E :=
    ⟨⟨a,ha⟩,hfa⟩
  have hZ : center S = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp h))
  have hb := AutomorphismSquare.abelian_exchange_rank_le hZ E hE
  have hlast := suzuki_automorphism_two_rank r hr
  change primeRank 2 (MulAut S) ≤ 2*r+1 at hlast
  let : IsElementaryAbelian 2 (⊤ : Subgroup E) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup E).subtype (Subgroup.subtype_injective _)
  have hb' : primeRank 2 E ≤ 2*r+2 := by omega
  have hc := (primeRank_le_iff_elementary_card_le E).mp hb'
    (⊤ : Subgroup E) inferInstance
  have hcard : Nat.card A = Nat.card (⊤ : Subgroup E) :=
    (Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv).trans
      (Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv).symm
  rw [←hcard] at hc
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank,Nat.log_pow (by decide : 1 < 2)] using hh
/-- A Suzuki-square elementary actor containing a factor exchange cannot
have action ratio at most two. -/
theorem binary_square_exchanged_actor_strict_bound (r : ℕ) (hr : 0 < r)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup r × SuzukiMatrixGroup r) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (a : linearNormalizer ρ) (ha : a ∈ A)
    (hswap : ∀ g v, normalizerRepresentation ρ a (ρ g v) =
      ρ (g.2,g.1) (normalizerRepresentation ρ a v)) :
    2 * rank A < fixedCodim (normalizerRepresentation ρ) A := by
  have h2 : normalizerRepresentation ρ a * normalizerRepresentation ρ a = 1 := by
    rw [←map_mul,←pow_two,elemPow_eq_one_of_isElementaryAbelian a ha,map_one]
  have hd := binary_square_exchange_displacement_ge r hr ρ hi hf
    (normalizerRepresentation ρ a) h2 hswap
  have hm := NaturalTensor.operatorFixedCodim_le_fixedCodim (normalizerRepresentation ρ) A ha
  change Module.finrank (ZMod 2) (normalizerRepresentation ρ a - 1).range ≤
    fixedCodim (normalizerRepresentation ρ) A at hm
  have hb := binary_square_exchange_rank_le r hr ρ hi hf A a ha hswap
  omega
end Representation.Suzuki

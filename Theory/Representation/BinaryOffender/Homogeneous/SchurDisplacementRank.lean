module

public import Theory.Representation.BinaryOffender.Homogeneous.SchurDisplacement
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.Quotient

/-!
# Elementary actor rank from centralizer displacements

Restrict literal conjugation on a normal subgroup H to an elementary actor X.
Its kernel is C_X(H), proved as an equality of subgroups of X. Common displacement
images and kernels embed this kernel in the endomorphisms of the marked
constituent. The kernel--image order formula then bounds the binary rank of X
by that endomorphism dimension plus the two-rank of Aut(H).

Source application: the A₆ branch of Aschbacher--Smith 14.3.15, printed p.994,
using the marked homogeneous geometry of G.10--11, printed pp.360,368--369.
The original source application discharges all displacement and faithfulness
premises in SmallRows.AlternatingSixActionSourceMultiplicityRank.
-/

public noncomputable section
open Subgroup Representation Module
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The kernel of the literal conjugation action is the centralizer inside X.
The common-displacement embedding bounds this kernel by the Schur degree. -/
theorem finrank_le_schur_add_automorphism_rank
    (ρ : Representation (ZMod 2) G V) (hfaith : Function.Injective ρ)
    (H X : Subgroup G) [H.Normal] [IsElementaryAbelian 2 X]
    (I : Subrepresentation (ρ.comp H.subtype)) (K : Submodule (ZMod 2) V)
    (hdata : ∀ c : X, (c : G) ∈ centralizer (H : Set G) → c ≠ 1 →
      LinearMap.range (ρ c - LinearMap.id) = I.toSubmodule ∧
      LinearMap.ker (ρ c - LinearMap.id) = K) :
    finrank (ZMod 2) (Additive X) ≤
      finrank (ZMod 2) (IntertwiningMap I.toRepresentation I.toRepresentation) +
        primeRank 2 (MulAut H) := by
  let C := (centralizer (H : Set G)).subgroupOf X
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective C.subtype C.subtype_injective
  let α := ρ.comp (X.subtype.comp C.subtype)
  have hα : Function.Injective α := hfaith.comp (X.subtype_injective.comp C.subtype_injective)
  have hc (c : C) (a : H) (v : V) :
      α c ((ρ.comp H.subtype) a v) = (ρ.comp H.subtype) a (α c v) := by
    change ρ ((c : X) : G) (ρ (a : G) v) = ρ (a : G) (ρ ((c : X) : G) v)
    have he : (a : G) * ((c : X) : G) = ((c : X) : G) * (a : G) :=
      mem_centralizer_iff.mp c.property a a.property
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, he]
  have hd (c : C) (hc1 : c ≠ 1) :
      LinearMap.range (α c - LinearMap.id) = I.toSubmodule ∧
      LinearMap.ker (α c - LinearMap.id) = K :=
    hdata c.val c.property (fun hh => hc1 (Subtype.ext hh))
  obtain ⟨j,hj⟩ := exists_injective_schur_displacement α (ρ.comp H.subtype) hα hc I K hd
  let s := finrank (ZMod 2) (IntertwiningMap I.toRepresentation I.toRepresentation)
  let : Finite (IntertwiningMap I.toRepresentation I.toRepresentation) :=
    Module.finite_of_finite (ZMod 2)
  have hC : Nat.card C ≤ 2^s := by
    calc
      Nat.card C = Nat.card (Additive C) := Nat.card_congr Additive.ofMul
      _ ≤ Nat.card (IntertwiningMap I.toRepresentation I.toRepresentation) :=
        Nat.card_le_card_of_injective j hj
      _ = 2^s := by
        simpa only [Nat.card_zmod] using
          Module.natCard_eq_pow_finrank (K := ZMod 2)
            (V := IntertwiningMap I.toRepresentation I.toRepresentation)
  let f : X →* MulAut H := (MulAut.conjNormal : G →* MulAut H).comp X.subtype
  have hker : f.ker = C := by
    ext x
    change (x : G) ∈ (MulAut.conjNormal : G →* MulAut H).ker ↔
      (x : G) ∈ centralizer (H : Set G)
    rw [MulAut.conjNormal_ker_eq_centralizer]
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hR : Nat.card f.range ≤ 2 ^ primeRank 2 (MulAut H) :=
    (primeRank_le_iff_elementary_card_le (MulAut H)).mp le_rfl f.range
      inferInstance
  have hcard : Nat.card X = Nat.card C * Nat.card f.range := by
    rw [← f.ker.card_mul_index, index_ker, hker]
  have hb : Nat.card X ≤ 2 ^ (s + primeRank 2 (MulAut H)) := by
    rw [hcard,pow_add]
    exact Nat.mul_le_mul hC hR
  have hx : Nat.card X = 2 ^ finrank (ZMod 2) (Additive X) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X)
  rw [hx] at hb
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hb
end Representation.BinaryOffender

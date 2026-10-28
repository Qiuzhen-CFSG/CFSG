module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.SourceMarking

/-!
# The three-part of the simple marked residual

In the genuine four-dimensional binary A₆ action, the normalizer of a
marked subgroup of order two maps onto its binary point stabilizer, whose
order is 24. The kernel is a subgroup of O₂(L). Passing to the two-residual
preserves the three-part. Removing the normalizing two-group T identifies
this residual with the literal L₁ = O²(N_{LT}(V₁)). Thus |L₁|₃ = 3.

Source: Aschbacher–Smith, proof of 13.8.5, printed p.947 (PDF p.964),
with Notation 13.2.1 and the natural action of 13.5.2(3). Only the intrinsic
source marking and residual-transport results of SourceMarking are used;
no later component conclusion is invoked.
-/

open Subgroup Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor

private theorem threeVal_twoGroup {A : Type*} [Group A] [Finite A]
    (h : IsPGroup 2 A) : (Nat.card A).factorization 3 = 0 := by
  obtain ⟨n, hn⟩ := h.exists_card_eq
  rw [hn, Nat.factorization_pow, Nat.prime_two.factorization]
  simp

private theorem threeVal_of_surjective {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] (f : A →* B) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) :
    (Nat.card A).factorization 3 = (Nat.card B).factorization 3 := by
  have h := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h
  rw [h, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
  simp only [Finsupp.add_apply, threeVal_twoGroup hk, add_zero]

private theorem threeVal_residual {A : Type*} [Group A] [Finite A] :
    (Nat.card (pResidual 2 A)).factorization 3 = (Nat.card A).factorization 3 := by
  have h := card_eq_card_quotient_mul_card_subgroup (pResidual 2 A)
  rw [h, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
  simp [threeVal_twoGroup (isPGroup_quotient_pResidual (G := A) 2)]

private noncomputable def binaryPointEquiv (x : BinaryPoint) :
    MulAction.stabilizer A6 x ≃* a6DuadStabilizer := by
  have he : MulAction.stabilizer A6 x =
      MulAction.stabilizer A6 (duadPolarEquiv.symm x) := by
    ext g
    change g.val • x = x ↔ g.val • duadPolarEquiv.symm x = duadPolarEquiv.symm x
    rw [← duadPolarEquiv.injective.eq_iff, duadPolarEquiv_equivariant]
    simp
  have hg := Classical.choose_spec (a6_duad_transitive 0 (duadPolarEquiv.symm x))
  exact (MulEquiv.subgroupCongr he).trans
    ((MulAction.stabilizerEquivStabilizer hg.symm).symm.trans
      (MulEquiv.subgroupCongr a6_duad_stabilizer_zero))

private theorem normalizes_two_iff {G : Type*} [Group G] (U : Subgroup G)
    (hc : Nat.card U = 2) (z : U) (hz : z ≠ 1) (g : G) :
    g ∈ normalizer (U : Set G) ↔ g * z.val * g⁻¹ = z.val := by
  have hu := (Nat.card_eq_two_iff' (1 : U)).mp hc
  constructor
  · intro hg
    have hne := (U.normalizerMonoidHom ⟨g, hg⟩).map_ne_one_iff.mpr hz
    exact congrArg Subtype.val (hu.unique hne hz)
  · intro hg
    apply centralizer_le_normalizer _
    intro u hu'
    by_cases he : (⟨u, hu'⟩ : U) = 1
    · have : u = 1 := congrArg Subtype.val he
      simp [this]
    · have : u = z.val := congrArg Subtype.val (hu.unique he hz)
      rw [this]
      exact (mul_inv_eq_iff_eq_mul.mp hg).symm

/-- The marked residual has three-part three and no prime divisor other than two and three. -/
public theorem simple_marked_order_data {G : Type*} [Group G] [Finite G] (L T V V₁ : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : SimplePointModel L V hLV)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (L : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) :
    (Nat.card (markedResidual L T V₁)).factorization 3 = 1 ∧
      ∃ n : ℕ, Nat.card (markedResidual L T V₁) ∣ 3 * 2 ^ n := by
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp hc
  let x : BinaryPoint := ⟨Multiplicative.toAdd (d.moduleEquiv (inclusion hV₁V z)),
    d.moduleEquiv.map_ne_one_iff.mpr (fun he => hz (Subtype.ext
      (congrArg (fun v : V => (v : G)) he)))⟩
  let q : L →* A6 := d.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let P := (normalizer (V₁ : Set G)).subgroupOf L
  have hmem (l : L) : q l ∈ MulAction.stabilizer A6 x ↔ l.val ∈ normalizer (V₁ : Set G) := by
    rw [normalizes_two_iff V₁ hc z hz]
    change (q l).val • x = x ↔ _
    rw [Subtype.ext_iff]
    change (polarPointPerm (q l).val x).val = _ ↔ _
    rw [← polarAction_point]
    change polarAction (d.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)).val
        (Multiplicative.toAdd (d.moduleEquiv (inclusion hV₁V z))) = _ ↔ _
    rw [← d.equivariant]
    change d.moduleEquiv (V.normalizerMonoidHom (inclusion hLV l) (inclusion hV₁V z)) =
      d.moduleEquiv (inclusion hV₁V z) ↔ _
    rw [d.moduleEquiv.injective.eq_iff, Subtype.ext_iff]
    rfl
  let f : P →* MulAction.stabilizer A6 x :=
    (q.comp P.subtype).codRestrict _ (fun l => (hmem l.val).mpr
      (show l.val.val ∈ normalizer (V₁ : Set G) from l.property))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨l, hl⟩ := (d.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)) y.val
    change q l = y.val at hl
    refine ⟨⟨l, (hmem l).mp (hl.symm ▸ y.property)⟩, ?_⟩
    exact Subtype.ext hl
  have hk : f.ker = (pCore 2 L).comap P.subtype := by
    dsimp only [f]
    erw [MonoidHom.ker_codRestrict]
    ext l
    change d.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l.val) = 1 ↔ _
    rw [d.quotientEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  have hp : (Nat.card P).factorization 3 = 1 := by
    rw [threeVal_of_surjective f hf (by
      rw [hk]; exact pCore_isPGroup.comap_of_injective _ P.subtype_injective)]
    rw [Nat.card_congr (binaryPointEquiv x).toEquiv, a6DuadStabilizer_card]
    rw [show (24 : ℕ) = 2 ^ 3 * 3 from rfl,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow,
      Nat.prime_two.factorization, Nat.prime_three.factorization]
    simp
  have hr : (pResidual 2 P).map (L.subtype.comp P.subtype) = markedResidual L T V₁ := by
    rw [← map_map, map_embedded_pResidual, subgroupOf_map_subtype, inf_comm,
      SourceMarking.residual_eq_left L T V₁ hT hn]
  have hi : Function.Injective (L.subtype.comp P.subtype) :=
    L.subtype_injective.comp P.subtype_injective
  have hcard : Nat.card (markedResidual L T V₁) = Nat.card (pResidual 2 P) := by
    rw [← hr]
    exact (Nat.card_congr ((pResidual 2 P).equivMapOfInjective _ hi).toEquiv).symm
  constructor
  · rw [hcard, threeVal_residual, hp]
  · have hk2 : IsPGroup 2 f.ker := by
      rw [hk]
      exact pCore_isPGroup.comap_of_injective _ P.subtype_injective
    obtain ⟨n, hn⟩ := hk2.exists_card_eq
    have hPcard := card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      Nat.card_congr (binaryPointEquiv x).toEquiv, a6DuadStabilizer_card, hn] at hPcard
    refine ⟨n + 3, ?_⟩
    rw [hcard]
    have hd := (pResidual 2 P).card_subgroup_dvd_card
    rw [hPcard] at hd
    convert hd using 1
    ring


/-- The three-adic valuation of the literal source L₁ is one in the simple case. -/
public theorem simple_marked_threeVal {G : Type*} [Group G] [Finite G]
    (L T V V₁ : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : SimplePointModel L V hLV)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (L : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) :
    (Nat.card (markedResidual L T V₁)).factorization 3 = 1 :=
  (simple_marked_order_data L T V V₁ hLV d hT hn hV₁V hc).1

/-- The literal three-part, rather than only a three-rank bound. -/
public theorem simple_marked_threePart {G : Type*} [Group G] [Finite G]
    (L T V V₁ : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : SimplePointModel L V hLV)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (L : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) :
    3 ^ (Nat.card (markedResidual L T V₁)).factorization 3 = 3 := by
  rw [simple_marked_threeVal L T V V₁ hLV d hT hn hV₁V hc, pow_one]

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor

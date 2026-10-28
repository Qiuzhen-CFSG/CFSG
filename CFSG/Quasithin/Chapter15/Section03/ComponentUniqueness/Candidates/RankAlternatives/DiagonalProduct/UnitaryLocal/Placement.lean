module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.CoreRemoval
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank.Intersection
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting.Transport
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Placement of the unitary actor in the local Borel

The proper subgroup M ∩ L contains the actual Sylow intersection S ∩ L.
Its image under L → L/O₂(L) → PSU₃ is therefore contained in the unique
proper Sylow overgroup. The actor preserves M ∩ L, so uniqueness forces
it to preserve this same Borel. S-invariance alone is not used as a
placement criterion.

The rank argument of 15.3.12 makes O²(Y₊ ∩ L) nontrivial. Since
Y₊/O₂(Y₊) is a three-group, Y₊ ∩ L contains an element of order three.
The quotient map has two-group kernel, so this element survives in the
Borel. Finally compatible conjugation by an order-three actor cubes to
the identity on the actual quotient.

`CubicBorelAction` specifies the remaining concrete matrix lemma. It is
an output to prove, not a local hypothesis attributed to the book.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.11(1),(5),(6), 15.3.12(1), and the final paragraph of 15.3.37,
printed pp.1123--1125 and 1135; rank-one Borel geometry is F.1.3(1).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.UnitaryLocal

/-- The remaining matrix assertion: a unitary conjugation of exponent dividing
three preserving a PSU₃ Borel with nontrivial three-part is inner. The matrix
field, Frobenius involution and literal unitary action are all specified. -/
def CubicBorelAction (n : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F),
    Nat.card F = (2 ^ n) ^ 2 → (∀ x, J.conj x = x ^ (2 ^ n)) →
    let U := BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J
    ∀ (T : Sylow 2 U) (d : J.unitarySubgroup),
      let B := normalizer (T : Set U)
      3 ∣ Nat.card B →
      (J.unitaryConjHom d) ^ 3 = 1 →
      B.map (J.unitaryConjHom d).toMonoidHom = B →
      J.unitaryConjHom d ∈ MulAut.innerSubgroup U

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

private theorem map_eq_self_of_le (A : Subgroup H) (β : MulAut H)
    (h : A.map β.toMonoidHom ≤ A) : A.map β.toMonoidHom = A :=
  eq_of_le_of_card_ge h (card_map_of_injective β.injective).ge

/-- Borel uniqueness promotes invariance of a proper Sylow overgroup to
invariance of the Borel. -/
theorem borel_preserved (T : Sylow 2 H) (hT : RankOneSylowFacts T)
    (A : Subgroup H) (hTA : (T : Subgroup H) ≤ A) (hA : A < ⊤)
    (β : MulAut H) (hβ : A.map β.toMonoidHom = A) :
    (normalizer (T : Set H)).map β.toMonoidHom = normalizer (T : Set H) := by
  have hAB := hT.unique_maximal A hTA hA
  apply map_eq_self_of_le
  apply hT.unique_maximal
  · exact hTA.trans (hβ ▸ map_mono (f := β.toMonoidHom) hAB)
  · apply lt_top_iff_ne_top.mpr
    intro he
    apply hT.proper.ne
    apply map_injective (f := β.toMonoidHom) β.injective
    simpa only [map_top_of_surjective β.toMonoidHom β.surjective] using he

omit [Finite H] [Finite G] in
/-- An actual order-three actor induces an automorphism whose cube is one. -/
theorem compatible_cube {L : Subgroup G} {y : G}
    (α : MulAut L) (β : MulAut H) (f : L →* H) (hf : Function.Surjective f)
    (hc : ConjugationOn L y α) (hy : orderOf y = 3)
    (he : ∀ x : L, f (α x) = β (f x)) : β ^ 3 = 1 := by
  ext z
  obtain ⟨x, rfl⟩ := hf z
  change β (β (β (f x))) = f x
  rw [← he, ← he, ← he]
  apply congrArg f
  apply Subtype.ext
  calc
    ((α (α (α x)) : L) : G) = y ^ 3 * (x : G) * (y ^ 3)⁻¹ := by
      rw [hc, hc, hc]
      simp only [pow_succ, pow_zero]
      group
    _ = x := by rw [← hy, pow_orderOf_eq_one]; simp

omit [Finite H] in
/-- The nontrivial intersection residual forces a factor of three upstairs. -/
theorem intersection_has_three {Y L : Subgroup G}
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hne : componentPart Y L ≠ ⊥) : 3 ∣ Nat.card (Y ⊓ L : Subgroup G) := by
  by_contra hthree
  let D := (Y ⊓ L).subgroupOf Y
  let q := QuotientGroup.mk' (pCore 2 Y)
  have hp : IsPGroup 3 (D.map q) := hY.to_subgroup _
  have hc : Nat.card (D.map q) = 1 := hp.card_eq_or_dvd.resolve_right (by
    intro hd
    apply hthree
    have hD : Nat.card D = Nat.card (Y ⊓ L : Subgroup G) :=
      Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [← hD]
    exact hd.trans (D.card_map_dvd q))
  have hb : D.map q = ⊥ := card_eq_one.mp hc
  have hD : D ≤ pCore 2 Y := by
    simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hb
  have hpD : IsPGroup 2 D := pCore_isPGroup.to_le hD
  have hpI : IsPGroup 2 (Y ⊓ L : Subgroup G) :=
    hpD.of_equiv (subgroupOfEquivOfLe inf_le_left)
  exact hne ((ComponentIntersection.intersectionResidual_eq_bot_iff Y L).mpr hpI)

omit [Finite H] in
/-- Restrict the given local Sylow to the relatively subnormal component. -/
theorem component_sylow {I L S : Subgroup G} (hLI : L ≤ I)
    (hL : (L.subgroupOf I).IsSubnormal) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = S) :
    ∃ T : Sylow 2 L, (T : Subgroup L) = S.subgroupOf L := by
  obtain ⟨T, hT⟩ := P.exists_subgroupOf_eq_of_subnormal (L.subgroupOf I) hL
  let e := subgroupOfEquivOfLe hLI
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (T : Subgroup (L.subgroupOf I)).map e.toMonoidHom = _
  rw [hT, ← hP]
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.val, ha, rfl⟩
  · rintro ⟨a, ha, he⟩
    refine ⟨⟨a, ?_⟩, ha, ?_⟩
    · change (a : G) ∈ L
      change (a : G) = (x : G) at he
      rw [he]
      exact x.property
    · exact Subtype.ext he

omit [Finite H] in
private theorem intersection_preserved {M L : Subgroup G} {y : G}
    (hy : y ∈ M) (α : MulAut L) (hc : ConjugationOn L y α) :
    (M.subgroupOf L).map α.toMonoidHom = M.subgroupOf L := by
  apply map_eq_self_of_le
  rintro _ ⟨x, hx, rfl⟩
  change (α x : G) ∈ M
  rw [hc]
  exact M.mul_mem (M.mul_mem hy hx) (M.inv_mem hy)

/-- The actual quotient Borel has order divisible by three and is preserved
by the compatible actor. The kernel is precisely O₂(L). -/
theorem local_borel_data {M L S Y : Subgroup G} {y : G}
    (hSM : S ≤ M) (hYM : Y ≤ M) (hy : y ∈ Y) (hLM : ¬ L ≤ M)
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y)) (hne : componentPart Y L ≠ ⊥)
    (T : Sylow 2 L) (hT : (T : Subgroup L) = S.subgroupOf L)
    (α : MulAut L) (β : MulAut H) (f : L →* H)
    (hf : Function.Surjective f) (hker : f.ker = pCore 2 L)
    (hc : ConjugationOn L y α) (he : ∀ x : L, f (α x) = β (f x))
    (hB : RankOneSylowFacts (T.mapSurjective hf)) :
    let B := normalizer ((T.mapSurjective hf) : Set H)
    3 ∣ Nat.card B ∧ B.map β.toMonoidHom = B := by
  let A := M.subgroupOf L
  let A' := A.map f
  have hTA : (T : Subgroup L) ≤ A := by
    rw [hT]
    exact comap_mono hSM
  have hkA : f.ker ≤ A := by
    rw [hker]
    exact (pCore_isPGroup.le_sylow_of_normal T).trans hTA
  have hA : A < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro ht
    apply hLM
    intro x hx
    exact (show (⟨x, hx⟩ : L) ∈ A from ht ▸ mem_top _)
  have hA' : A' < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro ht
    apply hA.ne
    change A.map f = ⊤ at ht
    rw [← comap_map_eq_self hkA, ht, comap_top]
  have hTA' : ((T.mapSurjective hf) : Subgroup H) ≤ A' := map_mono hTA
  have hAB := hB.unique_maximal A' hTA' hA'
  have hAf : A'.map β.toMonoidHom = A' := by
    have hef : β.toMonoidHom.comp f = f.comp α.toMonoidHom := by
      ext x
      exact (he x).symm
    change (A.map f).map β.toMonoidHom = A.map f
    rw [map_map, hef, ← map_map, intersection_preserved (hYM hy) α hc]
  refine ⟨?_, borel_preserved _ hB A' hTA' hA' β hAf⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (Y ⊓ L : Subgroup G)) 3
    (intersection_has_three hY hne)
  let l : L := ⟨x, x.property.2⟩
  have hl : orderOf l = 3 := by
    rw [← orderOf_injective L.subtype L.subtype_injective l]
    exact (orderOf_injective (Y ⊓ L).subtype (Y ⊓ L).subtype_injective x).trans hx
  have hfl : orderOf (f l) = 3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker
      (hker ▸ pCore_isPGroup) l (by rw [hl]; decide)).trans hl
  have hlB : f l ∈ normalizer ((T.mapSurjective hf) : Set H) :=
    hAB (mem_map_of_mem f (hYM x.property.1))
  have hh := orderOf_dvd_natCard (⟨f l, hlB⟩ : normalizer ((T.mapSurjective hf) : Set H))
  rw [← orderOf_injective (normalizer ((T.mapSurjective hf) : Set H)).subtype
    (normalizer ((T.mapSurjective hf) : Set H)).subtype_injective] at hh
  change orderOf (f l) ∣ _ at hh
  rwa [hfl] at hh

end CFSG.Quasithin.Chapter15.Section03.Candidates.UnitaryLocal

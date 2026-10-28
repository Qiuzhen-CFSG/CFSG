module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.ActionInterface
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.LocalReduction
public import Theory.GroupTheory.ComponentLocalPrimeFree
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# Invariance of the Suzuki orbit normalizer

Put L₀ = ⟨L^S⟩ and B = N_{L₀}(S ∩ L₀), with all subgroups embedded in
G. Since S normalizes Y and Y normalizes L, Y normalizes every S-conjugate
of L. The component--Sylow join has order prime to three. Hence Y ∩ L₀
lies in O₂(Y), which is contained in S by Sylow maximality. This puts
[Y, S ∩ L₀] in S ∩ L₀, so YS normalizes the concrete candidate B.

These statements establish the normalization part of the construction.
The marked Suzuki product, characteristic-two property, and invariant
maximality are separate obligations; none is assumed or asserted here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
15.3.34, printed p.1134, and the component calculus of 1.2/A.3.
-/

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped commutatorElement

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion.BorelConstruction
variable {G : Type*} [Group G]

private theorem span_normalized {L S Y : Subgroup G}
    (hSY : S ≤ normalizer (Y : Set G)) (hYL : Y ≤ normalizer (L : Set G)) :
    Y ≤ normalizer (localSpan L S : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro y hy x ⟨s, hs, l, hl, rfl⟩
  have hy' : s⁻¹ * y * s ∈ Y := by
    simpa only [inv_inv] using le_normalizer_iff.mp hSY s⁻¹ (S.inv_mem hs) y hy
  have hl' := le_normalizer_iff.mp hYL _ hy' l hl
  apply Subgroup.subset_closure
  refine ⟨s, hs, (s⁻¹ * y * s) * l * (s⁻¹ * y * s)⁻¹, hl', ?_⟩
  group

private theorem normalized_two_subgroup_le {I S R : Subgroup G}
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hRI : R ≤ I) (hp : IsPGroup 2 R) (hn : S ≤ normalizer (R : Set G)) : R ≤ S := by
  have h : R.subgroupOf I ≤ (P : Subgroup I) := by
    apply hp.comap_subtype.le_sylow_of_normalized P
    change (P : Subgroup I) ≤ normalizer (R.subgroupOf I : Set I)
    rw [← subgroupOf_normalizer_eq hRI]
    intro s hs
    exact hn (hP ▸ mem_map_of_mem I.subtype hs)
  simpa only [map_subgroupOf_eq_of_le hRI, hP] using
    map_mono (f := I.subtype) h

private theorem twoCore_le {I S Y : Subgroup G}
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hYI : Y ≤ I) (hSY : S ≤ normalizer (Y : Set G)) : Y.pCoreIn 2 ≤ S := by
  exact normalized_two_subgroup_le P hP ((pCoreIn_le 2 Y).trans hYI)
    (isPGroup_pCoreIn 2 Y)
    (hSY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)))

private theorem intersection_normalized {I S Y H : Subgroup G}
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hYI : Y ≤ I) (hSY : S ≤ normalizer (Y : Set G))
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hH : ¬ 3 ∣ Nat.card H) (hYH : Y ≤ normalizer (H : Set G)) :
    Y ≤ normalizer ((S ⊓ H : Subgroup G) : Set G) := by
  have hcY : ⁅Y, S ⊓ H⁆ ≤ Y :=
    le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hSY)
  have hcH : ⁅Y, S ⊓ H⁆ ≤ H :=
    (commutator_mono le_rfl inf_le_right).trans
      (le_normalizer_iff_commutator_le_right.mp hYH)
  have hI : Y ⊓ H ≤ Y.pCoreIn 2 := le_twoCore_of_three_free inf_le_left hY
    (fun hd => hH (hd.trans (card_dvd_of_le inf_le_right)))
  apply le_normalizer_iff_commutator_le_right.mpr
  exact le_inf ((le_inf hcY hcH).trans (hI.trans (twoCore_le P hP hYI hSY))) hcH

/-- The concrete candidate for the source Borel: the relative normalizer
of the Sylow intersection in the literal component orbit. -/
def orbitNormalizer (L S : Subgroup G) : Subgroup G :=
  localSpan L S ⊓ normalizer ((S ⊓ localSpan L S : Subgroup G) : Set G)

/-- The candidate lies inside the component orbit. -/
theorem orbitNormalizer_le (L S : Subgroup G) :
    orbitNormalizer L S ≤ localSpan L S := inf_le_left

/-- The candidate contains the Sylow intersection. -/
theorem sylow_intersection_le_orbitNormalizer (L S : Subgroup G) :
    S ⊓ localSpan L S ≤ orbitNormalizer L S :=
  le_inf inf_le_right (S ⊓ localSpan L S).le_normalizer

variable [Finite G]

/-- The entire component orbit has order prime to three. Its containing
component--Sylow join is three-free even if the Sylow subgroup moves L. -/
theorem localSpan_three_free {I L S : Subgroup G} (hLI : L ≤ I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hL : IsComponent I (L.subgroupOf I)) (m : ℕ) (hm : 0 < m)
    (e : L ≃* SuzukiMatrixGroup m) : ¬ 3 ∣ Nat.card (localSpan L S) := by
  have hLc : ¬ 3 ∣ Nat.card (L.subgroupOf I) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hLI).toEquiv, Nat.card_congr e.toEquiv]
    exact suzukiMatrixGroup_three_free m hm
  have hPc : ¬ 3 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hsup := hL.not_dvd_card_local_adjoin Nat.prime_three
    (K := L.subgroupOf I) (A := (P : Subgroup I)) le_rfl inf_le_right hLc hPc
  have he : ((L.subgroupOf I) ⊔ (P : Subgroup I)).map I.subtype = L ⊔ S := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLI, hP]
  have hamb : ¬ 3 ∣ Nat.card (L ⊔ S : Subgroup G) := by
    rw [← he, card_map_of_injective I.subtype_injective]
    exact hsup
  exact fun hd => hamb (hd.trans (card_dvd_of_le
    (conjugateSpanBy_le le_sup_left (le_sup_right.trans (L ⊔ S).le_normalizer))))

omit [Finite G] in
private theorem normalizes_normalizer {A U : Subgroup G} (h : A ≤ normalizer (U : Set G)) :
    A ≤ normalizer (normalizer (U : Set G) : Set G) :=
  h.trans (normalizer (U : Set G)).le_normalizer

/-- The two-by-three actor and the Sylow subgroup both preserve the
candidate. No normalization of the original component by S is needed. -/
theorem orbitNormalizer_invariant {I L S Y : Subgroup G} (hLI : L ≤ I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hL : IsComponent I (L.subgroupOf I)) (m : ℕ) (hm : 0 < m)
    (e : L ≃* SuzukiMatrixGroup m) (hYI : Y ≤ I)
    (hSY : S ≤ normalizer (Y : Set G)) (hY : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hYL : Y ≤ normalizer (L : Set G)) :
    Y ≤ normalizer (localSpan L S : Set G) ∧
      Y ⊔ S ≤ normalizer (orbitNormalizer L S : Set G) := by
  have hY0 := span_normalized hSY hYL
  have hS0 := le_normalizer_conjugateSpanBy L S
  have hYQ := intersection_normalized P hP hYI hSY hY
    (localSpan_three_free hLI P hP hL m hm e) hY0
  have hSQ := le_normalizer_inf S.le_normalizer hS0
  exact ⟨hY0, le_normalizer_inf (sup_le hY0 hS0)
    (normalizes_normalizer (sup_le hYQ hSQ))⟩

omit [Finite G] in
/-- Intrinsically the candidate is precisely the normalizer of the
restricted Sylow subgroup, rather than an ambient normalizer. -/
theorem orbitNormalizer_subgroupOf (L S : Subgroup G) :
    (orbitNormalizer L S).subgroupOf (localSpan L S) =
      normalizer (S.subgroupOf (localSpan L S) : Set (localSpan L S)) := by
  rw [orbitNormalizer, inf_subgroupOf_left]
  rw [subgroupOf_normalizer_eq inf_le_right, inf_subgroupOf_right]

end CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion.BorelConstruction

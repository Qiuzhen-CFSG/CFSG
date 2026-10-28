module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.FourGroupGeneration.EscapeInput
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.FourGroupGeneration.Escape
public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
import Mathlib.Tactic

/-!
# Two-conjugate four-group generation for the four small prime parameters

The maximal dihedral pair and involution fusion prove the inner branch.
For a diagonal actor, the actual prime-field outer quotient supplies an inner
involution. Fuse it to both generators of the maximal dihedral subgroup D,
and apply the explicit normalizer-escape input while fixing the second
generator. If the generated group met Inn(PSL₂) in D, it would normalize D,
contradicting escape. Maximality therefore forces the full inner group.

The proved normalizer escape discharges the diagonal input in the final
unconditional assembly. Both branches use conjugators in PSL₂ itself, as
required by the degree-eight consumer's central-cover transport.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.1,
manuscript pp.8--9; Aschbacher--Smith K.2, printed p.453.
-/

public section
open Subgroup GorensteinWalter Theory.PSL2
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight

/-- The inner-actor branch, with the literal automorphism subgroups and PSL₂ conjugators. -/
theorem fourGroup_inner_generation (F : Type) [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    (hF : Nat.card F = p) (A : Subgroup (MulAut PSL(2, F))) (hcard : Nat.card A = 4)
    (hinner : A ≤ (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F)).range) :
    ∃ c : Fin 2 → PSL(2, F), (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F)).range ≤
      ⨆ i, A.map (MulAut.conj (MulAut.conj (c i))).toMonoidHom := by
  let V := A.comap (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F))
  have hinj := Theory.GroupTheory.conj_injective_of_center_eq_bot (psl2_center_eq_bot F)
  have hmap : V.map (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F)) = A :=
    map_comap_eq_self hinner
  have hV : Nat.card V = 4 := by
    rw [← hcard, ← hmap, card_map_of_injective hinj]
  obtain ⟨c, hc⟩ := Theory.PSL2.SmallPrimeFourGroup.exists_two_conjugates hp hF V hV
  have hm := congrArg (Subgroup.map (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F))) hc
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map] at hm
  have he (i : Fin 2) :
      (V.map (MulAut.conj (c i)).toMonoidHom).map
        (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F)) =
      A.map (MulAut.conj (MulAut.conj (c i))).toMonoidHom := by
    rw [map_map, ← hmap, map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  simp only [he] at hm
  exact ⟨c, hm.ge⟩

/-- Normalizer escape discharges the diagonal-actor branch at a fixed parameter. -/
theorem fourGroup_generation_of_escape (F : Type) [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    (hF : Nat.card F = p) (hescape : FourGroupNormalizerEscape F p) :
    ActorGeneration PSL(2, F) 4 2 := by
  intro A hA hcard
  by_cases hinner : A ≤ (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F)).range
  · exact fourGroup_inner_generation F hp hF A hcard hinner
  have hodd : Odd p := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hlarge : 3 < p := by rcases hp with rfl | rfl | rfl | rfl <;> omega
  let I := (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F)).range
  let : I.Normal := I.normal_of_index_eq_two (prime_card_inner_index F hodd hlarge hF)
  let k (g : PSL(2, F)) := MulAut.conj (MulAut.conj g)
  have k_inner (g y : PSL(2, F)) : k g (MulAut.conj y) = MulAut.conj (g * y * g⁻¹) := by
    simp only [k, MulAut.conj_apply, map_mul, map_inv]
  obtain ⟨t, ht, ht2, htA⟩ := fourGroup_has_inner_involution F hodd hlarge hF A hA hcard
  obtain ⟨a, b, ha, ha2, hb, hb2, hmax, hDcard⟩ :=
    Theory.PSL2.SmallPrimeFourGroup.exists_maximal_pair hp hF
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp (Theory.PSL2.involutions_isConj t a
    (orderOf_eq_prime ht2 ht) (orderOf_eq_prime ha2 ha))
  obtain ⟨g₁, hg₁⟩ := isConj_iff.mp (Theory.PSL2.involutions_isConj t b
    (orderOf_eq_prime ht2 ht) (orderOf_eq_prime hb2 hb))
  let B := A.map (k g₁).toMonoidHom
  have hbB : MulAut.conj b ∈ B := by
    exact mem_map.mpr ⟨MulAut.conj t, htA, by simp only [MulEquiv.coe_toMonoidHom, k_inner, hg₁]⟩
  have hBout : ¬ B ≤ I := by
    intro hBI
    apply hinner
    intro u hu
    have hv := hBI (mem_map.mpr ⟨u, hu, rfl⟩)
    have hw := (inferInstance : I.Normal).conj_mem _ hv (MulAut.conj g₁)⁻¹
    have he : (MulAut.conj g₁)⁻¹ * (k g₁ u) * ((MulAut.conj g₁)⁻¹)⁻¹ = u := by
      change (MulAut.conj g₁)⁻¹ * (MulAut.conj g₁ * u * (MulAut.conj g₁)⁻¹) *
        ((MulAut.conj g₁)⁻¹)⁻¹ = u
      group
    exact he ▸ hw
  let : IsElementaryAbelian 2 A := hA
  have hBE : IsElementaryAbelian 2 B := IsElementaryAbelian.map (k g₁).toMonoidHom
  have hBc : Nat.card B = 4 := (card_map_of_injective (k g₁).injective).trans hcard
  obtain ⟨x, hxb, hx⟩ := hescape a b ha ha2 hb hb2 hmax hDcard B hBE hBc hBout hbB
  have hmaps : B.map (k x).toMonoidHom = A.map (k (x * g₁)).toMonoidHom := by
    dsimp [B]
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro u
    simp only [MonoidHom.comp_apply, k, map_mul]
    rfl
  let c : Fin 2 → PSL(2, F) := ![g₀, x * g₁]
  let H := ⨆ i, A.map (k (c i)).toMonoidHom
  have hA0 : A.map (k g₀).toMonoidHom ≤ H := by
    simpa only [c, Matrix.cons_val_zero] using
      le_iSup (fun i => A.map (k (c i)).toMonoidHom) 0
  have hBx : B.map (k x).toMonoidHom ≤ H := by
    rw [hmaps]
    simpa only [c, Matrix.cons_val_one, Matrix.cons_val_zero] using
      le_iSup (fun i => A.map (k (c i)).toMonoidHom) 1
  have haH : MulAut.conj a ∈ H := hA0 (mem_map.mpr
    ⟨MulAut.conj t, htA, by simp only [MulEquiv.coe_toMonoidHom, k_inner, hg₀]⟩)
  have hbH : MulAut.conj b ∈ H := hBx (mem_map.mpr
    ⟨MulAut.conj b, hbB, by simp only [MulEquiv.coe_toMonoidHom, k_inner, hxb]⟩)
  have hle : closure ({a, b} : Set PSL(2, F)) ≤ H.comap MulAut.conj :=
    (closure_le _).mpr (by
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨haH, hbH⟩)
  have hne : closure ({a, b} : Set PSL(2, F)) ≠ H.comap MulAut.conj := by
    intro heq
    apply hx
    apply hBx.trans
    rw [heq, map_comap_eq]
    exact normal_subgroupOf_iff_le_normalizer_inf.mp inferInstance
  have htop : H.comap MulAut.conj = ⊤ := hmax.lt_iff.mp (lt_of_le_of_ne hle hne)
  refine ⟨c, ?_⟩
  rintro u ⟨s, rfl⟩
  change s ∈ H.comap MulAut.conj
  rw [htop]
  trivial

/-- Conditional assembly of the precise model contract. The independent diagonal
normalizer-escape input must still be supplied. -/
theorem fourGroupModelGeneration_of_normalizer_escape
    (hescape : ∀ (F : Type) [Field F] [Finite F] (p : ℕ),
      (p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23) → Nat.card F = p →
      FourGroupNormalizerEscape F p) : FourGroupModelGeneration := by
  intro F _ _ p hp hF
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  exact fourGroup_generation_of_escape F hp hF (hescape F p hp hF)

/-- For q = 13, 17, 19, 23, two PSL₂-conjugates of every elementary
four-group in Aut(PSL₂(q)) generate a subgroup containing the full inner
group. This includes four-groups with diagonal outer automorphisms. -/
theorem fourGroupModelGeneration : FourGroupModelGeneration :=
  fourGroupModelGeneration_of_normalizer_escape fourGroupNormalizerEscape


end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight

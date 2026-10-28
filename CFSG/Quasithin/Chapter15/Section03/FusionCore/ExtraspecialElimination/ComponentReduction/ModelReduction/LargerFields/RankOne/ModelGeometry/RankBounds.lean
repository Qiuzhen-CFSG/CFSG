module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry.CentralProduct
public import Mathlib.Data.Nat.GCD.BigOperators
/-!
# Field parity and the rank of every actual factor Borel

Odd field degree makes all factor Sylow normalizers prime to three. The
product normalizer embeds in their direct product, and its surjective
image is the ambient normalizer. A cubic in C contradicts this, so the
field degree is even. Each individual factor normalizer embeds into the
ambient normalizer even in a central product. Its cubic theta subgroup
therefore has rank at most one.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49 after (k), printed p.1144.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry

variable {D E : Type*} [Group D] [Group E]

/-- The normalizer interface is invariant under actual multiplicative equivalence. -/
theorem NormalizerData.of_equiv [Finite D] {n r : ℕ} (e : D ≃* E) (h : NormalizerData E n r) :
    NormalizerData D n r := by
  let : Finite E := Finite.of_surjective e e.surjective
  have hn (S : Sylow 2 D) : (normalizer (S : Set D)).map e.toMonoidHom =
      normalizer (S.map e.toMonoidHom : Set E) :=
    map_normalizer_eq_of_bijective (S : Subgroup D) e.bijective
  let ne (S : Sylow 2 D) : normalizer (S : Set D) ≃*
      normalizer (S.map e.toMonoidHom : Set E) :=
    ((normalizer (S : Set D)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (hn S))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S H hH hSH
    let _ := hH
    have hm := h.solvable_overgroups (S.mapSurjective e.surjective) (H.map e.toMonoidHom)
      (Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H))
      (map_mono hSH)
    change H.map e.toMonoidHom ≤ normalizer (S.map e.toMonoidHom : Set E) at hm
    rw [← hn S] at hm
    exact (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp hm
  · intro S
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [map_commutator, hn S]
    exact h.commutator_le (S.mapSurjective e.surjective)
  · intro ho S
    rw [Nat.card_congr (ne S).toEquiv]
    exact h.odd ho (S.mapSurjective e.surjective)
  · intro he S
    have ht : (theta (normalizer (S : Set D))).map e.toMonoidHom =
        theta (normalizer (S.map e.toMonoidHom : Set E)) := by
      rw [theta_map_of_injective e.toMonoidHom e.injective, hn S]
    let te := ((theta (normalizer (S : Set D))).equivMapOfInjective
      e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr ht)
    rw [Theory.GroupTheory.primeRank_equiv 3 te]
    exact h.rank he (S.mapSurjective e.surjective)

section Product
variable {ι : Type*} [Fintype ι] (K : ι → Type*)
    [∀ i, Group (K i)] [∀ i, Finite (K i)]

/-- Absence of the prime three in the factor normalizers passes to the product. -/
private theorem product_normalizer_three_free
    (hK : ∀ i, ∀ P : Sylow 2 (K i), ¬ 3 ∣ Nat.card (normalizer (P : Set (K i))))
    (P : Sylow 2 (∀ i, K i)) : ¬ 3 ∣ Nat.card (normalizer (P : Set (∀ i, K i))) := by
  let Q (i : ι) : Sylow 2 (K i) :=
    P.mapSurjective (f := Pi.evalMonoidHom K i) (Function.surjective_eval i)
  let N (i : ι) := normalizer (Q i : Set (K i))
  let f (i : ι) : normalizer (P : Set (∀ i, K i)) →* N i :=
    ((Pi.evalMonoidHom K i).comp (normalizer (P : Set (∀ i, K i))).subtype).codRestrict
      (N i) (fun x => (P : Subgroup (∀ i, K i)).le_normalizer_map
        (Pi.evalMonoidHom K i) (mem_map_of_mem _ x.property))
  have hf : Function.Injective (MonoidHom.pi f) := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have hfree : Nat.Coprime 3 (Nat.card (∀ i, N i)) := by
    rw [Nat.card_pi]
    exact Nat.Coprime.prod_right fun i _ => (Nat.prime_three.coprime_iff_not_dvd).mpr (hK i (Q i))
  exact (Nat.prime_three.coprime_iff_not_dvd).mp
    (hfree.of_dvd_right (card_dvd_of_injective _ hf))
end Product

variable [Finite D]

omit [Finite D] in
/-- Absence of three in normalizers descends through arbitrary surjections. -/
private theorem image_normalizer_three_free {X : Type*} [Group X] [Finite X]
    (f : X →* D) (hf : Function.Surjective f)
    (hX : ∀ P : Sylow 2 X, ¬ 3 ∣ Nat.card (normalizer (P : Set X)))
    (S : Sylow 2 D) : ¬ 3 ∣ Nat.card (normalizer (S : Set D)) := by
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hf 2 S
  have hPS : P.map f = (S : Subgroup D) := congrArg Sylow.toSubgroup hP
  have hn := P.normalizer_map_surjective f hf
  rw [hPS, Sylow.coe_coe] at hn
  intro hd
  rw [← hn] at hd
  exact hX P (hd.trans (card_dvd_of_surjective
    (f.subgroupMap _) (f.subgroupMap_surjective _)))

/-- A cubic in C forces even field degree in a commuting product of the models. -/
theorem family_even {ι : Type*} [Fintype ι]
    (K : ι → Subgroup D)
    (hc : Pairwise fun i j => K i ≤ centralizer (K j : Set D))
    (hgen : iSup K = ⊤) (n : ℕ) (r : ι → ℕ)
    (hK : ∀ i, NormalizerData (K i) n (r i))
    (C : Subgroup D) (hC : CubicSylowControl D C) : Even n := by
  by_contra he
  have ho : Odd n := Nat.not_even_iff_odd.mp he
  obtain ⟨S, hn⟩ := hC.normalized
  have hCB := (family_borel K hc hgen n r hK C hC S hn).1
  have hcomm : Pairwise fun i j => ∀ x y : D,
      x ∈ K i → y ∈ K j → Commute x y :=
    fun _ _ hij _x y hx hy => (hc hij hx y hy).symm
  let f := noncommPiCoprod hcomm
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp
    (noncommPiCoprod_range.trans hgen)
  have hfree := image_normalizer_three_free f hf
    (product_normalizer_three_free (fun i => K i) (fun i => (hK i).odd ho)) S
  obtain ⟨c, hco⟩ := hC.cubic
  let x : normalizer (S : Set D) := ⟨c, hCB c.property⟩
  have hx : orderOf x = 3 := (Subgroup.orderOf_coe x).symm.trans
    ((Subgroup.orderOf_coe c).trans hco)
  exact hfree (hx ▸ orderOf_dvd_natCard x)

/-- Every individual factor's Borel theta rank is at most one, even when the
factor centers overlap. The factor normalizer maps injectively to the ambient one. -/
theorem family_factor_rank_le_one {ι : Type*} [Fintype ι]
    (K : ι → Subgroup D)
    (hc : Pairwise fun i j => K i ≤ centralizer (K j : Set D))
    (hgen : iSup K = ⊤) (n : ℕ) (r : ι → ℕ)
    (hK : ∀ i, NormalizerData (K i) n (r i))
    (C : Subgroup D) (hC : CubicSylowControl D C) (i : ι)
    (k : ℕ) (hi : NormalizerData (K i) n k) : k ≤ 1 := by
  have he := family_even K hc hgen n r hK C hC
  obtain ⟨S, hn⟩ := hC.normalized
  have hr := (family_borel K hc hgen n r hK C hC S hn).2.2
  obtain ⟨R, _, hR⟩ := Sylow.factor_normalizer_control K hc hgen S i
  have ht : (theta (normalizer (R : Set (K i)))).map (K i).subtype ≤
      theta (normalizer (S : Set D)) := by
    rw [theta_map_of_injective _ (K i).subtype_injective]
    exact theta_mono hR
  let f : theta (normalizer (R : Set (K i))) →* theta (normalizer (S : Set D)) :=
    (((K i).subtype).comp (theta (normalizer (R : Set (K i)))).subtype).codRestrict _
      (fun x => ht (mem_map_of_mem _ x.property))
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : theta (normalizer (S : Set D)) => (z : D)) h
  exact (hi.rank he R).trans
    ((Theory.GroupTheory.primeRank_le_of_injective 3 f hf).trans hr)
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry

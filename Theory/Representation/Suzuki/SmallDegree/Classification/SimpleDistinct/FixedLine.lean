module

public import Theory.Representation.Suzuki.SmallDegree.Classification.SimpleDistinct.HighestVector
public import Theory.Representation.G2.RestrictedModules.Steinberg.BinaryOrbit.Regular
public import Theory.Representation.InvariantsBaseChange
public import Mathlib.RingTheory.Flat.Basic

/-!
# The root-fixed line in concrete Suzuki Frobenius tensors

Put `q = 2^(2*m+1)`. The full word has dimension `q²`, the order of the
actual upper root subgroup. Its lowest pure tensor has nonzero root norm:
the highest coefficient at `u(a,b)` is the `(q-1)`st power of the upper-right
matrix entry. The Suzuki ovoid norm vanishes exactly when `(a,b) = (0,0)`,
so summing this coefficient over the root subgroup gives `q²-1 = 1` in the
defining field. The general modular p-group orbit lemma then makes that orbit
a basis and shows that its fixed space is the published highest line.

Inserting highest vectors at omitted positions embeds every support word as
a root module into the full word. Taking invariants commutes with scalar
extension, which proves the result over every extension field. This includes
empty and full support, and `m = 1`, without using tensor simplicity,
distinctness, exhaustion, or cyclicity as a premise.

Sources: GLS3, 2.8.2--2.8.9; Guralnick--Malle, *Classification of 2F-modules,
II*, §3.1, equation (3.2). The matrix norm calculation is the proved
Huppert--Blackburn XI.3.3 ovoid norm in the repository's upper-root convention.
-/

public noncomputable section
open scoped TensorProduct
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural
set_option backward.isDefEq.respectTransparency false

namespace FixedLine

local instance (m : ℕ) : Fintype (F m) := Fintype.ofFinite _
local instance (m : ℕ) : Fintype (SuzukiRootSubgroup m) := Fintype.ofFinite _

private def lowestVector (m : ℕ) : (l : List ℕ) → WordSpace m l
  | [] => (1 : F m)
  | _ :: l => (Pi.single 3 1 : W m) ⊗ₜ[F m] lowestVector m l

private theorem coefficient_lowest (m : ℕ) (l : List ℕ) (g : SuzukiMatrixGroup m) :
    wordHighestCoefficient m l (wordRep m l g (lowestVector m l)) =
      g.val.val 0 3 ^ (l.map (2 ^ ·)).sum := by
  induction l with
  | nil => change (1 : F m) = _ ^ 0; rw [pow_zero]
  | cons i l ih =>
    change (_root_.TensorProduct.lid (F m) (F m))
      (TensorProduct.map (LinearMap.proj 0) (wordHighestCoefficient m l)
        (factorRep m i g (Pi.single 3 1) ⊗ₜ[F m]
          wordRep m l g (lowestVector m l))) = _
    simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.proj_apply,
      ih, List.map_cons, List.sum_cons, pow_add]
    rw [factorRep_apply]
    simp [Pi.single_apply]

private theorem sum_binary_range (n : ℕ) :
    ((List.range n).map (2 ^ ·)).sum + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.range_succ, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
                 rw [pow_succ]; omega

private theorem root_entry_ne_zero (m : ℕ) (g : SuzukiRootSubgroup m) (hg : g ≠ 1) :
    g.val.val.val 0 3 ≠ 0 := by
  obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff m g.val).mp g.property
  let pi : F m ≃+* F m := iterateFrobeniusEquiv (F m) 2 (m + 1)
  have hpi : ∀ x : F m, pi x = x ^ (2 ^ (m + 1)) :=
    iterateFrobeniusEquiv_def (F m) 2 (m + 1)
  intro hz
  have hnorm : a * b + pi a * a ^ 2 + pi b = 0 := by
    simpa [hab, SuzukiRootGL, SuzukiRootMatrix, hpi, pow_add, add_comm, mul_comm]
      using hz
  obtain ⟨rfl, rfl⟩ := (BenderSuzuki.External.suzukiOvoidNorm_eq_zero m pi
    (BenderSuzuki.External.binaryGaloisField_tits_formula_sq m pi hpi) a b).mp hnorm
  apply hg
  apply Subtype.ext
  apply Subtype.ext
  rw [hab]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SuzukiRootGL, SuzukiRootMatrix]

private theorem field_card (m : ℕ) : Fintype.card (F m) = 2 ^ (2 * m + 1) := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 2 (2 * m + 1) (by omega)

private theorem full_norm_coefficient (m : ℕ) (hm : 0 < m) :
    wordHighestCoefficient m (List.range (2 * m + 1))
      (∑ g : SuzukiRootSubgroup m,
        wordRep m (List.range (2 * m + 1)) g.val
          (lowestVector m (List.range (2 * m + 1)))) = 1 := by
  classical
  rw [map_sum]
  have he : ((List.range (2 * m + 1)).map (2 ^ ·)).sum =
      Fintype.card (F m) - 1 := by rw [field_card]; have := sum_binary_range (2 * m + 1); omega
  have hterm (g : SuzukiRootSubgroup m) :
      wordHighestCoefficient m (List.range (2 * m + 1))
        (wordRep m (List.range (2 * m + 1)) g.val
          (lowestVector m (List.range (2 * m + 1)))) =
      1 - (if g = 1 then 1 else 0) := by
    rw [coefficient_lowest, he]
    by_cases hg : g = 1
    · subst g
      simp [Nat.sub_ne_zero_of_lt Fintype.one_lt_card]
    · rw [if_neg hg, sub_zero]
      exact FiniteField.pow_card_sub_one_eq_one _ (root_entry_ne_zero m g hg)
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  have hc : (Fintype.card (SuzukiRootSubgroup m) : F m) = 0 := by
    rw [Fintype.card_eq_nat_card, suzukiRootSubgroup_card m hm]
    have htwo : (2 : F m) = 0 := CharP.cast_eq_zero (F m) 2
    simp [Nat.cast_pow, htwo]
  simp [hc, CharTwo.neg_eq]

/-- The fixed line in the full word, proved from its nonzero root norm. -/
private theorem full_word_fixed_root (m : ℕ) (hm : 1 ≤ m)
    (v : WordSpace m (List.range (2 * m + 1)))
    (hv : ∀ g ∈ SuzukiRootSubgroup m,
      wordRep m (List.range (2 * m + 1)) g v = v) :
    ∃ c : F m, v = c • wordHighestVector m (List.range (2 * m + 1)) := by
  classical
  let ρ := (wordRep m (List.range (2 * m + 1))).comp (SuzukiRootSubgroup m).subtype
  let z := lowestVector m (List.range (2 * m + 1))
  have hn : (∑ g : SuzukiRootSubgroup m, ρ g z) ≠ 0 := by
    intro h
    have hc := full_norm_coefficient m (by omega)
    change wordHighestCoefficient m _ (∑ g : SuzukiRootSubgroup m, ρ g z) = 1 at hc
    rw [h, map_zero] at hc
    exact zero_ne_one hc
  have hp : IsPGroup (ringChar (F m)) (SuzukiRootSubgroup m) := by
    rw [ringChar.eq (F m) 2]
    exact suzukiRootSubgroup_isPGroup m (by omega)
  have hc : ringChar (F m) ≠ 0 := by rw [ringChar.eq (F m) 2]; decide
  have hi := Atlas.G2.Restricted.Steinberg.BinaryOrbit.Regular.independent_orbit hc hp ρ z hn
  have hspan : Submodule.span (F m) (Set.range fun g => ρ g z) = ⊤ := by
    apply hi.span_eq_top_of_card_eq_finrank'
    rw [finrank_wordSpace, List.length_range, ← Nat.card_eq_fintype_card,
      suzukiRootSubgroup_card m (by omega)]
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hfixed (x : WordSpace m (List.range (2 * m + 1)))
      (hx : ∀ g, ρ g x = x) : ∃ c : F m, x = c • ∑ g, ρ g z :=
    Atlas.G2.Restricted.Steinberg.BinaryOrbit.Regular.fixed_span_orbit hc hp ρ z hn x
      (by rw [hspan]; trivial) hx
  obtain ⟨a, ha⟩ := hfixed v (fun g => hv g.val g.property)
  obtain ⟨b, hb⟩ := hfixed (wordHighestVector m (List.range (2 * m + 1)))
    (fun g => wordHighestVector_fixed_root m _ g.val g.property)
  have hb0 : b ≠ 0 := by
    intro h
    exact wordHighestVector_ne_zero m _ (by simpa only [h, zero_smul] using hb)
  refine ⟨a / b, ?_⟩
  rw [hb, smul_smul, div_mul_cancel₀ _ hb0]
  exact ha

/-- Inserting highest vectors at omitted positions embeds smaller words
as root modules and preserves their specified highest vector. -/
private theorem exists_word_embedding (m : ℕ) {l L : List ℕ} (h : l.Sublist L) :
    ∃ j : WordSpace m l →ₗ[F m] WordSpace m L,
      Function.Injective j ∧
      j (wordHighestVector m l) = wordHighestVector m L ∧
      ∀ g ∈ SuzukiRootSubgroup m, ∀ v,
        j (wordRep m l g v) = wordRep m L g (j v) := by
  induction h with
  | slnil => exact ⟨LinearMap.id, Function.injective_id, rfl, fun _ _ _ => rfl⟩
  | @cons l L i h ih =>
    obtain ⟨j, hinj, hseed, hact⟩ := ih
    let k : WordSpace m L →ₗ[F m] WordSpace m (i :: L) :=
      TensorProduct.mk (F m) (W m) (WordSpace m L) (naturalHighestVector m)
    refine ⟨k.comp j, ?_, ?_, ?_⟩
    · intro x y hxy
      apply hinj
      change naturalHighestVector m ⊗ₜ[F m] j x =
        naturalHighestVector m ⊗ₜ[F m] j y at hxy
      have he := congrArg (fun z => (_root_.TensorProduct.lid (F m) (WordSpace m L))
        (TensorProduct.map (LinearMap.proj 0) LinearMap.id z)) hxy
      simpa [naturalHighestVector, TensorProduct.map_tmul] using he
    · change naturalHighestVector m ⊗ₜ[F m] j (wordHighestVector m l) = _
      rw [hseed]
      rfl
    · intro g hg v
      change naturalHighestVector m ⊗ₜ[F m] j (wordRep m l g v) =
        factorRep m i g (naturalHighestVector m) ⊗ₜ[F m] wordRep m L g (j v)
      rw [hact g hg v, factorHighestVector_fixed_root m i g hg]
  | @cons_cons l L i h ih =>
    obtain ⟨j, hinj, hseed, hact⟩ := ih
    refine ⟨TensorProduct.map LinearMap.id j,
      TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id hinj, ?_, ?_⟩
    · change TensorProduct.map LinearMap.id j
        (naturalHighestVector m ⊗ₜ[F m] wordHighestVector m l) = _
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, hseed]
      rfl
    · intro g hg v
      suffices he : (TensorProduct.map LinearMap.id j).comp (wordRep m (i :: l) g) =
          (wordRep m (i :: L) g).comp (TensorProduct.map LinearMap.id j) by
        exact LinearMap.congr_fun he v
      apply TensorProduct.ext'
      intro x y
      change TensorProduct.map LinearMap.id j
        (factorRep m i g x ⊗ₜ[F m] wordRep m l g y) = _
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, hact g hg y]
      rfl

private theorem exponents_sublist (m : ℕ) (I : Support m) :
    (exponents I).Sublist (List.range (2 * m + 1)) := by
  have hs : (I.sort (· ≤ ·)).Sublist (Finset.univ.sort (· ≤ ·)) := by
    apply List.sublist_of_subperm_of_pairwise
      (List.subperm_of_subset (Finset.sort_nodup I (· ≤ ·)) ?_)
      (Finset.pairwise_sort _ _) (Finset.pairwise_sort _ _)
    intro i hi
    exact (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_univ i)
  have := hs.map Fin.val
  simpa [exponents, Fin.sort_univ] using this


end FixedLine

/-- Root-fixed vectors in every support word form its specified highest line. -/
theorem word_fixed_root (m : ℕ) (hm : 1 ≤ m) (I : Support m)
    (v : WordSpace m (exponents I))
    (hv : ∀ g ∈ SuzukiRootSubgroup m, wordRep m (exponents I) g v = v) :
    ∃ c : F m, v = c • wordHighestVector m (exponents I) := by
  obtain ⟨j, hinj, hseed, hact⟩ := FixedLine.exists_word_embedding m
    (FixedLine.exponents_sublist m I)
  obtain ⟨c, hc⟩ := FixedLine.full_word_fixed_root m hm (j v) (by
    intro g hg
    rw [← hact g hg v, hv g hg])
  refine ⟨c, hinj ?_⟩
  rwa [map_smul, hseed]

/-- For every coefficient-field extension, the root-fixed space of a concrete
Suzuki Frobenius tensor is exactly its published highest line. -/
theorem tensor_fixed_root (m : ℕ) (hm : 1 ≤ m) (K : Type*) [Field K]
    [Algebra (F m) K] (I : Support m) (v : TensorSpace m K I)
    (hv : ∀ g ∈ SuzukiRootSubgroup m, tensorRep m K I g v = v) :
    ∃ c : K, v = c • tensorHighestVector m K I := by
  let ρ : Representation (F m) (SuzukiRootSubgroup m) (WordSpace m (exponents I)) :=
    (wordRep m (exponents I)).comp (SuzukiRootSubgroup m).subtype
  have he : ρ.invariants = Submodule.span (F m) {wordHighestVector m (exponents I)} := by
    ext x
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := word_fixed_root m hm I x (fun g hg => hx ⟨g, hg⟩)
      exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
    · intro hx g
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      exact (map_smul _ _ _).trans
        (congrArg (fun z => c • z) (wordHighestVector_fixed_root m _ g.val g.property))
  have hv' : v ∈ (Representation.extendScalars K ρ).invariants :=
    fun g => hv g.val g.property
  rw [Representation.invariants_extendScalars_eq_baseChange_of_finite, he,
    Submodule.baseChange_span, Set.image_singleton] at hv'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv'
  exact ⟨c, hc.symm⟩

end Representation.SuzukiSmallDegree

end

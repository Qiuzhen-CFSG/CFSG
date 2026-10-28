module

public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Defining-characteristic rank in SL₂ and PSL₂

For a finite field of cardinality `p^e`, the upper transvections give prime
rank at least `e` in every group containing SL₂ or PSL₂. The projective map
is injective on transvections because a central transvection is trivial.
In odd characteristic the image of `-1` under an SL₂ embedding is an
involution, and the whole SL₂ image lies in its centralizer. Thus the same
lower bound is a local rank witness, not merely an ordinary rank bound.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma A.2.17, pp. 38–39.
-/

namespace Matrix.SpecialLinearGroup

/-- Transvections in an embedded SL₂ witness the defining-field degree. -/
public theorem fieldExponent_le_primeRank_of_injective {K G : Type*}
    [Field K] [Finite K] [Group G] [Finite G]
    {p e : ℕ} [Fact p.Prime] [CharP K p] (hcard : Nat.card K = p ^ e)
    (f : Matrix.SpecialLinearGroup (Fin 2) K →* G) (hf : Function.Injective f) :
    e ≤ primeRank p G := by
  apply primeRank_ge_of_elementary_embedding (A := Multiplicative K) (p := p)
    (fun a => ?_) hcard (f.comp (Matrix.SpecialLinearGroup.upperUnipotentHom K))
    (hf.comp (Matrix.SpecialLinearGroup.upperUnipotentHom_injective K))
  change p • a.toAdd = 0
  simp [nsmul_eq_mul]

section Centralizer
variable {K G : Type*} [Field K] [Group G]
local instance : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩

private def sl2CentralizerMap (f : Matrix.SpecialLinearGroup (Fin 2) K →* G) :
    Matrix.SpecialLinearGroup (Fin 2) K →*
      Subgroup.centralizer ({f (-1)} : Set G) :=
  f.codRestrict _ fun a => by
    rw [Subgroup.mem_centralizer_singleton_iff, ← f.map_mul, ← f.map_mul]
    congr 1
    simp

/-- The root-group witness lies in the centralizer of the scalar `-1`. -/
public theorem fieldExponent_le_primeRank_centralizer [Finite K] [Finite G] {p e : ℕ} [Fact p.Prime]
    [CharP K p] (hcard : Nat.card K = p ^ e)
    (f : Matrix.SpecialLinearGroup (Fin 2) K →* G) (hf : Function.Injective f) :
    e ≤ primeRank p (Subgroup.centralizer ({f (-1)} : Set G)) := by
  apply fieldExponent_le_primeRank_of_injective hcard (sl2CentralizerMap f)
  intro a b h
  exact hf (congrArg Subtype.val h)

/-- In odd characteristic an SL₂ embedding sends `-1` to an involution. -/
public theorem map_neg_one_isInvolution {p : ℕ} [Fact p.Prime] [CharP K p] (hp : p ≠ 2)
    (f : Matrix.SpecialLinearGroup (Fin 2) K →* G) (hf : Function.Injective f) :
    f (-1) ≠ 1 ∧ f (-1) ^ 2 = 1 := by
  constructor
  · intro he
    have hm : (-1 : Matrix.SpecialLinearGroup (Fin 2) K) = 1 :=
      hf (he.trans f.map_one.symm)
    have hentry := congrArg (fun a : Matrix.SpecialLinearGroup (Fin 2) K => a.1 0 0) hm
    have : Fact (2 < p) := ⟨lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)⟩
    exact CharP.neg_one_ne_one K p (by simpa using hentry)
  · rw [← map_pow]
    simp [pow_two]
end Centralizer

/-- The central quotient is injective on the upper transvections. -/
public theorem projectiveUpperUnipotentHom_injective (K : Type*) [Field K] :
    Function.Injective
      ((QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))).comp
        (Matrix.SpecialLinearGroup.upperUnipotentHom K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have hc : Matrix.SpecialLinearGroup.upperUnipotentHom K a ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (QuotientGroup.eq_one_iff _).mp ha
  have ht : a.toAdd = 0 :=
    (Matrix.SpecialLinearGroup.transvection_mem_center_iff zero_ne_one a.toAdd).mp hc
  exact ht

/-- Projective transvections give the same defining-characteristic rank bound. -/
public theorem fieldExponent_le_primeRank_of_projective_injective {K G : Type*}
    [Field K] [Finite K] [Group G] [Finite G]
    {p e : ℕ} [Fact p.Prime] [CharP K p] (hcard : Nat.card K = p ^ e)
    (f : (Matrix.SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) →* G)
    (hf : Function.Injective f) : e ≤ primeRank p G := by
  apply primeRank_ge_of_elementary_embedding (A := Multiplicative K) (p := p)
    (fun a => ?_) hcard
    (f.comp ((QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))).comp
      (Matrix.SpecialLinearGroup.upperUnipotentHom K)))
    (hf.comp (projectiveUpperUnipotentHom_injective K))
  change p • a.toAdd = 0
  simp [nsmul_eq_mul]

/-- A direct product of an involution with PSL₂ gives a local rank witness. -/
public theorem exists_involution_primeRank_ge_of_projective_product {K G : Type*}
    [Field K] [Finite K] [Group G] [Finite G] {p e : ℕ} [Fact p.Prime] [CharP K p] (hcard : Nat.card K = p ^ e)
    (f : Multiplicative (ZMod 2) × (SpecialLinearGroup (Fin 2) K ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) K)) →* G) (hf : Function.Injective f) :
    ∃ z : G, z ≠ 1 ∧ z ^ 2 = 1 ∧ e ≤ primeRank p (Subgroup.centralizer ({z} : Set G)) := by
  let z : Multiplicative (ZMod 2) × (SpecialLinearGroup (Fin 2) K ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) K)) := (Multiplicative.ofAdd 1, 1)
  have hz : z ≠ 1 := by
    intro h
    have := congrArg (fun a : Multiplicative (ZMod 2) × (SpecialLinearGroup (Fin 2) K ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) K)) => a.1.toAdd) h
    exact one_ne_zero this
  have hz2 : z ^ 2 = 1 := by
    apply Prod.ext
    · change Multiplicative.ofAdd (1 : ZMod 2) ^ 2 = 1
      decide
    · simp [z]
  refine ⟨f z, fun h => hz (hf (h.trans f.map_one.symm)), ?_, ?_⟩
  · rw [← map_pow, hz2, map_one]
  · let j : (SpecialLinearGroup (Fin 2) K ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) K)) →* Subgroup.centralizer ({f z} : Set G) :=
      (f.comp (MonoidHom.inr _ _)).codRestrict _ fun a => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        change f (1, a) * f z = f z * f (1, a)
        rw [← map_mul, ← map_mul]
        congr 1
        ext <;> simp [z]
    apply SpecialLinearGroup.fieldExponent_le_primeRank_of_projective_injective hcard j
    intro a b h
    exact congrArg Prod.snd (hf (congrArg Subtype.val h))

end Matrix.SpecialLinearGroup

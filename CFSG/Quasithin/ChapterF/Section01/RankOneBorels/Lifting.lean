module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting.Transport
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Lifting the rank-one normalizer conclusions through the two-core

Source: Aschbacher–Smith, printed pp.259–260, F.1.2–F.1.3(1).
The actual quotient projection restricts to a surjection of Sylow normalizers,
with kernel O₂(H) restricted to the normalizer. Its first isomorphism theorem supplies the
normalizer quotient identification. Solvability lifts across the finite
2-group kernel. The normalizer modulo its Sylow subgroup is unchanged; hence
it is abelian when the quotient model has an abelian complement. Schur–Zassenhaus
then supplies a complement upstairs, isomorphic to that abelian odd-order quotient.

All results here are conditional transport lemmas. The concrete model premises
must still be discharged to establish the source theorem.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.Source
variable {H : Type*} [Group H] [Finite H]

/-- The intrinsic normalizer of the chosen Sylow two-subgroup. -/
abbrev sylowNormalizer (T : Sylow 2 H) := Subgroup.normalizer ((T : Subgroup H) : Set H)
/-- The Sylow subgroup, regarded as a normal subgroup of its own normalizer. -/
abbrev sylowInNormalizer (T : Sylow 2 H) := (T : Subgroup H).subgroupOf (sylowNormalizer T)

/-- The restriction of the actual projection H → H/O₂(H) to Sylow normalizers. -/
def normalizerProjection (T : Sylow 2 H) :
    sylowNormalizer T →* sylowNormalizer (quotientSylow T) :=
  ((QuotientGroup.mk' (pCore 2 H)).comp (sylowNormalizer T).subtype).codRestrict _
    (fun x => by
      have hx : (x : H) ∈ (sylowNormalizer (quotientSylow T)).comap
          (QuotientGroup.mk' (pCore 2 H)) := by
        rw [quotientSylow_normalizer_comap]; exact x.property
      exact hx)

/-- The restricted projection is onto the quotient Sylow normalizer. -/
theorem normalizerProjection_surjective (T : Sylow 2 H) :
    Function.Surjective (normalizerProjection T) := by
  intro y
  have hy : (y : H ⧸ pCore 2 H) ∈ (sylowNormalizer T).map
      (QuotientGroup.mk' (pCore 2 H)) := by
    rw [quotientSylow_normalizer_map]; exact y.property
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- Its kernel is O₂(H) regarded as a subgroup of the original normalizer. -/
theorem normalizerProjection_ker (T : Sylow 2 H) :
    (normalizerProjection T).ker = (pCore 2 H).subgroupOf (sylowNormalizer T) := by
  ext x
  change (⟨QuotientGroup.mk' (pCore 2 H) x, _⟩ : sylowNormalizer (quotientSylow T)) = 1 ↔ _
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff (x : H)

/-- The normalizer modulo the relative two-core is the quotient Sylow normalizer. -/
noncomputable def normalizerQuotientEquiv (T : Sylow 2 H) :
    sylowNormalizer T ⧸ (pCore 2 H).subgroupOf (sylowNormalizer T) ≃*
      sylowNormalizer (quotientSylow T) :=
  (QuotientGroup.quotientMulEquivOfEq (normalizerProjection_ker T).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (normalizerProjection_surjective T))

/-- On representatives the normalizer quotient equivalence is the restricted projection. -/
@[simp] theorem normalizerQuotientEquiv_mk (T : Sylow 2 H) (x : sylowNormalizer T) :
    normalizerQuotientEquiv T (QuotientGroup.mk x) = normalizerProjection T x := rfl

/-- Project the normalizer and then divide by the quotient Sylow subgroup. -/
def normalizerSylowQuotientProjection (T : Sylow 2 H) :
    sylowNormalizer T →* sylowNormalizer (quotientSylow T) ⧸
      sylowInNormalizer (quotientSylow T) :=
  (QuotientGroup.mk' _).comp (normalizerProjection T)

/-- The composite projection onto the normalizer/Sylow quotient is surjective. -/
theorem normalizerSylowQuotientProjection_surjective (T : Sylow 2 H) :
    Function.Surjective (normalizerSylowQuotientProjection T) :=
  (QuotientGroup.mk'_surjective _).comp (normalizerProjection_surjective T)

/-- The composite projection has precisely the original relative Sylow as kernel. -/
theorem normalizerSylowQuotientProjection_ker (T : Sylow 2 H) :
    (normalizerSylowQuotientProjection T).ker = sylowInNormalizer T := by
  ext x
  change QuotientGroup.mk' (sylowInNormalizer (quotientSylow T)) (normalizerProjection T x) = 1 ↔ (x : H) ∈ (T : Subgroup H)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  change (x : H) ∈ (quotientSylow T : Subgroup (H ⧸ pCore 2 H)).comap
    (QuotientGroup.mk' (pCore 2 H)) ↔ _
  rw [quotientSylow_comap]

/-- The normalizer/Sylow quotient is unchanged on dividing H by its two-core. -/
noncomputable def normalizerSylowQuotientEquiv (T : Sylow 2 H) :
    sylowNormalizer T ⧸ sylowInNormalizer T ≃*
      sylowNormalizer (quotientSylow T) ⧸ sylowInNormalizer (quotientSylow T) :=
  (QuotientGroup.quotientMulEquivOfEq (normalizerSylowQuotientProjection_ker T).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (normalizerSylowQuotientProjection_surjective T))

/-- The normalizer/Sylow equivalence is induced by the composite projection. -/
@[simp] theorem normalizerSylowQuotientEquiv_mk (T : Sylow 2 H) (x : sylowNormalizer T) :
    normalizerSylowQuotientEquiv T (QuotientGroup.mk x) =
      normalizerSylowQuotientProjection T x := rfl

private theorem commutative_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) [IsMulCommutative B] : IsMulCommutative A :=
  ⟨⟨fun x y => e.injective (by simp only [map_mul]; exact mul_comm' _ _)⟩⟩

private theorem quotient_commutative_of_sup {A : Type*} [Group A]
    (N D : Subgroup A) [N.Normal] [IsMulCommutative D] (h : N ⊔ D = ⊤) :
    IsMulCommutative (A ⧸ N) := by
  let q := QuotientGroup.mk' N
  have hm : D.map q = ⊤ := by
    have he := congrArg (Subgroup.map q) h
    have hN : N.map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff N).mpr
      exact (QuotientGroup.ker_mk' N).ge
    rw [Subgroup.map_sup, hN, bot_sup_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at he
    exact he
  have hsurj : Function.Surjective (q.comp D.subtype) := by
    intro y
    have hy : y ∈ D.map q := hm ▸ Subgroup.mem_top y
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, hxy⟩
  refine ⟨⟨?_⟩⟩
  intro x y
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  rw [← map_mul, ← map_mul, mul_comm' a b]

omit [Finite H] in
/-- An abelian complement makes the intrinsic normalizer/Sylow quotient abelian. -/
theorem RankOneSylowFacts.quotient_commutative (T : Sylow 2 H) (h : RankOneSylowFacts T) :
    IsMulCommutative (sylowNormalizer T ⧸ sylowInNormalizer T) := by
  obtain ⟨D, hD, _, ha, _, hs⟩ := h.abelian_odd_complement
  let := ha
  apply quotient_commutative_of_sup _ (D.subgroupOf (sylowNormalizer T))
  rw [← Subgroup.subgroupOf_sup (T : Subgroup H).le_normalizer hD, hs]
  exact Subgroup.subgroupOf_self _

/-- Solvability lifts through the finite two-core kernel. -/
theorem sylow_normalizer_solvable_of_quotient (T : Sylow 2 H)
    (h : Group.IsSolvable (sylowNormalizer (quotientSylow T))) :
    Group.IsSolvable (sylowNormalizer T) := by
  let := h
  have hp : IsPGroup 2 ((normalizerProjection T).ker) := by
    rw [normalizerProjection_ker]
    exact pCore_isPGroup.comap_subtype
  let := hp.isNilpotent
  exact Group.isSolvable_of_ker_le_range (normalizerProjection T).ker.subtype
    (normalizerProjection T) (by rw [Subgroup.range_subtype])

/-- Schur–Zassenhaus gives an abelian odd complement when normalizer/Sylow is abelian. -/
theorem sylow_normalizer_abelian_odd_complement (T : Sylow 2 H)
    (hc : IsMulCommutative (sylowNormalizer T ⧸ sylowInNormalizer T)) :
    ∃ D : Subgroup H, D ≤ sylowNormalizer T ∧ Nat.Coprime 2 (Nat.card D) ∧
      IsMulCommutative D ∧ Disjoint (T : Subgroup H) D ∧
        (T : Subgroup H) ⊔ D = sylowNormalizer T := by
  let P := T.subtype (T : Subgroup H).le_normalizer
  let : (P : Subgroup (sylowNormalizer T)).Normal := by
    change (sylowInNormalizer T).Normal
    infer_instance
  obtain ⟨D, hD⟩ := Subgroup.exists_right_complement'_of_coprime P.card_coprime_index
  let : IsMulCommutative ((sylowNormalizer T) ⧸ (P : Subgroup _)) := hc
  have ha : IsMulCommutative D := commutative_of_equiv hD.symm.QuotientMulEquiv.symm
  let := ha
  refine ⟨D.map (sylowNormalizer T).subtype, Subgroup.map_subtype_le _, ?_, inferInstance, ?_, ?_⟩
  · rw [← Nat.card_congr (D.equivMapOfInjective _ (sylowNormalizer T).subtype_injective).toEquiv,
      ← hD.symm.index_eq_card]
    exact Nat.prime_two.coprime_iff_not_dvd.mpr P.not_dvd_index
  · have hd := Subgroup.disjoint_map (sylowNormalizer T).subtype_injective hD.disjoint
    simpa only [P, Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le
      (T : Subgroup H).le_normalizer] using hd
  · have hs := congrArg (Subgroup.map (sylowNormalizer T).subtype) hD.sup_eq_top
    simpa only [Subgroup.map_sup, P, Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le
      (T : Subgroup H).le_normalizer, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hs

/-- Lift all intrinsic rank-one conclusions from H/O₂(H). -/
theorem rankOneSylowFacts_of_quotient (T : Sylow 2 H)
    (h : RankOneSylowFacts (quotientSylow T)) : RankOneSylowFacts T := by
  refine ⟨sylow_normalizer_proper_of_quotient T h.proper,
    sylow_normalizer_unique_of_quotient T h.unique_maximal,
    twoCore_sylow_normalizer T, sylow_normalizer_solvable_of_quotient T h.solvable, ?_⟩
  apply sylow_normalizer_abelian_odd_complement
  let := h.quotient_commutative (quotientSylow T)
  exact commutative_of_equiv (normalizerSylowQuotientEquiv T)
/-- The full conditional passage from a quotient-model Sylow to an ambient Borel. -/
theorem rankOneBorelFacts_of_quotient {G : Type*} [Group G]
    (L S : Subgroup G) [Finite L] (T : Sylow 2 L)
    (hT : (T : Subgroup L).map L.subtype = S ⊓ L)
    (h : RankOneSylowFacts (quotientSylow T)) : RankOneBorelFacts L S :=
  rankOneBorelFacts_of_sylow L S T hT (rankOneSylowFacts_of_quotient T h)

end CFSG.Quasithin.ChapterF.Source

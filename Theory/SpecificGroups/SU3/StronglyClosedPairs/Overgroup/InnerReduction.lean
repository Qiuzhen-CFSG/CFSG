module

public import Theory.SpecificGroups.SU3.StronglyClosedPairs.Inner
public import Theory.SpecificGroups.SU3.StronglyClosedPairs.Contract
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Restricting a strongly closed pair to the inner unitary group

The inner conjugation map into an automorphism overgroup is injective, by
centerlessness of the actual projective matrix group. Its range is normal.
Consequently a Sylow subgroup pulls back to a Sylow subgroup of PSU₃, and
the inner parts of a commuting strongly closed pair satisfy the inner
coordinate theorem. If both whole factors are inner, the resulting
containment and square identities give the full requested conclusion.

This reduction leaves the case involving an outer element open; innerness
of involutions alone is not asserted to imply innerness of whole factors.
Source: the terminal model calculation in Aschbacher (1975), Lemma 3.4,
pp.94–96, using Huppert II.10.12 for the actual Hermitian root group.
-/

open Subgroup Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs

variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The full inner action with codomain restricted to the given overgroup. -/
@[expose] public def innerHom
    (K : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hK : (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range ≤ K) :
    ProjectiveSpecialUnitaryMatrixGroup J →* K :=
  MulAut.conj.codRestrict K (fun g => hK ⟨g, rfl⟩)

private theorem centerless [Finite E] {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n) :
    center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  apply EvenTwoRank.standard_center_eq_bot J hJ
  by_contra! h
  have hc : Nat.card {x : E // J.conj x = x} = Nat.card E :=
    Nat.card_congr (Equiv.subtypeUnivEquiv h)
  rw [hcard, hfixed] at hc
  have hp : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  nlinarith

private theorem innerHom_injective [Finite E] {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (K : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hK : (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range ≤ K) :
    Function.Injective (innerHom J K hK) := by
  intro x y h
  apply MulAut.conj_injective_of_center_eq_bot (centerless J hn hJ hcard hfixed)
  exact congrArg Subtype.val h

private theorem innerHom_range
    (K : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hK : (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range ≤ K) :
    (innerHom J K hK).range =
      (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)).comap K.subtype := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩

private theorem exists_sylow_comap {G H : Type*} [Group G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Injective f) [f.range.Normal]
    (T : Sylow 2 H) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = (T : Subgroup H).comap f := by
  obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_normal f.range
  let P := Q.comapOfInjective f.rangeRestrict
    (fun x y h => hf (congrArg Subtype.val h))
    (by rw [MonoidHom.range_eq_top.mpr f.rangeRestrict_surjective]; exact le_top)
  refine ⟨P, ?_⟩
  change (Q : Subgroup f.range).comap f.rangeRestrict = _
  rw [hQ]
  rfl

/-- The original overgroup Sylow pulls back to an actual Sylow of PSU₃. -/
public theorem innerHom_sylow [Finite E] {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (K : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hK : (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range ≤ K)
    (T : Sylow 2 K) :
    ∃ P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
        (T : Subgroup K).comap (innerHom J K hK) := by
  let X := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite X := Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let f := innerHom J K hK
  have hf : Function.Injective f := innerHom_injective J hn hJ hcard hfixed K hK
  have : f.range.Normal := by
    rw [show f.range = (MulAut.innerSubgroup X).comap K.subtype from innerHom_range J K hK]
    infer_instance
  exact exists_sylow_comap f hf T

/-- The inner parts of arbitrary commuting strongly closed factors are nested,
with square one on the smaller part. No whole-factor innerness is assumed. -/
public theorem inner_parts_nested_elementary [Finite E] {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (K : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hK : (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range ≤ K)
    (T : Sylow 2 K) (B C : Subgroup K)
    (hBT : B ≤ T) (hCT : C ≤ T) (hBC : ⁅B, C⁆ = ⊥)
    (hclosed : IsStronglyClosedSet ((B : Set K) ∪ C) (T : Subgroup K) ⊤) :
    (B.comap (innerHom J K hK) ≤ C.comap (innerHom J K hK) ∧
      ∀ x ∈ B.comap (innerHom J K hK), x ^ 2 = 1) ∨
    (C.comap (innerHom J K hK) ≤ B.comap (innerHom J K hK) ∧
      ∀ x ∈ C.comap (innerHom J K hK), x ^ 2 = 1) := by
  let X := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite X := Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let f := innerHom J K hK
  have hf : Function.Injective f := innerHom_injective J hn hJ hcard hfixed K hK
  obtain ⟨P, hP⟩ := innerHom_sylow J hn hJ hcard hfixed K hK T
  apply inner_factors_nested_elementary J hn hJ hcard hfixed P
  · rw [hP]; exact comap_mono hBT
  · rw [hP]; exact comap_mono hCT
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    intro b hb
    apply mem_centralizer_iff.mpr
    intro c hc
    apply hf
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hBC) hb) (f c) hc
  · constructor
    · intro x hx
      rw [hP]
      exact hclosed.1 hx
    · intro x hx g _ hreturn
      have hr : f (g⁻¹ * x * g) ∈ (T : Subgroup K) := by
        simpa only [hP, mem_comap] using hreturn
      have hh := hclosed.2 (f x) hx (f g) (mem_top _) (by
        simpa only [map_mul, map_inv] using hr)
      change f (g⁻¹ * x * g) ∈ (B : Set K) ∪ C
      simpa only [map_mul, map_inv] using hh

/-- The full rigidity conclusion when both factors lie in the inner image.
The outer-factor branch is a separate model obligation. -/
public theorem factors_nested_elementary_of_inner [Finite E] {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (K : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hK : (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range ≤ K)
    (T : Sylow 2 K) (B C : Subgroup K)
    (hBT : B ≤ T) (hCT : C ≤ T) (hBC : ⁅B, C⁆ = ⊥)
    (hclosed : IsStronglyClosedSet ((B : Set K) ∪ C) (T : Subgroup K) ⊤)
    (hB : B ≤ (innerHom J K hK).range) (hC : C ≤ (innerHom J K hK).range) :
    (B ≤ C ∧ ∀ b ∈ B, b ^ 2 = 1) ∨
      (C ≤ B ∧ ∀ c ∈ C, c ^ 2 = 1) := by
  let f := innerHom J K hK
  have lift (A D : Subgroup K) (hA : A ≤ f.range)
      (hle : A.comap f ≤ D.comap f) (hsq : ∀ x ∈ A.comap f, x ^ 2 = 1) :
      A ≤ D ∧ ∀ a ∈ A, a ^ 2 = 1 := by
    constructor
    · intro a ha
      obtain ⟨x, rfl⟩ := hA ha
      exact hle ha
    · intro a ha
      obtain ⟨x, rfl⟩ := hA ha
      rw [← map_pow, hsq x ha, map_one]
  rcases inner_parts_nested_elementary J hn hJ hcard hfixed K hK T B C hBT hCT hBC hclosed
      with ⟨hle, hsq⟩ | ⟨hle, hsq⟩
  · exact Or.inl (lift B C hB hle hsq)
  · exact Or.inr (lift C B hC hle hsq)

end BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs

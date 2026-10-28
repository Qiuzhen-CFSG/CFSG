module

public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Quasithin.LocalRank

/-!
# Local rank in a commuting product with cubic intersection

A p-subgroup in the first factor and a subgroup in the second are disjoint
when the factor intersection is a three-group and p ≠ 3. Their commuting
product lies in the normalizer of the original first-factor two-subgroup,
embedded in the ambient group. Additivity of prime rank supplies the local
obstruction without assuming that an image of a two-local is two-local.

Source: Aschbacher–Smith A.2.12(II), printed p.37.
-/

public section
namespace Theory.Quasithin.CubicIntersection

open Subgroup Theory.GroupTheory

variable {H : Type*} [Group H] [Finite H]

/-- The independent product lies in the actual ambient normalizer. -/
theorem exists_normalizer_rank_sum (A B : Subgroup H) (hc : A ≤ centralizer (B : Set H))
    (hI : IsPGroup 3 (A ⊓ B : Subgroup H))
    {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (Q E : Subgroup A) (F : Subgroup B)
    (hQ : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (hE : IsPGroup p E)
    (hEn : E ≤ normalizer (Q : Set A)) :
    ∃ R : Subgroup H, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      primeRank p E + primeRank p F ≤ primeRank p (normalizer (R : Set H)) := by
  let E' := E.map A.subtype
  let F' := F.map B.subtype
  let R := Q.map A.subtype
  have hEA : E' ≤ A := map_subtype_le E
  have hFB : F' ≤ B := map_subtype_le F
  have hRA : R ≤ A := map_subtype_le Q
  have hdI : Disjoint E' (A ⊓ B) :=
    IsPGroup.disjoint_of_ne p 3 hp3 _ _ (hE.map A.subtype) hI
  have hd : Disjoint E' F' := by
    apply disjoint_def.mpr
    intro x hx hy
    exact disjoint_def.mp hdI hx ⟨hEA hx, hFB hy⟩
  have hcc : E' ≤ centralizer (F' : Set H) := by
    intro x hx y hy
    exact hc (hEA hx) y (hFB hy)
  have hEN : E' ≤ normalizer (R : Set H) :=
    (map_mono hEn).trans (le_normalizer_map A.subtype)
  have hFN : F' ≤ normalizer (R : Set H) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro y hy x hx
    exact (hc (hRA hx) y (hFB hy)).symm
  refine ⟨R, ?_, hQ.map A.subtype, ?_⟩
  · exact fun hz => hQne ((map_eq_bot_iff_of_injective Q A.subtype_injective).mp hz)
  · have hl := primeRank_le_of_injective p (inclusion (sup_le hEN hFN))
      (inclusion_injective (sup_le hEN hFN))
    rw [primeRank_sup_eq_add_of_disjoint_commuting E' F' hd hcc p] at hl
    rwa [← primeRank_equiv p (equivMapOfInjective E A.subtype A.subtype_injective),
      ← primeRank_equiv p (equivMapOfInjective F B.subtype B.subtype_injective)] at hl

/-- Numerical factor ranks supply actual subgroups in an ambient two-local. -/
theorem exists_normalizer_rank_three (A B : Subgroup H)
    (hc : A ≤ centralizer (B : Set H))
    (hI : IsPGroup 3 (A ⊓ B : Subgroup H))
    {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (hA : 1 ≤ twoLocalPrimeRank p A) (hB : 2 ≤ primeRank p B) :
    ∃ R : Subgroup H, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      3 ≤ primeRank p (normalizer (R : Set H)) := by
  classical
  have hex : ∃ M : Subgroup A, IsTwoLocal M ∧ 1 ≤ primeRank p M := by
    by_contra! hn
    have hzero : twoLocalPrimeRank p A ≤ 0 :=
      (twoLocalPrimeRank_le_iff p 0).mpr (fun M hM => by have := hn M hM; omega)
    omega
  obtain ⟨M, ⟨Q, hQne, hQ, rfl⟩, hM⟩ := hex
  obtain ⟨E, hE, hEc⟩ := exists_elementaryAbelian_card_primeRank
    (G := normalizer (Q : Set A)) (p := p)
  obtain ⟨F, hF, hFc⟩ := exists_elementaryAbelian_card_primeRank (G := B) (p := p)
  let _ := hE
  let _ := hF
  let : CommGroup E := IsMulCommutative.instCommGroup
  let : CommGroup F := IsMulCommutative.instCommGroup
  let E' := E.map (normalizer (Q : Set A)).subtype
  have hrE : 1 ≤ primeRank p E' := by
    rw [← primeRank_equiv p
      (equivMapOfInjective E (normalizer (Q : Set A)).subtype Subtype.val_injective)]
    exact hM.trans (primeRank_ge_of_elementary_embedding
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E)) hEc (MonoidHom.id E) Function.injective_id)
  have hrF : 2 ≤ primeRank p F :=
    hB.trans (primeRank_ge_of_elementary_embedding
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p F)) hFc (MonoidHom.id F) Function.injective_id)
  obtain ⟨R, hRne, hR, hr⟩ := exists_normalizer_rank_sum A B hc hI hp3 Q E' F hQ hQne
    ((IsElementaryAbelian.isPGroup p E).map (normalizer (Q : Set A)).subtype)
    (map_subtype_le E)
  exact ⟨R, hRne, hR, by omega⟩

/-- Quasithinness excludes the constructed independent rank-three product. -/
theorem not_quasithin_of_local_and_ordinary_rank (A B : Subgroup H)
    (hc : A ≤ centralizer (B : Set H))
    (hI : IsPGroup 3 (A ⊓ B : Subgroup H))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hA : 1 ≤ twoLocalPrimeRank p A) (hB : 2 ≤ primeRank p B) :
    ¬ IsQuasithin H := by
  intro hH
  obtain ⟨R, hRne, hR, hr⟩ := exists_normalizer_rank_three A B hc hI hp3 hA hB
  have hl := isQuasithin_iff_twoLocal.mp hH (normalizer (R : Set H))
    ⟨R, hRne, hR, rfl⟩ p Fact.out ((Fact.out : p.Prime).odd_of_ne_two hp2)
  omega

end Theory.Quasithin.CubicIntersection

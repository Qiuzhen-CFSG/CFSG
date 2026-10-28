module

public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.SymmetricThreeSylowNormalizer
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual
public import Theory.SpecificGroups.SymmetricThreeProduct.NormalThreeSubgroups
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Sylow-invariant cubic directions in a normal symmetric-three span

A subgroup of the odd residual of S₃ or S₃ × S₃ that is invariant under
an ambient Sylow two-subgroup is normal inside the span: its residual
centralizes it and the Sylow intersection normalizes it. For a cubic
subgroup, the pair model has just two possible normal directions. Its
ambient conjugacy orbit therefore has size at most two and odd size,
so the subgroup is ambient normal.

Consequently a two-perfect Sylow-invariant subgroup of order dividing
3 times a power of two, if not normal, meets the odd residual trivially.
The actual covered L₀ application is in Chapter13 Section04's
Solvable/LocalProduct/CoveredIntersection extension.
Source: Aschbacher–Smith 13.4.8, the covered-row intersection argument,
printed p.905. Every normality assertion is relative to its stated group.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory.SymmetricThreeCubicNormality
variable {G : Type*} [Group G] [Finite G]
local notation "S3" => Equiv.Perm (Fin 3)

private theorem residual_commutative {D : Type*} [Group D]
    (hm : Nonempty (D ≃* S3) ∨ Nonempty (D ≃* (S3 × S3))) :
    IsMulCommutative (pResidual 2 D) := by
  rcases hm with he | he
  · obtain ⟨e⟩ := he
    have hc : Nat.card (pResidual 2 D) = 3 := by
      rw [← card_map_of_injective (K := pResidual 2 D) (f := e.toMonoidHom) e.injective,
        map_pResidual, Equiv.Perm.twoResidual_eq_alternating,
        nat_card_alternatingGroup, Nat.card_fin]
      rfl
    let : IsCyclic (pResidual 2 D) := isCyclic_of_prime_card hc
    infer_instance
  · obtain ⟨e⟩ := he
    apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
    rw [← card_map_of_injective (K := pResidual 2 D) (f := e.toMonoidHom) e.injective, map_pResidual]
    exact SymmetricThreeProductResidual.residual_card

private theorem normal_in_span (I B : Subgroup G) [I.Normal]
    (hm : Nonempty (I ≃* S3) ∨ Nonempty (I ≃* (S3 × S3)))
    (S : Sylow 2 G) (hB : B ≤ (pResidual 2 I).map I.subtype)
    (hS : (S : Subgroup G) ≤ normalizer (B : Set G)) :
    (B.subgroupOf I).Normal := by
  let := residual_commutative hm
  have hBI : B ≤ I := hB.trans (map_subtype_le _)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal I
  have hc : pResidual 2 I ≤ centralizer (B.subgroupOf I : Set I) := by
    intro x hx y hy
    have hyR : y ∈ pResidual 2 I := (mem_map_iff_mem I.subtype_injective).mp (hB hy)
    exact congrArg Subtype.val (mul_comm (⟨y,hyR⟩ : pResidual 2 I) ⟨x,hx⟩)
  have hs : (P : Subgroup I) ≤ normalizer (B.subgroupOf I : Set I) := by
    rw [hP, ← subgroupOf_normalizer_eq hBI]
    exact subgroupOf_mono I hS
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← pResidual_sup_sylow_eq_top P]
  exact sup_le (hc.trans (centralizer_le_normalizer _)) hs

omit [Finite G] in
private theorem pair_axes (I : Subgroup G) (e : I ≃* (S3 × S3))
    (B : Subgroup G) (hBI : B ≤ I) [(B.subgroupOf I).Normal]
    (hc : Nat.card B = 3) :
    B = (SymmetricThreeProduct.leftThree.comap e.toMonoidHom).map I.subtype ∨
    B = (SymmetricThreeProduct.rightThree.comap e.toMonoidHom).map I.subtype := by
  let A := (B.subgroupOf I).map e.toMonoidHom
  let : A.Normal := Normal.map inferInstance _ e.surjective
  have hcard : Nat.card A = 3 := by
    rw [card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hBI).toEquiv,hc]
  have hp : IsPPerfect 2 A := by
    apply (pResidual_eq_top_iff 2 A).mp
    apply top_unique
    intro a _
    have ho := orderOf_dvd_natCard a
    rw [hcard] at ho
    exact mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right ho)
  have hr := SymmetricThreeProduct.normal_twoPerfect_threePart A hp (by rw [hcard, Nat.Prime.factorization_self Nat.prime_three, pow_one])
  have hback : (A.comap e.toMonoidHom).map I.subtype = B := by
    rw [comap_map_eq_self_of_injective e.injective,map_subgroupOf_eq_of_le hBI]
  exact hr.imp (fun h => by rw [h] at hback; exact hback.symm)
    (fun h => by rw [h] at hback; exact hback.symm)

/-- A Sylow-invariant cubic in the odd residual is normal in the ambient group. -/
theorem cubic_normal_of_sylow_normalizes (I B : Subgroup G) [I.Normal]
    (hm : Nonempty (I ≃* S3) ∨ Nonempty (I ≃* (S3 × S3)))
    (S : Sylow 2 G) (hB : B ≤ (pResidual 2 I).map I.subtype)
    (hc : Nat.card B = 3)
    (hS : (S : Subgroup G) ≤ normalizer (B : Set G)) : B.Normal := by
  have hBI : B ≤ I := hB.trans (map_subtype_le _)
  let := normal_in_span I B hm S hB hS
  rcases hm with he | he
  · obtain ⟨e⟩ := he
    have hR : Nat.card ((pResidual 2 I).map I.subtype) = 3 := by
      rw [card_map_of_injective I.subtype_injective,
        ← card_map_of_injective (K := pResidual 2 I) (f := e.toMonoidHom) e.injective,
        map_pResidual, Equiv.Perm.twoResidual_eq_alternating,
        nat_card_alternatingGroup,Nat.card_fin]
      rfl
    have he : B = (pResidual 2 I).map I.subtype := eq_of_le_of_card_ge hB (by rw [hc,hR])
    rw [he]
    infer_instance
  · obtain ⟨e⟩ := he
    classical
    let A₁ := (SymmetricThreeProduct.leftThree.comap e.toMonoidHom).map I.subtype
    let A₂ := (SymmetricThreeProduct.rightThree.comap e.toMonoidHom).map I.subtype
    let : MulAction G (Subgroup G) := MulAction.compHom (Subgroup G) MulAut.conj
    have hpair (g : G) : g • B = A₁ ∨ g • B = A₂ := by
      let C := B.map (MulAut.conj g).toMonoidHom
      have hCI : C ≤ I := by
        rintro _ ⟨b,hb,rfl⟩
        exact (inferInstance : I.Normal).conj_mem b (hBI hb) g
      have heq : C.subgroupOf I =
          (B.subgroupOf I).map (MulAut.conjNormal g).toMonoidHom := by
        apply map_injective I.subtype_injective
        rw [map_subgroupOf_eq_of_le hCI,map_map]
        change B.map (MulAut.conj g).toMonoidHom = _
        rw [show I.subtype.comp (MulAut.conjNormal g).toMonoidHom =
          (MulAut.conj g).toMonoidHom.comp I.subtype from rfl,
          ← map_map,map_subgroupOf_eq_of_le hBI]
      have hn : (C.subgroupOf I).Normal := by
        rw [heq]
        exact Normal.map inferInstance _ (MulAut.conjNormal g).surjective
      let := hn
      exact pair_axes I e C hCI (by rw [card_map_of_injective (MulAut.conj g).injective,hc])
    have hcov : MulAction.orbit G B ⊆ ({A₁,A₂} : Set (Subgroup G)) := by
      rintro C ⟨g,rfl⟩
      exact hpair g
    have hidx : (MulAction.stabilizer G B).index ≤ 2 := by
      rw [MulAction.index_stabilizer]
      exact (Set.ncard_le_ncard hcov).trans (by simpa using Set.ncard_insert_le A₁ {A₂})
    have hs : (S : Subgroup G) ≤ MulAction.stabilizer G B := by
      intro s hs
      exact mem_normalizer_iff_map_conj_eq.mp (hS hs)
    have hodd : ¬ 2 ∣ (MulAction.stabilizer G B).index := fun hd =>
      S.not_dvd_index (hd.trans (index_dvd_of_le hs))
    have hpos := (MulAction.stabilizer G B).index_ne_zero_of_finite
    have htop : MulAction.stabilizer G B = ⊤ := index_eq_one.mp (by omega)
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (show g ∈ MulAction.stabilizer G B from htop ▸ mem_top _)

/-- A nonnormal two-perfect cubic section cannot meet the normal span’s odd residual. -/
theorem residual_disjoint_of_not_normal (I B : Subgroup G) [I.Normal]
    (hm : Nonempty (I ≃* S3) ∨ Nonempty (I ≃* (S3 × S3)))
    (S : Sylow 2 G) (hp : IsPPerfect 2 B)
    (horder : ∃ n : ℕ, Nat.card B ∣ 3 * 2 ^ n)
    (hS : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hn : ¬ B.Normal) : Disjoint ((pResidual 2 I).map I.subtype) B := by
  let R := (pResidual 2 I).map I.subtype
  let C := R ⊓ B
  have hR : IsPGroup 3 R := (SymmetricThreeSylowNormalizer.residual_threeGroup_of_models hm).map _
  have hC : IsPGroup 3 C := hR.to_le inf_le_left
  by_contra hd
  have hC1 : C ≠ ⊥ := fun h => hd (disjoint_iff.mpr h)
  obtain ⟨n,ho⟩ := horder
  obtain ⟨k,hk⟩ := hC.exists_card_eq
  have hcop : (Nat.card C).Coprime (2 ^ n) := by
    rw [hk]
    exact ((by decide : Nat.Coprime 3 2).pow_left k).pow_right n
  have hc3 : Nat.card C ∣ 3 := hcop.dvd_of_dvd_mul_right
    ((card_dvd_of_le (show C ≤ B from inf_le_right)).trans ho)
  have hc : Nat.card C = 3 := (Nat.prime_three.eq_one_or_self_of_dvd _ hc3).resolve_left
    (fun h => hC1 (card_eq_one.mp h))
  let D := C.subgroupOf B
  let : R.Normal := inferInstanceAs ((pResidual 2 I).map I.subtype).Normal
  let : D.Normal := by
    have he : D = R.subgroupOf B := by ext x; exact and_iff_left x.property
    rw [he]
    infer_instance
  have hD : Nat.card D = 3 := (Nat.card_congr (subgroupOfEquivOfLe
    (show C ≤ B from inf_le_right)).toEquiv).trans hc
  have hq : Nat.card (B ⧸ D) ∣ 2 ^ n := by
    have he := D.card_mul_index
    rw [hD,index_eq_card] at he
    rw [← he] at ho
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp ho
  have ht := hp D inferInstance (IsPGroup.of_card_dvd_pow hq)
  have hBC : B ≤ C := by
    intro b hb
    exact (show (⟨b,hb⟩ : B) ∈ D from ht ▸ mem_top _)
  have hBCeq : B = C := le_antisymm hBC inf_le_right
  apply hn
  exact cubic_normal_of_sylow_normalizes I B hm S (hBC.trans inf_le_left)
    (hBCeq ▸ hc) hS

end Theory.GroupTheory.SymmetricThreeCubicNormality

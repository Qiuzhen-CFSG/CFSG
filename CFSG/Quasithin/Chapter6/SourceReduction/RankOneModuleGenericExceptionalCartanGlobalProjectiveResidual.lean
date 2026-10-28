module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeDiagramApplication
public import Theory.SpecificGroups.PSL3.CartanActions.ProjectiveTorusRank
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalDegreeEight

/-!
# Projective residual tori in the Cartan normalization argument

The full Sylow normalizer in the literal residual maps to the original
maximal-local overlap. Its quotient by its own two-core is the two-parameter
unit torus modulo the cubic diagonal scalars. The coordinate isomorphism
with the units times their cubes proves the required rank bound, including
the cubic prime exactly when nine divides the unit order.

A zero-core prime actor bounds this same overlap's prime rank by one.
Consequently noncubic Fermat actors in the residual split torus are
excluded. An original cubic/quintic actor with n dividing the residual
degree f is forced to be cubic, with six not dividing f. Conversely, for
n = 2, 4 or 8, n dividing f and three dividing f give the actual Cartan
normalization conclusion. The existing nonprojective proofs then close
all diagram covering alternatives at these degrees.

The original SourceLocalCartanEscape input remains owned by the local
classification task. Diagram parabolic selection, the remaining field
comparisons, zero-core model exclusions and changed-Sylow assembly remain
with qt-d-1222-rankone-cartan-local-to-global. No general normalization or
field-degree equality is asserted here. The internal import reuses the
checked squarefree-order generation argument without changing its boundary.
Source: Aschbacher–Smith 5.1.6 and 5.2.2, printed pp.631–633,646–649
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

private theorem projective_normalizer_solvable {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f) (S : Sylow 2 PSL(3,F)) :
    Group.IsSolvable (normalizer (S : Set PSL(3,F))) := by
  let N := normalizer (S : Set PSL(3,F))
  let := (pCore_isPGroup (p := 2) (G := N)).isNilpotent
  let e := Matrix.PSL3.CartanActions.BorelQuotient.sylowNormalizerQuotientEquiv F hf hF S
  let : Group.IsSolvable (N ⧸ pCore 2 N) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  apply Group.isSolvable_of_ker_le_range (pCore 2 N).subtype (QuotientGroup.mk' (pCore 2 N))
  rw [QuotientGroup.ker_mk',range_subtype]

/-- The original residual Sylow normalizer lies in the literal overlap and
retains the projective cubic scalar quotient. -/
private theorem projective_residual_normalizer
    {T : Sylow 2 G} {L H : Subgroup G} {f : ℕ}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
      ∃ N : Subgroup (residual H),
        N.map (residual H).subtype ≤ normalizer (L : Set G) ⊓ H ∧
        Nonempty ((N ⧸ pCore 2 N) ≃* ((Fˣ × Fˣ) ⧸ Matrix.PSL3.CartanActions.BorelQuotient.cubicScalars F)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let K := residual H
  let eK : pResidual 2 H ≃* K :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let eqK := QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  let e0 := eqK.symm.trans e
  let q := e0.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e0.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    ext x
    exact e0.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K
    (hH.1.1.2.trans (le_normalizer_residual H))
  let N := normalizer (P : Set K)
  let S := P.mapSurjective hq
  have hmap : N.map q = normalizer (S : Set PSL(3,F)) := P.normalizer_map_surjective q hq
  let a := (q.subgroupMap N)
  have ha : IsPGroup 2 a.ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  let eN := a.quotientPCoreEquivOfSurjective (q.subgroupMap_surjective N) ha
  let eb := MulEquiv.subgroupCongr hmap
  let et := eN.trans ((QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)).trans
    (Matrix.PSL3.CartanActions.BorelQuotient.sylowNormalizerQuotientEquiv F
      (by omega) hF S))
  have hn : N ≠ ⊤ := by
    intro he
    have hs : normalizer (S : Set PSL(3,F)) = ⊤ := by
      rw [←hmap,he,map_top_of_surjective q hq]
    let : Group.IsSolvable (⊤ : Subgroup PSL(3,F)) :=
      hs ▸ projective_normalizer_solvable (by omega) hF S
    let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
    exact Group.IsPerfect.not_isSolvable PSL(3,F)
      (Group.isSolvable_of_surjective (f := (topEquiv (G := PSL(3,F))).toMonoidHom)
        (topEquiv (G := PSL(3,F))).surjective)
  let U := (T : Subgroup G) ⊓ K
  let J := H ⊓ normalizer (U : Set G)
  have hUK : U ≤ K := inf_le_right
  have heP : (P : Subgroup K) = U.subgroupOf K := by
    rw [hP]
    exact (inf_subgroupOf_right _ _).symm
  have hTJ : (T : Subgroup G) ≤ J := le_inf hH.1.1.2
    ((le_inf (T : Subgroup G).le_normalizer
      (hH.1.1.2.trans (le_normalizer_residual H))).trans inf_normalizer_le_normalizer_inf)
  have hJH : J < H := lt_of_le_of_ne inf_le_left (by
    intro he
    apply hn
    apply top_unique
    change ⊤ ≤ normalizer ((P : Subgroup K) : Set K)
    rw [heP,←subgroupOf_normalizer_eq hUK]
    intro x _
    exact (show H ≤ normalizer (U : Set G) from he ▸ inf_le_right)
      ((map_subtype_le (pResidual 2 H)) x.property))
  have hNM : N.map K.subtype ≤ normalizer (L : Set G) := by
    apply le_trans _ (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)
    apply le_inf
    · exact (map_subtype_le N).trans (map_subtype_le (pResidual 2 H))
    · change (normalizer ((P : Subgroup K) : Set K)).map K.subtype ≤ normalizer (U : Set G)
      rw [heP,←subgroupOf_normalizer_eq hUK]
      exact map_le_iff_le_comap.mpr le_rfl
  exact ⟨F,inferInstance,inferInstance,hF,N,
    le_inf hNM ((map_subtype_le N).trans (map_subtype_le (pResidual 2 H))),⟨et⟩⟩

/-- An escaping Fermat prime cannot occupy two independent directions in
 the projective residual torus. The cubic scalar defect is retained. -/
theorem CartanPair.projective_residual_fermat_not_dvd {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hp : p = 3 ∨ p = 5 ∨ p = 17) (hDA : D ≤ A) (hcard : Nat.card D = p)
    (hzero : (D ⊔ H).pCoreIn 2 = ⊥)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f))
    (hscalar : p ≠ 3 ∨ 9 ∣ 2 ^ f - 1) : ¬ p ∣ 2 ^ f - 1 := by
  intro hdiv
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> decide
  have ho : Odd p := by rcases hp with rfl | rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨F,_,_,hF,N,hNM,⟨e⟩⟩ := projective_residual_normalizer hH hf hm
  have hu := c.overlap_fermatRank_le_one h hp hDA hcard hzero hH.1.1.1
  have hr := primeRank_mono p hNM
  rw [← primeRank_equiv p (N.equivMapOfInjective (residual H).subtype
    (residual H).subtype_injective)] at hr
  have hl := primeRank_le_of_surjective_of_coprime p (QuotientGroup.mk' (pCore 2 N))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := N)).exists_card_eq
      rw [hk]
      exact (Nat.coprime_two_right.mpr ho).pow_right k)
  rw [primeRank_equiv p e] at hl
  have hb := Matrix.PSL3.CartanActions.BorelQuotient.projective_torus_primeRank_ge_two F
    (hF.symm ▸ hdiv) (hF.symm ▸ hscalar)
  omega

/-- A quintic or order-seventeen zero-core actor is excluded whenever its
prime divides the actual residual field's split torus. -/
theorem CartanPair.projective_residual_noncubic_fermat_not_dvd {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hp : p = 5 ∨ p = 17) (hDA : D ≤ A) (hcard : Nat.card D = p)
    (hzero : (D ⊔ H).pCoreIn 2 = ⊥)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    ¬ p ∣ 2 ^ f - 1 :=
  c.projective_residual_fermat_not_dvd h (.inr hp) hDA hcard hzero hH hf hm
    (.inl (by rcases hp with rfl | rfl <;> decide))

/-- Before normalization, the projective row leaves only the cubic actor
and a field degree not divisible by six. No equality of the field degrees is assumed. -/
theorem CartanPair.projective_residual_prime_constraints {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H p D)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hf : 1 < f) (hnf : n ∣ f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    p = 3 ∧ ¬ 9 ∣ 2 ^ f - 1 ∧ ¬ 6 ∣ f := by
  have hcard := (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  have hdvd : p ∣ 2 ^ f - 1 := by
    apply dvd_trans _ (Nat.pow_sub_one_dvd_pow_sub_one 2 hnf)
    rw [←hcard,←hd.card]
    exact card_dvd_of_le hd.le_cartan
  have hno := c.projective_residual_fermat_not_dvd h (hd.prime.imp_right Or.inl)
    hd.le_cartan hd.card hd.zero_core hH hf hm
  have hp : p = 3 := by
    by_contra hp
    exact hno (.inl hp) hdvd
  have h9 : ¬ 9 ∣ 2 ^ f - 1 := fun h9 => hno (.inr h9) hdvd
  exact ⟨hp,h9,fun h6 => h9 ((by decide : 9 ∣ 2 ^ 6 - 1).trans
    (Nat.pow_sub_one_dvd_pow_sub_one 2 h6))⟩

/-- All three original small degrees normalize the projective residual
when their degree divides f and the cubic scalar defect is absorbed by 9 | 2^f-1. -/
theorem Input.cartan_normalizes_of_projective_residual_small_degree {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n f : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hn : n = 2 ∨ n = 4 ∨ n = 8) (hf : 1 < f) (hnf : n ∣ f)
    (h9 : 9 ∣ 2 ^ f - 1)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    A ≤ normalizer (residual H : Set G) := by
  have hcard := (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  have hprime (p : ℕ) (hp : p = 3 ∨ p = 5 ∨ p = 17)
      (D : Subgroup G) (hDA : D ≤ A) (hD : Nat.card D = p) :
      D ≤ normalizer (residual H : Set G) := by
    apply hcontrol D hDA
    intro hzero
    apply c.projective_residual_fermat_not_dvd h hp hDA hD hzero hH hf hm (.inr h9)
    have hdvd : p ∣ 2 ^ n - 1 := by
      rw [←hcard,←hD]
      exact card_dvd_of_le hDA
    exact hdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hnf)
  rcases hn with hn | hn | hn
  · by_contra hnot
    obtain ⟨p,D,hd⟩ :=
      (cartanSmallGeneration_of_degree_two_or_four hH hcard (.inl hn)).exists_prime_actor hcontrol hnot
    exact h.prime_actor_not_normalizes hH hd
      (hprime p (hd.prime.imp_right Or.inl) D hd.le_cartan hd.card)
  · by_contra hnot
    obtain ⟨p,D,hd⟩ :=
      (cartanSmallGeneration_of_degree_two_or_four hH hcard (.inr hn)).exists_prime_actor hcontrol hnot
    exact h.prime_actor_not_normalizes hH hd
      (hprime p (hd.prime.imp_right Or.inl) D hd.le_cartan hd.card)
  · subst n
    exact card_255_le_of_prime_subgroups (by simpa using hcard) hprime

/-- Divisibility of the genuine field degrees discharges the scalar-order condition. -/
theorem Input.cartan_normalizes_of_projective_residual_cubic_degree {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n f : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hn : n = 2 ∨ n = 4 ∨ n = 8) (hf : 1 < f) (hnf : n ∣ f) (h3 : 3 ∣ f)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    A ≤ normalizer (residual H : Set G) := by
  have h2 : 2 ∣ f := (show 2 ∣ n by rcases hn with rfl | rfl | rfl <;> decide).trans hnf
  have h6 : 6 ∣ f := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3
  have h9 : 9 ∣ 2 ^ f - 1 :=
    (by decide : 9 ∣ 2 ^ 6 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 h6)
  exact h.cartan_normalizes_of_projective_residual_small_degree hH c hcontrol hn hf hnf h9 hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- Every diagram covering alternative gives normalization at the indicated
original and residual degrees, with the projective scalar obstruction discharged. -/
theorem Input.cartan_normalizes_of_diagram_cubic_degree
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n f : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hn : n = 2 ∨ n = 4 ∨ n = 8) (hnf : n ∣ f) (h3 : 3 ∣ f)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    (hm : DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) f) :
    A ≤ normalizer (residual H : Set G) := by
  by_cases hproj : ClassicalGroup.IsPSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)
  · exact h.cartan_normalizes_of_projective_residual_cubic_degree hH c hcontrol hn hf hnf h3 hproj
  · exact h.cartan_normalizes_of_nonprojective_diagram_small_degree hH hpar c hcontrol
      hn hnf hC hqs hc hf hm hproj
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

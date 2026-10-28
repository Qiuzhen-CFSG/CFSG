module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeHallRank
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
public import Theory.GroupTheory.SylowNormalizerCentralQuotient

/-!
# Cartan normalization with a genuine special-linear residual

The normalizer of a full Sylow in the literal residual has quotient
Fˣ × Fˣ by its two-core. The relative normalizer in H is proper: its
image is the solvable SL₃ Sylow normalizer, whereas SL₃ is perfect and
nontrivial. The H-star property therefore puts this normalizer in the
original overlap N_G(L) ∩ H.

At any prime dividing |F|−1 this constructs two independent directions
in that overlap. An escaping cubic or quintic actor leaves at most one
by the original quasithin rank bound, giving a contradiction. Thus local
Cartan control gives residual normalization when the original degree is
two or four and divides the residual degree. No projective identification,
Borel-marking assumption or equality of the two field degrees is used.
The remaining degrees and source rows retain their local-to-global owner.

Source: Aschbacher–Smith 5.1.10 and 5.2.2, printed pp.634,648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

private theorem linear_normalizer_solvable {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f) (S : Sylow 2 SL(3,F)) :
    Group.IsSolvable (normalizer (S : Set SL(3,F))) := by
  let N := normalizer (S : Set SL(3,F))
  let := (pCore_isPGroup (p := 2) (G := N)).isNilpotent
  let e := Matrix.PSL3.CartanActions.BorelQuotient.sylowSLNormalizerQuotientEquiv F hf hF S
  let : Group.IsSolvable (N ⧸ pCore 2 N) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  apply Group.isSolvable_of_ker_le_range (pCore 2 N).subtype (QuotientGroup.mk' (pCore 2 N))
  rw [QuotientGroup.ker_mk',range_subtype]

/-- The original residual Sylow normalizer lies in the literal overlap and
has the full two-parameter torus quotient of SL₃. -/
private theorem specialLinear_residual_normalizer
    {T : Sylow 2 G} {L H : Subgroup G} {f : ℕ}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hf : 1 < f)
    (hm : Chapter1.Section02.LocalModels.IsSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
      ∃ N : Subgroup (residual H),
        N.map (residual H).subtype ≤ normalizer (L : Set G) ⊓ H ∧
        Nonempty ((N ⧸ pCore 2 N) ≃* (Fˣ × Fˣ)) := by
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
  have hmap : N.map q = normalizer (S : Set SL(3,F)) := P.normalizer_map_surjective q hq
  let a := (q.subgroupMap N)
  have ha : IsPGroup 2 a.ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  let eN := a.quotientPCoreEquivOfSurjective (q.subgroupMap_surjective N) ha
  let eb := MulEquiv.subgroupCongr hmap
  let et := eN.trans ((QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)).trans
    (Matrix.PSL3.CartanActions.BorelQuotient.sylowSLNormalizerQuotientEquiv F
      (by omega) hF S))
  have hn : N ≠ ⊤ := by
    intro he
    have hs : normalizer (S : Set SL(3,F)) = ⊤ := by
      rw [←hmap,he,map_top_of_surjective q hq]
    let : Group.IsSolvable (⊤ : Subgroup SL(3,F)) :=
      hs ▸ linear_normalizer_solvable (by omega) hF S
    let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
    let : Nontrivial SL(3,F) := Function.Surjective.nontrivial (Matrix.PSL3.projection_surjective F)
    exact Group.IsPerfect.not_isSolvable SL(3,F)
      (Group.isSolvable_of_surjective (f := (topEquiv (G := SL(3,F))).toMonoidHom)
        (topEquiv (G := SL(3,F))).surjective)
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

/-- The genuine SL₃ residual excludes any escaping prime in its split torus. -/
theorem CartanPair.specialLinear_residual_prime_not_dvd {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H p D)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hf : 1 < f)
    (hm : Chapter1.Section02.LocalModels.IsSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) : ¬ p ∣ 2 ^ f - 1 := by
  intro hdiv
  have hp : p.Prime := by rcases hd.prime with rfl | rfl <;> decide
  have ho : Odd p := by rcases hd.prime with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,N,hNM,⟨e⟩⟩ := specialLinear_residual_normalizer hH hf hm
  have hu := c.overlap_primeRank_le_one h hd hH.1.1.1
  have hr := primeRank_mono p hNM
  rw [← primeRank_equiv p (N.equivMapOfInjective (residual H).subtype
    (residual H).subtype_injective)] at hr
  have hl := primeRank_le_of_surjective_of_coprime p (QuotientGroup.mk' (pCore 2 N))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := N)).exists_card_eq
      rw [hk]
      exact (Nat.coprime_two_right.mpr ho).pow_right k)
  rw [primeRank_equiv p e,primeRank_prod_eq_add] at hl
  have hdvd : p ∣ Nat.card Fˣ := by rwa [Nat.card_units,hF]
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hdvd
  let E := zpowers x
  have hE : Nat.card E = p := (Nat.card_zpowers x).trans hx
  have hpos : 1 ≤ primeRank p Fˣ := primeRank_ge_of_elementary_embedding
    (fun y : E => by simpa only [hE] using pow_card_eq_one' (x := y))
    (by simpa using hE) E.subtype E.subtype_injective
  omega

/-- The special-linear cover supplies normalization in each original small degree
which divides the residual degree, with no Borel-marking assumption. -/
theorem Input.cartan_normalizes_of_specialLinear_residual_small_degree {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n f : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hn : n = 2 ∨ n = 4) (hf : 1 < f) (hnf : n ∣ f)
    (hm : Chapter1.Section02.LocalModels.IsSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    A ≤ normalizer (residual H : Set G) := by
  by_contra hnot
  have hcard := (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  have hs := cartanSmallGeneration_of_degree_two_or_four hH hcard hn
  obtain ⟨p,D,hd⟩ := hs.exists_prime_actor hcontrol hnot
  apply c.specialLinear_residual_prime_not_dvd h hd hH hf hm
  have hdvd : p ∣ 2 ^ n - 1 := by
    rw [←hcard,←hd.card]
    exact card_dvd_of_le hd.le_cartan
  exact hdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hnf)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

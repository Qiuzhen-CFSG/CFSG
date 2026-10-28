module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics

/-!
# Replacement and the full pushing-up product in 13.6.18

Equal star images preserve the seed span and its moving commutator. A minimal
member of the local family exists by finiteness. The rank-one geometry must
still show that its star image is unchanged and that its actual overgroup is
minimal parabolic.

For the pushing-up step, the local C-component condition identifies the whole
component with a factor of C.1.26's central product: otherwise every factor is
a proper subnormal, hence solvable, subgroup, and their normal join is solvable.
This avoids assuming a quasisimple two-core quotient for the replacement.
Perfectness excludes the A₃ block. The A₅ module alternative is retained until
its action is compared with 13.6.15; its group name alone does not exclude it.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.18, printed p.931 (PDF p.948); A.3.1–3 and C.1.26.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement
open Subgroup Theory.GroupTheory ComponentSelection
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
open HigherFieldParabolics

universe u
variable {G : Type u} [Group G]

/-- Equality of the faithful star images preserves the actual seed span. -/
theorem seedSpan_eq_of_starImage_eq (K₀ K L : Subgroup G) (z v : G)
    (h₀ : K₀ ≤ Gv v) (hK : K ≤ Gv v)
    (he : starImage z v K₀ = starImage z v K) :
    conjugateSpanBy (zpowers z) (K₀ ⊔ Lv L v) =
      conjugateSpanBy (zpowers z) (K ⊔ Lv L v) := by
  rw [← seedSpan_starPreimage_starImage K₀ L z v h₀, he,
    seedSpan_starPreimage_starImage K L z v hK]

/-- For invariant local components the source W_K itself is unchanged. -/
theorem WK_eq_of_starImage_eq (K₀ K L T : Subgroup G) (z v : G)
    (h₀ : K₀ ≤ Gv v) (hK : K ≤ Gv v)
    (hn₀ : Tv T v ≤ normalizer (K₀ : Set G))
    (hnK : Tv T v ≤ normalizer (K : Set G))
    (he : starImage z v K₀ = starImage z v K) :
    WK K₀ L T z v = WK K L T z v := by
  rw [WK, WK, Kminus_eq_of_invariant K₀ T v hn₀,
    Kminus_eq_of_invariant K T v hnK]
  exact seedSpan_eq_of_starImage_eq K₀ K L z v h₀ hK he

/-- Equal star images give the same moving subgroup, not just isomorphic
abstract modules. Membership of the replacement is derived using the local
family observation, and U_K is identified by 13.6.14's transport theorem. -/
theorem replacement_module_eq (K₀ K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (h₀ : K₀ ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hn₀ : Tv T v ≤ normalizer (K₀ : Set G))
    (hnK : Tv T v ≤ normalizer (K : Set G))
    (he : starImage z v K₀ = starImage z v K) :
    K₀ ∈ Yz L T z v ∧ WK K₀ L T z v = WK K L T z v ∧
      ⁅WK K₀ L T z v, K₀⁆ = ⁅WK K L T z v, K⁆ := by
  have hY := mem_Yz_of_starImage_eq L T z v hK h₀ he
  refine ⟨hY, WK_eq_of_starImage_eq K₀ K L T z v h₀.1 hK.1.1 hn₀ hnK he, ?_⟩
  rw [← (invariant_component_consequences K₀ L T z v hY hn₀).2, he,
    (invariant_component_consequences K L T z v hK hnK).2]

variable [Finite G]

/-- The source's minimal choice exists in the literal local family inside
KT_v. This does not yet assert its image or its parabolic geometry. -/
theorem exists_minimal_local (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v) :
    ∃ K₀ : Subgroup G, K₀ ≤ K ∧
      Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀ := by
  exact exists_minimal_le_of_wellFoundedLT _ K ⟨le_sup_left, hK.1.2⟩

private theorem component_mem_centralProduct {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) (hK : K.IsCComponent)
    (F : Set (Subgroup H)) (hgen : sSup F = K)
    (hcomm : F.Pairwise fun A B => ⁅A, B⁆ = ⊥) : K ∈ F := by
  classical
  have hle (A : Subgroup H) (hA : A ∈ F) : A ≤ K := hgen ▸ le_sSup hA
  have hn (A : Subgroup H) (hA : A ∈ F) : (A.subgroupOf K).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer (hle A hA)).mpr
    rw [← hgen]
    apply sSup_le
    intro B hB
    by_cases he : A = B
    · subst B; exact A.le_normalizer
    · exact le_normalizer_iff_commutator_le_left.mpr (by
        rw [hcomm hA hB he]; exact bot_le)
  by_contra hnot
  have hr (A : Subgroup H) (hA : A ∈ F) : A.subgroupOf K ≤ solvableRadical K := by
    have hp : A.subgroupOf K ≠ ⊤ := by
      intro ht
      have he : A = K := le_antisymm (hle A hA) (subgroupOf_eq_top.mp ht)
      exact hnot (he ▸ hA)
    exact le_solvableRadical _ (hn A hA)
      (hK.isSolvable_of_subnormal_lt_top (hn A hA).isSubnormal hp)
  have hall : K ≤ (solvableRadical K).map K.subtype := by
    apply hgen.ge.trans
    apply sSup_le
    intro A hA x hx
    exact ⟨⟨x, hle A hA hx⟩, hr A hA hx, rfl⟩
  have ht : solvableRadical K = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, hy, he⟩ := hall x.property
    exact (show y = x from Subtype.ext he) ▸ hy
  have hs : Group.IsSolvable (⊤ : Subgroup K) := ht ▸ inferInstance
  let := hs
  exact hK.not_isSolvable
    (Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup K) ≃* K).toMonoidHom)
      (topEquiv : (⊤ : Subgroup K) ≃* K).surjective)

private theorem perfect_twoPerfect (K : Subgroup G) [Group.IsPerfect K] :
    IsPPerfect 2 K := by
  intro N hN hp
  let := hN
  by_contra hn
  let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
  exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent

/-- The actual local component is a factor of the full residual product.
No quasisimplicity of K/O₂(K), factor choice, or single-block assertion is
an additional input. -/
theorem local_mem_factors (S K : Subgroup G) (hlocal : K ∈ Chapter1.L G S)
    (hn : S ≤ normalizer (K : Set G)) (P : Sylow 2 (K ⊔ S : Subgroup G))
    (b : ResidualBlockProduct (K ⊔ S : Subgroup G) P) :
    K.subgroupOf (K ⊔ S) ∈ b.factors := by
  let := Chapter1.mem_L_isPerfect hlocal
  have hres : (pResidual 2 (K ⊔ S : Subgroup G)).map (K ⊔ S).subtype = K :=
    embedded_pResidual_join_pGroup K S (perfect_twoPerfect K)
      (Chapter1.isSylowIn_iff.mp hlocal.2.1).1 hn
  apply component_mem_centralProduct _ hlocal.1 b.factors _ b.commute
  apply map_injective (K ⊔ S).subtype_injective
  rw [b.generate, hres, map_subgroupOf_eq_of_le le_sup_left]

/-- The full transitive product has just this factor: K is normalized by S,
so its orbit under the specified Sylow subgroup is a singleton. -/
theorem local_factors_eq_singleton (S K : Subgroup G) (hlocal : K ∈ Chapter1.L G S)
    (hn : S ≤ normalizer (K : Set G)) (P : Sylow 2 (K ⊔ S : Subgroup G))
    (b : ResidualBlockProduct (K ⊔ S : Subgroup G) P) :
    b.factors = {K.subgroupOf (K ⊔ S)} := by
  let H := K ⊔ S
  let A := K.subgroupOf H
  have hmem := local_mem_factors S K hlocal hn P b
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer
    (show K ≤ H from le_sup_left)).mpr (sup_le K.le_normalizer hn)
  apply Set.Subset.antisymm
  · intro B hB
    obtain ⟨t, ht⟩ := b.transitive A hmem B hB
    have he : A.map (MulAut.conj (t : H)).toMonoidHom = A :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top _)
    exact Set.mem_singleton_iff.mpr (ht.symm.trans he)
  · exact Set.singleton_subset_iff.mpr hmem

private theorem not_alternating_three {H : Type*} [Group H] [Group.IsPerfect H] :
    ¬ ChapterC.IsAlternatingBlock H 3 := by
  intro h
  obtain ⟨e⟩ := h.2.2.quotient_iso
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : Group.IsPerfect (alternatingGroup (Fin 3)) :=
    Group.IsPerfect.ofSurjective (f := f)
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact Group.IsPerfect.not_isMulCommutative (alternatingGroup (Fin 3))
    (alternatingGroup.isMulCommutative_of_card_le_three (by simp))

/-- Resolve the central product and its A₃ alternative for the actual
local overgroup. The remaining A₅ alternative specifies its permutation
module and cannot be removed by the abstract rank-one group name. -/
theorem block_alternatives_of_C126 {𝒦 : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (S K : Subgroup G) (hlocal : K ∈ Chapter1.L G S)
    (hn : S ≤ normalizer (K : Set G))
    (hpush : CharacteristicNormalizerObstruction S K)
    (hsqtk : IsSQTK 𝒦 (K ⊔ S : Subgroup G))
    (hf : generalizedFitting (K ⊔ S : Subgroup G) = pCore 2 (K ⊔ S : Subgroup G))
    (hpar : ∀ P : Sylow 2 (K ⊔ S : Subgroup G),
      (P : Subgroup (K ⊔ S : Subgroup G)).map (K ⊔ S).subtype = S →
      ChapterB.IsMinimalParabolicOver P ⊤) :
    ChapterC.IsBlock (K.subgroupOf (K ⊔ S)) ∧
      ((∃ n, ChapterC.IsL2EvenBlock K n) ∨ ChapterC.IsAlternatingBlock K 5) := by
  obtain ⟨P, hP⟩ := hlocal.2.1
  let : Nontrivial P := sylow_nontrivial_of_minimalParabolic P (hpar P hP)
  obtain ⟨b⟩ := blockProduct_of_characteristic_exclusion P (choices.pair P P.isPGroup')
    (source _ hsqtk hf P (hpar P hP))
    (characteristic_exclusion_transport P hP (characteristic_exclusion S K hpush))
  have hmem : K.subgroupOf (K ⊔ S) ∈ b.factors := by
    rw [local_factors_eq_singleton S K hlocal hn P b]
    exact Set.mem_singleton _
  have hb := b.block _ hmem
  let e : K.subgroupOf (K ⊔ S) ≃* K := subgroupOfEquivOfLe le_sup_left
  refine ⟨hb.1, ?_⟩
  rcases hb.2 with ⟨n, hn⟩ | hthree | hfive
  · exact Or.inl ⟨n, hn.of_mulEquiv e⟩
  · let := Chapter1.mem_L_isPerfect hlocal
    exact (not_alternating_three (hthree.of_mulEquiv e)).elim
  · exact Or.inr (hfive.of_mulEquiv e)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement

end

module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Quotients
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Factors.Transport
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.SolvableRadical

/-!
# Moving residuals and the pushing-up obstruction for 13.6.19

Generation in the literal plus quotient detects movement of the seed: its
kernel centralizes W_K and hence z. The characteristic-normalizer strictness
of 13.6.16(2) excludes both characteristic alternatives of C.1.26, with
normality taken inside K₁Tᵥ. A quasisimple core quotient identifies the residual
with a factor of the remaining central product, so it is a short group.

These are conditional assembly tools. The three higher-field model branches
must still construct their parabolics, local membership, core quotients,
minimal-parabolic geometry and failure of shortness from the marked action.
In particular no non-block assertion about an abstract matrix parabolic is
assumed to describe its preimage in the source group.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 13.6.16(2) and
13.6.19, printed pp.930–931; C.1.7 and C.1.26, pp.123 and 132.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics
open ComponentSelection
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
universe u
variable {G : Type u} [Group G]

/-- P∞, embedded back into the original group. -/
abbrev residualIn (P : Subgroup G) : Subgroup G :=
  (solvableResidual P).map P.subtype

/-- The strict product assertion of 13.6.16(2), with the characteristic
subgroup intrinsic to S and its normalizer taken in K. -/
def CharacteristicNormalizerObstruction (S K : Subgroup G) : Prop :=
  ∀ C : Subgroup S, C.Characteristic → C ≠ ⊥ →
    (solvableRadical K).map K.subtype ⊔
      (K ⊓ normalizer (C.map S.subtype : Set G)) < K

private theorem le_of_map_le_map_of_kernel_le {A B : Type*} [Group A] [Group B]
    (f : A →* B) (X C : Subgroup A) (hk : f.ker ≤ C)
    (h : X.map f ≤ C.map f) : X ≤ C := by
  have hc := (map_le_iff_le_comap).mp h
  rw [comap_map_eq, sup_eq_left.mpr hk] at hc
  exact hc

private theorem component_le_actor (K L T : Subgroup G) (v : G) :
    K ≤ plusActor K L T v :=
  (le_conjugateSpanBy K (Tv T v)).trans (le_sup_left.trans le_sup_left)

/-- Generation by the images of two subgroups forces one to move z.
Images are restricted to the actual plus actor; the kernel is discharged
using z ∈ W_K, rather than a faithfulness assumption on K. -/
theorem moves_of_plus_generation (K L T A B : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hgen : plusImage K L T z v hL hz K ≤
      plusImage K L T z v hL hz A ⊔ plusImage K L T z v hL hz B)
    (hm : ¬ K ≤ centralizer ({z} : Set G)) :
    ¬ A ≤ centralizer ({z} : Set G) ∨ ¬ B ≤ centralizer ({z} : Set G) := by
  classical
  by_contra h
  push Not at h
  let H := plusActor K L T v
  let C := (centralizer ({z} : Set G)).subgroupOf H
  let f := plusMk K L T z v hL hz
  have hker : f.ker ≤ C := by
    rw [plusMk_ker]
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (hx z (le_conjugateSpanBy _ _ (mem_zpowers z))).symm
  have him : (K.subgroupOf H).map f ≤ C.map f :=
    hgen.trans (sup_le (map_mono (comap_mono h.1)) (map_mono (comap_mono h.2)))
  have hKC := le_of_map_le_map_of_kernel_le f (K.subgroupOf H) C hker him
  exact hm (by
    intro k hk
    exact hKC (show (⟨k, component_le_actor K L T v hk⟩ : H) ∈ K.subgroupOf H from hk))

/-- Application to the two maximal-parabolic residuals. The model owner
supplies generation, not a moving residual witness. -/
theorem moving_residual_of_plus_generation (K L T P Q : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hP : P ≤ K) (hQ : Q ≤ K)
    (hgen : plusImage K L T z v hL hz K ≤
      plusImage K L T z v hL hz (residualIn P) ⊔
        plusImage K L T z v hL hz (residualIn Q))
    (hm : ¬ K ≤ centralizer ({z} : Set G)) :
    ∃ R ∈ ({P, Q} : Set (Subgroup G)),
      R ≤ K ∧ ¬ residualIn R ≤ centralizer ({z} : Set G) := by
  rcases moves_of_plus_generation K L T (residualIn P) (residualIn Q) z v hL hz
    hgen hm with h | h
  · exact ⟨P, by simp, hP, h⟩
  · exact ⟨Q, by simp, hQ, h⟩

/-- Source strictness forbids normality in KS of every nontrivial
characteristic subgroup of S. This keeps the original embedding of S. -/
theorem characteristic_exclusion (S K : Subgroup G)
    (h : CharacteristicNormalizerObstruction S K) :
    ∀ C : Subgroup S, C.Characteristic → C ≠ ⊥ →
      ¬ ((C.map S.subtype).subgroupOf (K ⊔ S)).Normal := by
  intro C hC hne hn
  have hle : C.map S.subtype ≤ K ⊔ S := (map_subtype_le _).trans le_sup_right
  have hn' := (normal_subgroupOf_iff_le_normalizer hle).mp hn
  have hK : K ≤ normalizer (C.map S.subtype : Set G) := le_sup_left.trans hn'
  exact (not_le_of_gt (h C hC hne))
    (le_sup_of_le_right (le_inf le_rfl hK))

/-- A nonzero triple commutator in two actual core subgroups obstructs
C.1.7's centrality clause. This criterion is suitable for a marked module
calculation in the preimage of a matrix parabolic. -/
theorem not_short_of_core_triple (K U Q : Subgroup G)
    (hU : U ≤ K.pCoreIn 2) (hQ : Q ≤ K.pCoreIn 2)
    (hne : ⁅⁅U, K⁆, Q⁆ ≠ ⊥) : ¬ ChapterC.IsShort K := by
  intro h
  have hc : ⁅ChapterC.blockU K, pCore 2 K⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr h.central
  have hm := congrArg (Subgroup.map K.subtype) hc
  rw [map_commutator, Subgroup.map_bot] at hm
  have hUK : ⁅U, K⁆ ≤ (ChapterC.blockU K).map K.subtype := by
    rw [ChapterC.blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact commutator_mono hU le_rfl
  exact hne (bot_unique ((commutator_mono hUK hQ).trans hm.le))

/-- The same obstruction rules out being a block in any given ambient
group, without confusing its intrinsic core with the ambient two-core. -/
theorem not_block_of_core_triple (K U Q : Subgroup G)
    (hU : U ≤ K.pCoreIn 2) (hQ : Q ≤ K.pCoreIn 2)
    (hne : ⁅⁅U, K⁆, Q⁆ ≠ ⊥) : ¬ ChapterC.IsBlock K :=
  fun h => not_short_of_core_triple K U Q hU hQ hne h.short

private theorem perfect_twoPerfect [Finite G] (K : Subgroup G) [Group.IsPerfect K] :
    IsPPerfect 2 K := by
  intro N hN hp
  let := hN
  by_contra hn
  let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
  exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent

private theorem member_eq_join {H : Type*} [Group H]
    (K : Subgroup H) (F : Set (Subgroup H)) (hgen : sSup F = K)
    (hcomm : F.Pairwise fun A B => ⁅A, B⁆ = ⊥)
    (hp : IsPPerfect 2 K) [IsQuasisimple (K ⧸ pCore 2 K)] : K ∈ F := by
  classical
  let Q := K ⧸ pCore 2 K
  let q : K →* Q := QuotientGroup.mk' (pCore 2 K)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
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
  have hc (A : Subgroup H) (hA : A ∈ F) : (A.subgroupOf K).map q ≤ center Q := by
    let := hn A hA
    let : ((A.subgroupOf K).map q).Normal := (hn A hA).map q hq
    rcases IsQuasisimple.normal_le_center_or_eq_top ((A.subgroupOf K).map q) with hc | ht
    · exact hc
    · have hs : A.subgroupOf K ⊔ pCore 2 K = ⊤ := by
        have he := congrArg (Subgroup.comap q) ht
        have hk : q.ker = pCore 2 K := QuotientGroup.ker_mk' _
        simpa only [comap_map_eq, hk, comap_top] using he
      have he := hp (A.subgroupOf K) (hn A hA)
        (isPGroup_quotient_of_sup_eq_top _ _ pCore_isPGroup hs)
      have he' : A = K := le_antisymm (hle A hA) (subgroupOf_eq_top.mp he)
      exact (hnot (he' ▸ hA)).elim
  have hK : K ≤ ((center Q).comap q).map K.subtype := by
    apply hgen.ge.trans
    apply sSup_le
    intro A hA x hx
    exact ⟨⟨x, hle A hA hx⟩,
      hc A hA (mem_map_of_mem q (show (⟨x, hle A hA hx⟩ : K) ∈ A.subgroupOf K from hx)), rfl⟩
  have hz : center Q = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := hq y
    obtain ⟨w, hw, he⟩ := hK x.property
    exact (show w = x from Subtype.ext he) ▸ hw
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  exact Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hz)

/-- C.1.26 applied inside K₁Tᵥ, including elimination of both characteristic
branches and identification of the whole residual in the block product.
Minimal parabolicity and the intrinsic core quotient remain explicit model
obligations; the result does not infer them from a plus-quotient isomorphism. -/
theorem short_of_C126 [Finite G] {𝒦 : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (S K : Subgroup G) (hlocal : K ∈ Chapter1.L G S)
    (hSK : S ≤ normalizer (K : Set G))
    (hpush : CharacteristicNormalizerObstruction S K)
    (hsqtk : IsSQTK 𝒦 (K ⊔ S : Subgroup G))
    (hf : generalizedFitting (K ⊔ S : Subgroup G) = pCore 2 (K ⊔ S : Subgroup G))
    (hpar : ∀ P : Sylow 2 (K ⊔ S : Subgroup G),
      (P : Subgroup (K ⊔ S : Subgroup G)).map (K ⊔ S).subtype = S →
      ChapterB.IsMinimalParabolicOver P ⊤)
    [IsQuasisimple (K ⧸ pCore 2 K)] : ChapterC.IsShort K := by
  let := Chapter1.mem_L_isPerfect hlocal
  obtain ⟨P, hP⟩ := hlocal.2.1
  let : Nontrivial P := sylow_nontrivial_of_minimalParabolic P (hpar P hP)
  obtain ⟨b⟩ := blockProduct_of_characteristic_exclusion P (choices.pair P P.isPGroup')
    (source _ hsqtk hf P (hpar P hP))
    (characteristic_exclusion_transport P hP (characteristic_exclusion S K hpush))
  let H := K ⊔ S
  let e : K ≃* K.subgroupOf H := (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).symm
  let : IsQuasisimple ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hres : (pResidual 2 H).map H.subtype = K :=
    embedded_pResidual_join_pGroup K S (perfect_twoPerfect K)
      (Chapter1.isSylowIn_iff.mp hlocal.2.1).1 hSK
  have hgen : sSup b.factors = K.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [b.generate, hres, map_subgroupOf_eq_of_le le_sup_left]
  have hmem := member_eq_join _ b.factors hgen b.commute
    ((perfect_twoPerfect K).of_surjective e.toMonoidHom e.surjective)
  exact (b.block _ hmem).1.short.of_mulEquiv e.symm

/-- The terminal C.1.26 obstruction for a moving member of the literal
local family. The construction of the non-short residual is separate. -/
theorem false_of_moving_local_nonshort [Finite G] {𝒦 : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (T K : Subgroup G) (z v : G)
    (hlocal : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hSK : Tv T v ≤ normalizer (K : Set G))
    (hm : ¬ K ≤ centralizer ({z} : Set G))
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      CharacteristicNormalizerObstruction (Tv T v) D)
    (hsqtk : IsSQTK 𝒦 (K ⊔ Tv T v : Subgroup G))
    (hf : generalizedFitting (K ⊔ Tv T v : Subgroup G) = pCore 2 (K ⊔ Tv T v : Subgroup G))
    (hpar : ∀ P : Sylow 2 (K ⊔ Tv T v : Subgroup G),
      (P : Subgroup (K ⊔ Tv T v : Subgroup G)).map (K ⊔ Tv T v).subtype = Tv T v →
      ChapterB.IsMinimalParabolicOver P ⊤)
    [IsQuasisimple (K ⧸ pCore 2 K)] (hn : ¬ ChapterC.IsShort K) : False :=
  hn (short_of_C126 choices source (Tv T v) K hlocal.2 hSK
    (h16 K hlocal hSK hm) hsqtk hf hpar)

/-- A marked core-action calculation on P∞ feeds the source obstruction
directly. No non-block premise is needed in this consumer. The model branches
must construct the parabolic and the nonzero triple commutator. -/
theorem false_of_moving_residual_core_triple [Finite G] {𝒦 : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (T P U Q : Subgroup G) (z v : G)
    (hlocal : residualIn P ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hSK : Tv T v ≤ normalizer (residualIn P : Set G))
    (hm : ¬ residualIn P ≤ centralizer ({z} : Set G))
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      CharacteristicNormalizerObstruction (Tv T v) D)
    (hsqtk : IsSQTK 𝒦 (residualIn P ⊔ Tv T v : Subgroup G))
    (hf : generalizedFitting (residualIn P ⊔ Tv T v : Subgroup G) =
      pCore 2 (residualIn P ⊔ Tv T v : Subgroup G))
    (hpar : ∀ S : Sylow 2 (residualIn P ⊔ Tv T v : Subgroup G),
      (S : Subgroup (residualIn P ⊔ Tv T v : Subgroup G)).map
        (residualIn P ⊔ Tv T v).subtype = Tv T v → ChapterB.IsMinimalParabolicOver S ⊤)
    [IsQuasisimple (residualIn P ⧸ pCore 2 (residualIn P))]
    (hU : U ≤ (residualIn P).pCoreIn 2) (hQ : Q ≤ (residualIn P).pCoreIn 2)
    (hne : ⁅⁅U, residualIn P⁆, Q⁆ ≠ ⊥) : False :=
  false_of_moving_local_nonshort choices source T (residualIn P) z v hlocal hSK hm
    h16 hsqtk hf hpar (not_short_of_core_triple (residualIn P) U Q hU hQ hne)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics
end

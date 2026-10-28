module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWeakClosure
public import Theory.Representation.HermitianTensorThree.Involutions

/-!
# The zero weak-closure alternative at field four

An actor in the third fixed-space family cannot have rank three: removing
two generators leaves an involution with the same fixed space, but its
codimension is at most four whereas a rank-three actor has codimension at
least five. The automizer two-rank bound therefore forces rank four, and
the outer-centralizer bound places that actor in the original inner image.

If weak closure is zero, the paired-action theorem would contradict r >= 4.
The initial bound r >= 3 thus forces r = s = 3. A returning whole conjugate
supplies the third-family actor above. Since the conjugate has rank nine,
its centralizer kernel has rank five. The Chapter 12 consumer retains this
case explicitly alongside the actual parameter-one selections. Eliminating
it requires the field-four source argument; the higher-field bound does not
settle it.

Source: Aschbacher--Smith E.3.10, E.3.28, H.4.4, 7.3.2 and 7.5.6,
pp.232--238,381,698,701, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE
variable {G : Type*} [Group G] [Finite G]
  (V : Subgroup G) [IsElementaryAbelian 2 V]
  (e : Additive V ≃ₗ[ZMod 2] Space 1)
  (j : Automizer V →* binaryNormalizer 1) (hj : Function.Injective j)
  (he : ∀ a v, e (automizerRepresentation V a v) =
    overgroupAction 1 (binaryNormalizer 1) (j a) (e v))

include hj he in
/-- Every third-family actor at field four is a maximal inner elementary actor. -/
theorem field_four_fixed_family_three_rank
    (A : Subgroup (Automizer V))
    (hA : A ∈ fixedSpaceFamily (automizerRepresentation V) 3) :
    rank A = 4 ∧ A.map ((binaryNormalizer 1).subtype.comp j) ≤ binaryImage 1 := by
  let : IsElementaryAbelian 2 A := hA.2.1.2
  have hl := parameter_le_rank_of_mem_fixedSpaceFamily _ (automizerRepresentation_injective V) hA
  have hu : rank A ≤ 4 := (offender_rank_le_primeRank A).trans
    ((Theory.GroupTheory.primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le 1 (normalizerCoverage 1)
        ⟨FieldSections.centralizerEquiv 1⟩))
  have hne : rank A ≠ 3 := by
    intro hr
    obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.2.1.1
    have ha2 : orderOf a = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (A := A) a ha) ha1
    have hpa : zpowers a ≤ A := zpowers_le.mpr ha
    have hrp : rank (zpowers a) = 1 := by rw [rank,Nat.card_zpowers,ha2]; decide
    have hc := offender_corank_add (W := A) (A := zpowers a) bot_le hpa
    have hc' : rank A = subgroupCorank A (zpowers a) + rank (zpowers a) := by
      simpa only [subgroupCorank,relIndex_bot_left,rank] using hc
    have hfix := hA.2.2 (zpowers a) hpa (by change subgroupCorank A (zpowers a) < 3; omega)
    have hcodeq : fixedCodim (automizerRepresentation V) A =
        fixedCodim (automizerRepresentation V) (zpowers a) := by
      unfold fixedCodim
      rw [hfix]
    let : IsElementaryAbelian 2 (A.map j) := IsElementaryAbelian.map _
    have hlarge := LargeActors.overgroup_large_elementary_fixedCodim 1
      (binaryNormalizer 1) le_rfl (A.map j) (by rw [rank_map_injective j hj,hr])
    rw [←fixedCodim_map_equivariant (automizerRepresentation V)
      (overgroupAction 1 (binaryNormalizer 1)) j e he A,hcodeq] at hlarge
    have hcode := fixedCodim_map_equivariant (automizerRepresentation V)
      (overgroupAction 1 (binaryNormalizer 1)) j e he (zpowers a)
    rw [MonoidHom.map_zpowers,Involutions.overgroup_involution_fixedCodim
      1 (binaryNormalizer 1) le_rfl (j a) ((orderOf_injective j hj a).trans ha2)] at hcode
    split_ifs at hcode <;> omega
  have hr : rank A = 4 := by omega
  refine ⟨hr,?_⟩
  let f := (binaryNormalizer 1).subtype.comp j
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map _
  apply Chapter7.NormalizedSource.NonMathieuHermitian.large_elementary_le_image 1 (A.map f)
    (by rintro _ ⟨a,ha,rfl⟩; exact (j a).property)
  rw [rank_map_injective f ((binaryNormalizer 1).subtype_injective.comp hj),hr]
  decide

include hj he in
/-- The zero weak-closure branch has a returning whole conjugate with a
rank-four inner action and a rank-five centralizer kernel. -/
theorem field_four_zero_weak_closure
    (T : Sylow 2 G) (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hr : 3 ≤ globalR V) (hm : 3 ≤ localM V) (hw : globalW V T = 0) :
    globalR V = 3 ∧ globalS V = 3 ∧
      ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T ∧ IsWOffenderAt V T g ∧
        rank (inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom)) = 4 ∧
        (inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom)).map
          ((binaryNormalizer 1).subtype.comp j) ≤ binaryImage 1 ∧
        rank (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G)) = 5 := by
  have hrlt : globalR V < 4 := by
    by_contra! hr4
    have hh := globalW_ge_of_hermitian_coordinates V T 1 e j hj he hT (Or.inr hFF) hr4
    rw [hw] at hh
    norm_num at hh
  have hr3 : globalR V = 3 := le_antisymm
    ((ENat.lt_natCast_add_one_iff (n := 3)).mp hrlt) hr
  have hs3 : globalS V = 3 := by
    rw [globalS,hr3,min_eq_left]
    exact_mod_cast hm
  obtain ⟨g,hg,hmove⟩ := (globalW_eq_zero_iff V T).mp hw
  let W := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hWN : W ≤ normalizer (V : Set G) := hg.trans hT.normalizes
  have hA : offenderNormalizer V g = W := inf_eq_left.mpr hWN
  have hOff : IsWOffenderAt V T g := by
    refine ⟨?_,?_⟩
    · intro hc
      exact hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
    · rw [hA,hw]
      simp [subgroupCorank,W]
  have hf := (offender_fixedSpaceFamily_of_lt_globalS hOff (by rw [hw,hs3]; decide)).2
  rw [hw,hs3] at hf
  rw [hA] at hf
  obtain ⟨ha,hi⟩ := field_four_fixed_family_three_rank V e j hj he _ hf
  have hdim : rank W = 9 := by
    rw [rank_map_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hadd := offender_corank_add (W := W) (A := W ⊓ centralizer (V : Set G)) bot_le inf_le_left
  have hadd' : rank W = subgroupCorank W (W ⊓ centralizer (V : Set G)) +
      rank (W ⊓ centralizer (V : Set G)) := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hadd
  have hc := rank_inducedAutomizer V W hWN
  refine ⟨hr3,hs3,g,hg,hOff,ha,hi,?_⟩
  change rank (W ⊓ centralizer (V : Set G)) = 5
  omega

end CFSG.Quasithin.Chapter8.Section02.HermitianSource

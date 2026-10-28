module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension
public import Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.MapInjectivity
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The exhaustive residual catalogue in the S₇ branch

For a surjection onto S₇ with two-group kernel, the T-invariant two-perfect
subgroups with two-core index three are exactly three literal residual
preimages. Adjoining the Sylow subgroup turns each member into an
index-three overgroup. The existing permutation recognition exhausts those
overgroups; taking the residual of the full preimage recovers the original
subgroup. The reverse inclusion follows by transporting core quotients.
No splitting or centrality of the kernel is required.

The coordinate convention inherited from `LocalResidualRecognition` uses
`{2,3,4,5}`, `{0,1}`, `{6}` for the source's `{1,2,3,4}`, `{5,6}`, `{7}`.
Thus the cubic candidate is the source's first actor, the duad candidate
its second, and the syntheme candidate its third. Comparison with the
pointwise stabilizer definitions reduces to a permutation residual equality
by `residualLift_eq_of_residual_eq`.

`source_XFamily_catalogue` applies the result to the literal H/O₂(H)
projection and embeds the three subgroups back into G. The overlap quotient
is transported through the actual restricted quotient map. The linear
calculations determining Y and the final S₃ × S₃ model identification
remain separate obligations of Lemma 14.4.11.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 14.4.11, printed p.1011 (PDF p.1028).
-/

@[expose] public section
open Subgroup
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven
variable {A : Type*} [Group A] [Finite A]

/-- The residual of the literal preimage of a permutation subgroup. -/
def residualLift (q : A →* S7) (P : Subgroup S7) : Subgroup A :=
  twoResidual (P.comap q)

/-- Source actor on the last three letters (after the fixed coordinate relabelling). -/
def firstActor (q : A →* S7) : Subgroup A := residualLift q cubicOvergroup
/-- Source actor on the first four letters. -/
def secondActor (q : A →* S7) : Subgroup A := residualLift q duadOvergroup
/-- The residual of the three-pair partition stabilizer. -/
def thirdActor (q : A →* S7) : Subgroup A := residualLift q synthemeOvergroup

omit [Finite A] in
private theorem residual_eq_iff (X : Subgroup A) :
    twoResidual X = X ↔ IsPPerfect 2 X := by
  have hh := (map_injective X.subtype_injective).eq_iff (a := pResidual 2 X) (b := ⊤)
  simpa only [twoResidual, ← MonoidHom.range_eq_map, range_subtype] using
    hh.trans (pResidual_eq_top_iff 2 X)

private theorem core_index {B : Type*} [Group B] (X : Subgroup B) :
    (twoCore X).relIndex X = Nat.card (X ⧸ pCore 2 X) := by
  have hh := relIndex_map_map_of_injective (pCore 2 X) ⊤ X.subtype_injective
  simpa only [twoCore, ← MonoidHom.range_eq_map, range_subtype, relIndex_top_right,
    index_eq_card] using hh

theorem residualLift_map (q : A →* S7) (hq : Function.Surjective q) (P : Subgroup S7) :
    (residualLift q P).map q = twoResidual P := by
  change ((pResidual 2 (P.comap q)).map (P.comap q).subtype).map q = _
  rw [map_embedded_pResidual, map_comap_eq_self_of_surjective hq]
  rfl

/-- Equal permutation residuals have equal residual lifts. Normalization by
the kernel is proved from the literal preimage, so no central extension or
splitting assumption is used. -/
theorem residualLift_eq_of_residual_eq (q : A →* S7) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) {P R : Subgroup S7}
    (hPR : twoResidual P = twoResidual R) : residualLift q P = residualLift q R := by
  apply eq_of_map_eq_map_of_isPPerfect q
    (isPPerfect_embedded_pResidual 2 (P.comap q))
    (isPPerfect_embedded_pResidual 2 (R.comap q)) hk
  · exact (comap_mono bot_le).trans (le_normalizer_embedded_pResidual 2 (P.comap q))
  · exact (comap_mono bot_le).trans (le_normalizer_embedded_pResidual 2 (R.comap q))
  · change (residualLift q P).map q = (residualLift q R).map q
    rw [residualLift_map q hq, residualLift_map q hq, hPR]

private theorem residualLift_three (q : A →* S7) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (T : Subgroup A) (P : Subgroup S7)
    (hTP : T.map q ≤ P) (hi : (twoCore (twoResidual P)).relIndex (twoResidual P) = 3) :
    ThreeExtension ⊤ T (residualLift q P) := by
  have hTpre : T ≤ P.comap q := map_le_iff_le_comap.mp hTP
  have hp := isPPerfect_embedded_pResidual 2 (P.comap q)
  refine ⟨le_top, hTpre.trans (le_normalizer_embedded_pResidual 2 (P.comap q)),
    (residual_eq_iff _).mpr hp, ?_⟩
  let X := residualLift q P
  let f := q.subgroupMap X
  have hkf : IsPGroup 2 f.ker := by
    have he : f.ker = q.ker.comap X.subtype := by
      ext x
      change f x = 1 ↔ q (x : A) = 1
      exact Subtype.ext_iff
    rw [he]
    exact hk.comap_of_injective X.subtype X.subtype_injective
  have he := MonoidHom.quotientPCoreEquivOfSurjective f (q.subgroupMap_surjective X) hkf
  rw [core_index, Nat.card_congr he.toEquiv, residualLift_map q hq]
  exact (core_index (twoResidual P)) ▸ hi

omit [Finite A] in
private theorem core_le_sylow (T : Sylow 2 A) (X : Subgroup A)
    (hn : (T : Subgroup A) ≤ normalizer (X : Set A)) : twoCore X ≤ T := by
  have hnQ : (T : Subgroup A) ≤ normalizer (twoCore X : Set A) :=
    hn.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hp : IsPGroup 2 (twoCore X ⊔ (T : Subgroup A) : Subgroup A) :=
    (isPGroup_pCoreIn 2 X).to_sup_of_normal_left' T.isPGroup' hnQ
  exact le_sup_left.trans (T.is_maximal' hp le_sup_right).le

private theorem threeExtension_sylow_index (T : Sylow 2 A) (X : Subgroup A)
    (hX : ThreeExtension ⊤ T X) : (T : Subgroup A).relIndex (X ⊔ T) = 3 := by
  have hQT := core_le_sylow T X hX.T_normalizes
  have hi : (pCore 2 X).index = 3 := by
    exact (core_index X).symm.trans hX.index_three
  let S : Sylow 2 X := pCore_isPGroup.toSylow (by rw [hi]; decide)
  have hXT : X ⊓ (T : Subgroup A) = twoCore X := by
    have hh := inf_eq_sylow_map S T.isPGroup' hQT
    exact (inf_comm X (T : Subgroup A)).trans hh
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes X (T : Subgroup A) hX.T_normalizes
  rw [hXT] at hc
  have h1 := relIndex_mul_relIndex (⊥ : Subgroup A) (twoCore X) X bot_le (map_subtype_le _)
  simp only [relIndex_bot_left, hX.index_three] at h1
  have h2 := relIndex_mul_relIndex (⊥ : Subgroup A) (T : Subgroup A) (X ⊔ T) bot_le le_sup_right
  simp only [relIndex_bot_left] at h2
  rw [← h1, ← h2, mul_assoc] at hc
  have hh := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := twoCore X)) hc
  rw [mul_comm 3] at hh
  exact (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (T : Subgroup A))) hh).symm

/-- Every source family member is one of the three literal residual lifts.
The kernel need only be a two-group; it need not be central or split. -/
theorem mem_XFamily_cases (q : A →* S7) (hk : IsPGroup 2 q.ker)
    (T : Sylow 2 A) (hT : (T : Subgroup A).map q = standardTwo)
    (X : Subgroup A) (hX : X ∈ XFamily ⊤ T) :
    X = firstActor q ∨ X = secondActor q ∨ X = thirdActor q := by
  have hkT : q.ker ≤ T := hk.le_sylow_of_normal T
  have hi : standardTwo.relIndex ((X ⊔ T).map q) = 3 := by
    rw [← hT, relIndex_map_map, sup_eq_left.mpr hkT,
      sup_eq_left.mpr (hkT.trans le_sup_right)]
    exact threeExtension_sylow_index T X hX
  have hb : standardTwo ≤ (X ⊔ T).map q := hT ▸ map_mono le_sup_right
  have hlift : residualLift q ((X ⊔ T).map q) = X := by
    rw [residualLift, comap_map_eq, sup_eq_left.mpr (hkT.trans le_sup_right)]
    exact embedded_pResidual_join_pGroup X T ((residual_eq_iff X).mp hX.residual_eq)
      T.isPGroup' hX.T_normalizes
  rcases index_three_over_standardTwo _ hb hi with hd | hs | hc
  · exact Or.inr (Or.inl (hlift.symm.trans (congrArg (residualLift q) hd)))
  · exact Or.inr (Or.inr (hlift.symm.trans (congrArg (residualLift q) hs)))
  · exact Or.inl (hlift.symm.trans (congrArg (residualLift q) hc))

private theorem tetrahedral_core_index :
    (pCore 2 (alternatingGroup (Fin 4))).index = 3 := by
  open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition in
  have hc := (pCore 2 (alternatingGroup (Fin 4))).card_mul_index
  rw [klein_core, klein_card] at hc
  have ha : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [ha] at hc
  rw [Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.klein_core]
  omega

private theorem core_index_equiv {B C : Type*} [Group B] [Group C]
    (e : B ≃* C) : Nat.card (B ⧸ pCore 2 B) = Nat.card (C ⧸ pCore 2 C) := by
  exact Nat.card_congr (QuotientGroup.congr (pCore 2 B) (pCore 2 C) e
    (pCore_map_iso 2 e)).toEquiv

private theorem duad_index : (twoCore (twoResidual duadOvergroup)).relIndex
    (twoResidual duadOvergroup) = 3 := by
  rw [core_index, twoResidual, residual_duadOvergroup]
  let e := (MonoidHom.ofInjective
    (Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.duadHom_injective)).trans
    (Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.duadHom.range.equivMapOfInjective
      liftSix liftSix_injective)
  exact (core_index_equiv e).symm.trans tetrahedral_core_index

private theorem syntheme_index : (twoCore (twoResidual synthemeOvergroup)).relIndex
    (twoResidual synthemeOvergroup) = 3 := by
  rw [core_index, twoResidual, residual_synthemeOvergroup]
  let e := (MonoidHom.ofInjective
    (Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.synthemeHom_injective)).trans
    (Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.synthemeHom.range.equivMapOfInjective
      liftSix liftSix_injective)
  exact (core_index_equiv e).symm.trans tetrahedral_core_index

private theorem cubic_index : (twoCore (twoResidual cubicOvergroup)).relIndex
    (twoResidual cubicOvergroup) = 3 := by
  rw [core_index, twoResidual, residual_cubicOvergroup]
  rw [← core_index_equiv (cubicResidual7.equivMapOfInjective (MulAut.conj cubicConjugator).toMonoidHom
      (MulAut.conj cubicConjugator).injective),
    ← core_index]
  change (cubicResidual7.pCoreIn 2).relIndex cubicResidual7 = 3
  rw [cubicResidual7_core, relIndex_bot_left, cubicResidual7_card]

/-- The first literal lift satisfies all four clauses of the source family. -/
theorem firstActor_mem_XFamily (q : A →* S7) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (T : Subgroup A) (hT : T.map q = standardTwo) :
    firstActor q ∈ XFamily ⊤ T :=
  residualLift_three q hq hk T cubicOvergroup (hT ▸ standardTwo_le_cubic) cubic_index

/-- The second literal lift satisfies all four clauses of the source family. -/
theorem secondActor_mem_XFamily (q : A →* S7) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (T : Subgroup A) (hT : T.map q = standardTwo) :
    secondActor q ∈ XFamily ⊤ T :=
  residualLift_three q hq hk T duadOvergroup (hT ▸ inf_le_left) duad_index

/-- The third literal lift satisfies all four clauses of the source family. -/
theorem thirdActor_mem_XFamily (q : A →* S7) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (T : Subgroup A) (hT : T.map q = standardTwo) :
    thirdActor q ∈ XFamily ⊤ T :=
  residualLift_three q hq hk T synthemeOvergroup (hT ▸ inf_le_right) syntheme_index

/-- Exhaustive equality for the actual family in the covering group. -/
theorem XFamily_eq (q : A →* S7) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (T : Sylow 2 A)
    (hT : (T : Subgroup A).map q = standardTwo) :
    XFamily ⊤ T = {firstActor q, secondActor q, thirdActor q} := by
  ext X
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · exact mem_XFamily_cases q hk T hT X
  · rintro (rfl | rfl | rfl)
    · exact firstActor_mem_XFamily q hq hk T hT
    · exact secondActor_mem_XFamily q hq hk T hT
    · exact thirdActor_mem_XFamily q hq hk T hT


/-- Distinctness is detected in the quotient: the first image has order three,
whereas the second image is an actual tetrahedral group of order twelve. -/
theorem firstActor_ne_secondActor (q : A →* S7) (hq : Function.Surjective q) :
    firstActor q ≠ secondActor q := by
  intro h
  have hh := congrArg (fun X : Subgroup A => Nat.card (X.map q)) h
  have hfirst : Nat.card ((firstActor q).map q) = 3 := by
    rw [firstActor, residualLift_map q hq, twoResidual, residual_cubicOvergroup,
      card_map_of_injective (MulAut.conj cubicConjugator).injective, cubicResidual7_card]
  have hsecond : Nat.card ((secondActor q).map q) = 12 := by
    rw [secondActor, residualLift_map q hq, twoResidual, residual_duadOvergroup,
      duadResidual7, card_map_of_injective liftSix_injective,
      ← Nat.card_congr (MonoidHom.ofInjective
        Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.duadHom_injective).toEquiv]
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hfirst, hsecond] at hh
  omega

private theorem core_map {B C : Type*} [Group B] [Group C]
    (f : B →* C) (hf : Function.Injective f) (X : Subgroup B) :
    (twoCore X).map f = twoCore (X.map f) := by
  let e := X.equivMapOfInjective f hf
  rw [twoCore, twoCore, ← pCore_map_iso 2 e, map_map, map_map]
  rfl

/-- Embedding a local family member preserves residuals, relative normality,
and the intrinsic core index. -/
theorem threeExtension_map {B : Type*} [Group B] [Finite B]
    (f : A →* B) (hf : Function.Injective f) (T X : Subgroup A)
    (hX : ThreeExtension ⊤ T X) :
    ThreeExtension f.range (T.map f) (X.map f) := by
  refine ⟨map_le_range _ _, (map_mono hX.T_normalizes).trans (le_normalizer_map f), ?_, ?_⟩
  · have hh := congrArg (fun Y : Subgroup A => Y.map f) hX.residual_eq
    rw [twoResidual, map_embedded_pResidual] at hh
    exact hh
  · rw [← core_map f hf, relIndex_map_map_of_injective _ _ hf]
    exact hX.index_three

/-- Restriction to the literal local subgroup preserves the source conditions. -/
theorem threeExtension_subgroupOf {B : Type*} [Group B] [Finite B]
    (H T X : Subgroup B) (hX : ThreeExtension H T X) :
    ThreeExtension ⊤ (T.subgroupOf H) (X.subgroupOf H) := by
  refine ⟨le_top, ?_, ?_, ?_⟩
  · apply le_normalizer_iff.mpr
    intro t ht x hx
    exact (le_normalizer_iff.mp hX.T_normalizes) t ht x hx
  · apply map_injective H.subtype_injective
    rw [twoResidual, map_embedded_pResidual, map_subgroupOf_eq_of_le hX.le_H]
    exact hX.residual_eq
  · have hi := relIndex_map_map_of_injective (twoCore (X.subgroupOf H))
      (X.subgroupOf H) H.subtype_injective
    rw [core_map H.subtype H.subtype_injective, map_subgroupOf_eq_of_le hX.le_H] at hi
    exact hi.symm.trans hX.index_three

/-- Complete catalogue in the original ambient group, through the actual
map from H and its subgroup inclusion. -/
theorem ambient_XFamily_eq {B : Type*} [Group B] [Finite B]
    (H T : Subgroup B) (q : H →* S7) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (S : Sylow 2 H)
    (hS : (S : Subgroup H).map H.subtype = T)
    (hT : (S : Subgroup H).map q = standardTwo) :
    XFamily H T = {(firstActor q).map H.subtype, (secondActor q).map H.subtype,
      (thirdActor q).map H.subtype} := by
  have hTH : T ≤ H := hS ▸ map_subtype_le _
  have hTS : T.subgroupOf H = (S : Subgroup H) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hTH, hS]
  ext X
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hX
    have hi := threeExtension_subgroupOf H T X hX
    rw [hTS] at hi
    rcases mem_XFamily_cases q hk S hT (X.subgroupOf H) hi with h | h | h
    · exact Or.inl ((map_subgroupOf_eq_of_le hX.le_H).symm.trans (congrArg (map H.subtype) h))
    · exact Or.inr (Or.inl ((map_subgroupOf_eq_of_le hX.le_H).symm.trans (congrArg (map H.subtype) h)))
    · exact Or.inr (Or.inr ((map_subgroupOf_eq_of_le hX.le_H).symm.trans (congrArg (map H.subtype) h)))
  · rintro (rfl | rfl | rfl)
    · simpa only [XFamily, Set.mem_ofPred_eq, range_subtype, hS] using threeExtension_map H.subtype H.subtype_injective S
        (firstActor q) (firstActor_mem_XFamily q hq hk S hT)
    · simpa only [XFamily, Set.mem_ofPred_eq, range_subtype, hS] using threeExtension_map H.subtype H.subtype_injective S
        (secondActor q) (secondActor_mem_XFamily q hq hk S hT)
    · simpa only [XFamily, Set.mem_ofPred_eq, range_subtype, hS] using threeExtension_map H.subtype H.subtype_injective S
        (thirdActor q) (thirdActor_mem_XFamily q hq hk S hT)


/-- The literal two-core quotient map followed by seven-point coordinates. -/
def starProjection (e : (A ⧸ pCore 2 A) ≃* S7) : A →* S7 :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))

omit [Finite A] in
theorem starProjection_surjective (e : (A ⧸ pCore 2 A) ≃* S7) :
    Function.Surjective (starProjection e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite A] in
theorem starProjection_ker (e : (A ⧸ pCore 2 A) ≃* S7) :
    (starProjection e).ker = pCore 2 A := by
  rw [starProjection, MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

/-- Conjugating the quotient coordinates aligns the actual Sylow image with
 the fixed sixteen-element Sylow subgroup used in the catalogue. -/
theorem exists_aligned_coordinates (S : Sylow 2 A)
    (e₀ : (A ⧸ pCore 2 A) ≃* S7) :
    ∃ e : (A ⧸ pCore 2 A) ≃* S7,
      (S : Subgroup A).map (starProjection e) = standardTwo := by
  let q := starProjection e₀
  let S₀ := S.mapSurjective (starProjection_surjective e₀)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S7 S₀ standardSylow
  let e := e₀.trans (MulAut.conj g)
  refine ⟨e, ?_⟩
  have hh := congrArg Sylow.toSubgroup hg
  change ((S : Subgroup A).map q).map (MulAut.conj g).toMonoidHom = standardTwo at hh
  rw [map_map] at hh
  exact hh

/-- Source application of the exhaustive catalogue in the ambient group.
The only model hypothesis here is the actual quotient isomorphism H/O₂(H) ≃ S₇. -/
theorem source_XFamily_catalogue {B : Type*} [Group B] [Finite B]
    (H T : Subgroup B) (S : Sylow 2 H)
    (hS : (S : Subgroup H).map H.subtype = T)
    (e₀ : coreQuotient H ≃* S7) :
    ∃ e : coreQuotient H ≃* S7,
      (S : Subgroup H).map (starProjection e) = standardTwo ∧
      XFamily H T = {(firstActor (starProjection e)).map H.subtype,
        (secondActor (starProjection e)).map H.subtype,
        (thirdActor (starProjection e)).map H.subtype} ∧
      (firstActor (starProjection e)).map H.subtype ≠
        (secondActor (starProjection e)).map H.subtype := by
  obtain ⟨e, he⟩ := exists_aligned_coordinates S e₀
  have hk : IsPGroup 2 (starProjection e).ker := by
    rw [starProjection_ker]
    exact pCore_isPGroup
  refine ⟨e, he, ambient_XFamily_eq H T (starProjection e)
    (starProjection_surjective e) hk S hS he, ?_⟩
  intro hh
  exact firstActor_ne_secondActor _ (starProjection_surjective e)
    (map_injective H.subtype_injective hh)


omit [Finite A] in
/-- Restricting the projection to a subgroup preserves the two-group kernel. -/
theorem restricted_kernel_two (q : A →* S7) (hk : IsPGroup 2 q.ker)
    (J : Subgroup A) : IsPGroup 2 (q.subgroupMap J).ker := by
  have he : (q.subgroupMap J).ker = q.ker.comap J.subtype := by
    ext x
    change q.subgroupMap J x = 1 ↔ q (x : A) = 1
    exact Subtype.ext_iff
  rw [he]
  exact hk.comap_of_injective J.subtype J.subtype_injective

/-- The equivalence on core quotients induced by the literal restricted projection. -/
noncomputable def coreImageEquiv (q : A →* S7) (hk : IsPGroup 2 q.ker)
    (J : Subgroup A) : coreQuotient J ≃* coreQuotient (J.map q) :=
  MonoidHom.quotientPCoreEquivOfSurjective (q.subgroupMap J) (q.subgroupMap_surjective J)
    (restricted_kernel_two q hk J)

/-- Compatibility with both actual quotient maps. -/
theorem coreImageEquiv_mk (q : A →* S7) (hk : IsPGroup 2 q.ker)
    (J : Subgroup A) (x : J) :
    coreImageEquiv q hk J (QuotientGroup.mk' (pCore 2 J) x) =
      QuotientGroup.mk' (pCore 2 (J.map q)) (q.subgroupMap J x) := by
  exact MonoidHom.quotientPCoreEquivOfSurjective_mk _ _ _ x

/-- The concrete permutation group whose core quotient is needed for the overlap. -/
def modelOverlap : Subgroup S7 :=
  twoResidual cubicOvergroup ⊔ twoResidual duadOvergroup ⊔ standardTwo

/-- The overlap of the lifted actors projects onto the literal permutation overlap. -/
theorem overlap_map (q : A →* S7) (hq : Function.Surjective q)
    (T : Subgroup A) (hT : T.map q = standardTwo) :
    (firstActor q ⊔ secondActor q ⊔ T).map q = modelOverlap := by
  rw [Subgroup.map_sup, Subgroup.map_sup, firstActor, secondActor,
    residualLift_map q hq, residualLift_map q hq, hT]
  rfl

/-- Removing the two-cores transports the actual lifted overlap to the
fixed permutation overlap. Its identification with S₃ × S₃ is a separate
concrete permutation calculation. -/
noncomputable def overlapQuotientEquiv (q : A →* S7) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (T : Subgroup A) (hT : T.map q = standardTwo) :
    coreQuotient (firstActor q ⊔ secondActor q ⊔ T) ≃* coreQuotient modelOverlap := by
  let e := coreImageEquiv q hk (firstActor q ⊔ secondActor q ⊔ T)
  let f := MulEquiv.subgroupCongr (overlap_map q hq T hT)
  exact e.trans (QuotientGroup.congr _ _ f (pCore_map_iso 2 f))

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven

module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCommonSpace
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The factor normalizer of the original common three-space

In the two-factor case of 14.7.6, minimal normality makes the two canonical
five-factors conjugate. Their dihedral extensions have the same normalizers,
so the selected factor's normalizer has index two in the local quotient.
Its full preimage has index-two intersection with every Sylow two-subgroup.

The original critical actor is only known to be conjugate into the original
edge core. We therefore construct a compatible Sylow S inside the same I,
explicitly conjugate to T, while keeping the actor, C and selected factor
unchanged. Within a two-group the reflection in that dihedral factor is
unique. Thus the factor normalizer in S fixes its displacement plane and,
by the literal quotient map, normalizes the full central preimage C.

Conversely an element of I normalizing C preserves its canonical factor:
otherwise independence of the conjugate supports would put C in the central
line. Consequently the selected normalizer in S is Sylow in N_I(C). The
original T's factor-normalizer index is retained separately; no arbitrary
quotient normalization is asserted to lift to an arbitrary subgroup.

LargePrimeFactorNormalizerSource applies this to the original minimal
five-core witness. The A4/S4 endpoint images and both ambient exclusions
remain to be proved. Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source ChapterD
universe u
variable {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
  [IsElementaryAbelian 2 V] [MulDistribMulAction G V] [FaithfulSMul G V]

private theorem pair_factor_index
    (X : Subgroup G) [X.Normal]
    (hgen : smallSupportGroup G V 2 = X)
    (hmin : ∀ N : Subgroup G, N.Normal → N ≤ X → N = ⊥ ∨ N = X)
    (f : CanonicalFiveDihedralFamily (G := G) (V := V))
    (i : smallSupportFactors G V 2)
    (htwo : Nat.card (smallSupportFactors G V 2) = 2) :
    (normalizer (f.factor i : Set G)).index = 2 := by
  let : MulAction G (Subgroup G) := MulAction.compHom (Subgroup G) MulAut.conj
  have he : MulAction.orbit G i.val = smallSupportFactors G V 2 := by
    ext D
    constructor
    · rintro ⟨g,rfl⟩
      exact smallSupportFactors_conjBy i.property g
    · intro hD
      obtain ⟨g,hg⟩ := canonical_five_conjugate_of_minimal X hgen hmin i ⟨D,hD⟩
      exact ⟨g,hg⟩
  have hs : MulAction.stabilizer G i.val = normalizer (i.val : Set G) := by
    ext g
    exact mem_normalizer_iff_map_conj_eq.symm
  rw [f.normalizer_factor,←hs,MulAction.index_stabilizer,he,←Nat.card_coe_set_eq]
  exact htwo

variable {D : Type*} [Group D] [Finite D]
private theorem sylow_index_two_normalizer (S : Sylow 2 D) (N : Subgroup D)
    (hi : N.index = 2) :
    N.relIndex (S : Subgroup D) = 2 ∧
      ∃ P : Sylow 2 N, (P : Subgroup N) = (S : Subgroup D).subgroupOf N := by
  let : N.Normal := normal_of_index_eq_two hi
  refine ⟨?_,S.exists_subgroupOf_eq_of_normal N⟩
  have hd := relIndex_dvd_index_of_normal N (S : Subgroup D)
  rw [hi] at hd
  apply (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left
  intro hone
  have hSN : (S : Subgroup D) ≤ N := relIndex_eq_one.mp hone
  apply S.not_dvd_index
  simpa only [hi] using (index_dvd_of_le hSN)

private theorem two_group_normalizes_reflection
    (D A S : Subgroup G) (hD : Nat.card D = 10) (hA : Nat.card A = 2)
    (hS : IsPGroup 2 S) (hAD : A ≤ D) (hAS : A ≤ S) :
    S ⊓ normalizer (D : Set G) ≤ normalizer (A : Set G) := by
  have hp : IsPGroup 2 (S.subgroupOf D) := hS.comap_subtype
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have hcP : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity,hD]
    decide +kernel
  have hcard : Nat.card (S ⊓ D : Subgroup G) ≤ 2 := by
    have hh := (Subgroup.card_le_of_le hP).trans_eq hcP
    rw [←inf_subgroupOf_right S D,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : S ⊓ D ≤ D)).toEquiv] at hh
    exact hh
  have he : A = S ⊓ D := eq_of_le_of_card_ge (le_inf hAS hAD) (hA ▸ hcard)
  rw [he]
  apply le_normalizer_iff.mpr
  intro g hg x hx
  exact ⟨S.mul_mem (S.mul_mem hg.1 hx.1) (S.inv_mem hg.1),
    (mem_normalizer_iff.mp hg.2 x).mp hx.2⟩

variable {H U Z : Subgroup D} [IsElementaryAbelian 2 U]
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter14.Section06.OddNormalizer

/-- Normalizing a noncentral subspace on one canonical support forces
normalization of that very factor. The full central preimage is retained. -/
theorem local_common_space_factor_control
    (a : LocalQuotientAction H U Z) :
    let := BinaryGroupAction.action a.representation
    ∀ (C : Subgroup D) (_hCZ : ¬ C ≤ Z)
    (f : let := BinaryGroupAction.action a.representation
      CanonicalFiveDihedralFamily (G := HStar H)
        (V := Multiplicative (Additive (U ⧸ Z.subgroupOf U))))
    (i : let := BinaryGroupAction.action a.representation
      smallSupportFactors (HStar H) (Multiplicative (Additive (U ⧸ Z.subgroupOf U))) 2)
    (_hCW : C ≤ supportPreimage a (subspaceCommutator a.representation ⊤ i.val)),
    actorImage H (H ⊓ normalizer (C : Set D)) ≤ normalizer (f.factor i : Set (HStar H)) := by
  intro _
  let := BinaryGroupAction.action a.representation
  intro C hCZ f i hCW
  let : IsElementaryAbelian 2 (Multiplicative (Additive (U ⧸ Z.subgroupOf U))) :=
    BinaryGroupAction.elementary
  let : FaithfulSMul (HStar H) (Multiplicative (Additive (U ⧸ Z.subgroupOf U))) :=
    BinaryGroupAction.faithful a.representation a.faithful
  rintro _ ⟨g,hg,rfl⟩
  rw [f.normalizer_factor,mem_normalizer_iff_map_conj_eq]
  let q := QuotientGroup.mk' (pCore 2 H)
  let j := smallSupportFactors_conjEquiv (V := Multiplicative (Additive (U ⧸ Z.subgroupOf U))) 2 (q g) i
  change i.val.conjBy (q g) = i.val
  by_contra hn
  have hij : i ≠ j := fun he => hn (congrArg Subtype.val he).symm
  have hdis : Disjoint (subspaceCommutator a.representation ⊤ i.val)
      (subspaceCommutator a.representation ⊤ j.val) := by
    have hd := (smallSupportSupports_internalDirectSum
      (G := HStar H) (V := Multiplicative (Additive (U ⧸ Z.subgroupOf U)))
      (Or.inr rfl)).1.pairwiseDisjoint hij
    change Disjoint
      (commutatorAction i.val (Multiplicative (Additive (U ⧸ Z.subgroupOf U))))
      (commutatorAction j.val (Multiplicative (Additive (U ⧸ Z.subgroupOf U)))) at hd
    rw [BinaryGroupAction.commutator_eq a.representation i.val,
      BinaryGroupAction.commutator_eq a.representation j.val] at hd
    apply Submodule.disjoint_def.mpr
    intro v hv hw
    exact hd.le_bot (show Multiplicative.ofAdd v ∈
      BinaryGroupAction.submoduleEquivSubgroup (subspaceCommutator a.representation ⊤ i.val) ⊓
        BinaryGroupAction.submoduleEquivSubgroup (subspaceCommutator a.representation ⊤ j.val)
      from ⟨hv,hw⟩)
  have hm := map_mono (f := (MulAut.conj (g : D)).toMonoidHom) hCW
  have hC : C.map (MulAut.conj (g : D)).toMonoidHom = C :=
    mem_normalizer_iff_map_conj_eq.mp (show (g : D) ∈ normalizer (C : Set D) from hg.2)
  rw [hC,supportPreimage_conjugate a _ g,moved_map_conjugate] at hm
  exact hCZ ((le_inf hCW hm).trans (supportPreimage_disjoint_modulo a _ _ hdis))

/-- Once the selected reflection lies in the chosen two-subgroup, its
factor normalizer preserves its displacement plane, hence the full C upstairs. -/
theorem local_common_space_sylow_normalizes
    (a : LocalQuotientAction H U Z) (C : Subgroup D)
    (A : Subgroup (HStar H)) (hA : Nat.card A = 2)
    (D0 : Subgroup (HStar H)) (hD0 : Nat.card D0 = 10) (hAD : A ≤ D0)
    (S : Subgroup D) (hS : IsPGroup 2 S) (hSH : S ≤ H)
    (hAS : A ≤ actorImage H S)
    (hpre : C = supportPreimage a (subspaceCommutator a.representation ⊤ A)) :
    S ⊓ ((normalizer (D0 : Set (HStar H))).comap
      (QuotientGroup.mk' (pCore 2 H))).map H.subtype ≤ normalizer (C : Set D) := by
  rw [hpre]
  apply supportPreimage_normalized a _ _ (inf_le_left.trans hSH)
  apply subspaceCommutator_invariant_normalizer a.representation
    (le_subspaceStabilizer _ ⊤ (by intros; trivial))
  apply le_trans _ (two_group_normalizes_reflection D0 A (actorImage H S) hD0 hA
    (hS.comap_subtype.map _) hAD hAS)
  rintro _ ⟨g,hg,rfl⟩
  refine ⟨mem_map_of_mem _ hg.1,?_⟩
  obtain ⟨x,hx,hxg⟩ := hg.2
  have he : x = g := H.subtype_injective hxg
  exact he ▸ hx

/-- The same endpoint has a compatible Sylow subgroup inside the same I.
Only the Sylow subgroup is conjugated; the actor and all its labels stay fixed. -/
theorem local_critical_compatible_sylow
    {T : Sylow 2 D} {L V : Subgroup D} {F : InvariantFlag T V 3}
    (I : Subgroup D) (hI : I ∈ F.Hz L (normalizer (L : Set D)))
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (c : hf.CriticalEndpoint) (hb : 3 ≤ hf.b) :
    ∃ S : Sylow 2 D, (S : Subgroup D) ≤ I ∧
      c.conjugate (F.UH I) ≤ S ∧ ∃ x : I, S = (x : D)⁻¹ • T := by
  obtain ⟨x,hx⟩ := local_critical_endpoint_edge I hf c hb
  let S : Sylow 2 D := (x : D)⁻¹ • T
  have hST : (S : Subgroup D) = (T : Subgroup D).conjBy (x : D)⁻¹ := rfl
  refine ⟨S,?_,?_,x,rfl⟩
  · exact T.smul_le (F.sylow_le_of_mem_Hz hI) x⁻¹
  · rw [hST]
    have hRT : F.Ri L 1 ≤ (T : Subgroup D) :=
      (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans
        (map_subgroupOf_eq_of_le le_sup_right).le
    have hh := map_mono (f := (MulAut.conj (x : D)⁻¹).toMonoidHom) (hx.trans hRT)
    change ((c.conjugate (F.UH I)).conjBy (x : D)).conjBy (x : D)⁻¹ ≤ _ at hh
    rwa [conjBy_inv] at hh

omit [Finite D] in
private theorem normalizer_preimage (H : Subgroup D) (B : Subgroup (HStar H)) :
    ((normalizer (B : Set (HStar H))).comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype =
      H ⊓ normalizer (((B.comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype : Subgroup D) : Set D) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let K := (B.comap q).map H.subtype
  have hK : K.subgroupOf H = B.comap q := by
    exact comap_map_eq_self_of_injective H.subtype_injective _
  rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),←hK,
    ←subgroupOf_normalizer_eq (map_subtype_le _),subgroupOf_map_subtype,inf_comm]
  rw [hK]

/-- The common three-space has a Sylow normalizer of index two in an
ambient Sylow subgroup. Its factor is the original full quotient preimage. -/
theorem local_common_space_two_factor_sylow
    {T : Sylow 2 D} {L V : Subgroup D} {F : InvariantFlag T V 3}
    (I : Subgroup D) (hI : I ∈ F.Hz L (normalizer (L : Set D)))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    let := BinaryGroupAction.action a.representation
    ∀ (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (c : hf.CriticalEndpoint) (_hb : 3 ≤ hf.b)
    (X : Subgroup (HStar I)) [X.Normal]
    (_hgen : let := BinaryGroupAction.action a.representation
      smallSupportGroup (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2 = X)
    (_hmin : ∀ N : Subgroup (HStar I), N.Normal → N ≤ X → N = ⊥ ∨ N = X)
    (f : let := BinaryGroupAction.action a.representation
      CanonicalFiveDihedralFamily (G := HStar I)
        (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))))
    (i : let := BinaryGroupAction.action a.representation
      smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2)
    (_htwo : let := BinaryGroupAction.action a.representation
      Nat.card (smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 2)
    (_hAD : actorImage I (c.conjugate (F.UH I)) ≤ f.factor i)
    (_hAc : Nat.card (actorImage I (c.conjugate (F.UH I))) = 2)
    (C : Subgroup D) (_hCZ : ¬ C ≤ F.Vi 1)
    (_hpre : C = supportPreimage a (subspaceCommutator a.representation ⊤
      (actorImage I (c.conjugate (F.UH I)))))
    (_hCW : C ≤ supportPreimage a (subspaceCommutator a.representation ⊤ i.val)),
    ∃ S : Sylow 2 D, (S : Subgroup D) ≤ I ∧ c.conjugate (F.UH I) ≤ S ∧
      (∃ x : I, S = (x : D)⁻¹ • T) ∧
      let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
      let T1 := (S : Subgroup D) ⊓ normalizer (K1 : Set D)
      ((T : Subgroup D) ⊓ normalizer (K1 : Set D)).relIndex (T : Subgroup D) = 2 ∧
      T1.relIndex (S : Subgroup D) = 2 ∧ T1 ≤ normalizer (C : Set D) ∧
      I ⊓ normalizer (C : Set D) ≤ normalizer (K1 : Set D) ∧
      ∃ P : Sylow 2 (I ⊓ normalizer (C : Set D) : Subgroup D),
        (P : Subgroup (I ⊓ normalizer (C : Set D) : Subgroup D)).map
          (I ⊓ normalizer (C : Set D)).subtype = T1 := by
  intro _
  let := BinaryGroupAction.action a.representation
  intro hf c hb X hXn hgen hmin f i htwo hAD hAc C hCZ hpre hCW
  let : IsElementaryAbelian 2
      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) :=
    BinaryGroupAction.elementary
  let : FaithfulSMul (HStar I)
      (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) :=
    BinaryGroupAction.faithful a.representation a.faithful
  obtain ⟨S,hSI,hAS,hconj⟩ := local_critical_compatible_sylow I hI hf c hb
  let q := QuotientGroup.mk' (pCore 2 I)
  let K1 := ((f.factor i).comap q).map I.subtype
  let N := (normalizer (f.factor i : Set (HStar I))).comap q
  let B := I ⊓ normalizer (C : Set D)
  have hNmap : N.map I.subtype = I ⊓ normalizer (K1 : Set D) := normalizer_preimage I (f.factor i)
  have hNI : N.index = 2 := by
    rw [index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact pair_factor_index X hgen hmin f i htwo
  have hBN : B.subgroupOf I ≤ N := by
    intro g hg
    exact local_common_space_factor_control a C hCZ f i hCW (mem_map_of_mem q hg)
  have hBK : B ≤ normalizer (K1 : Set D) := by
    have hh := map_mono (f := I.subtype) hBN
    rw [map_subgroupOf_eq_of_le inf_le_left,hNmap] at hh
    exact hh.trans inf_le_right
  let S0 := S.subtype hSI
  obtain ⟨_,P,hP⟩ := sylow_index_two_normalizer S0 N hNI
  have hDcard : Nat.card (f.factor i) = 10 := by
    rw [Nat.card_congr (f.model i).some.toEquiv,DihedralGroup.nat_card]
  have hnormal := local_common_space_sylow_normalizes a C _ hAc (f.factor i) hDcard hAD
    (S : Subgroup D) S.isPGroup' hSI (map_mono (comap_mono hAS)) hpre
  rw [hNmap,←inf_assoc,inf_eq_left.mpr hSI] at hnormal
  have hPN : (P : Subgroup N).map N.subtype = (S0 : Subgroup I) ⊓ N := by
    rw [hP,subgroupOf_map_subtype]
  have hPambient : ((P : Subgroup N).map N.subtype).map I.subtype =
      (S : Subgroup D) ⊓ normalizer (K1 : Set D) := by
    rw [hPN,map_inf _ _ _ I.subtype_injective]
    rw [show (S0 : Subgroup I) = (S : Subgroup D).subgroupOf I from S.coe_subtype hSI,
      map_subgroupOf_eq_of_le hSI,hNmap,
      ←inf_assoc,inf_eq_left.mpr hSI]
  have hPB : (P : Subgroup N) ≤ (B.subgroupOf I).subgroupOf N := by
    intro p hp
    have hpS : (p : I) ∈ S0 := by
      change p ∈ (S0 : Subgroup I).subgroupOf N
      rw [←hP]
      exact hp
    exact ⟨p.val.property,hnormal ⟨hpS,(hNmap ▸ mem_map_of_mem I.subtype p.property).2⟩⟩
  let P0 := P.subtype hPB
  let e : (B.subgroupOf I).subgroupOf N ≃* B :=
    (subgroupOfEquivOfLe hBN).trans (subgroupOfEquivOfLe inf_le_left)
  let P1 : Sylow 2 B := P0.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP1 : (P1 : Subgroup B).map B.subtype =
      (S : Subgroup D) ⊓ normalizer (K1 : Set D) := by
    apply le_antisymm
    · rintro _ ⟨b,hb,rfl⟩
      obtain ⟨p,hp,rfl⟩ := hb
      exact hPambient ▸ mem_map_of_mem I.subtype
        (mem_map_of_mem N.subtype (show (p : N) ∈ P from hp))
    · intro x hx
      have hx' : x ∈ ((P : Subgroup N).map N.subtype).map I.subtype := hPambient.symm ▸ hx
      obtain ⟨p,hp,hpx⟩ := hx'
      obtain ⟨y,hy,rfl⟩ := hp
      exact ⟨e ⟨y,hPB hy⟩,mem_map_of_mem e.toMonoidHom
        (show (⟨y,hPB hy⟩ : (B.subgroupOf I).subgroupOf N) ∈ P0 from hy),hpx⟩
  have index_for (R : Sylow 2 D) (hRI : (R : Subgroup D) ≤ I) :
      ((R : Subgroup D) ⊓ normalizer (K1 : Set D)).relIndex (R : Subgroup D) = 2 := by
    have hi := (sylow_index_two_normalizer (R.subtype hRI) N hNI).1
    have hh := relIndex_map_map_of_injective N ((R.subtype hRI) : Subgroup I) I.subtype_injective
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hRI,hNmap] at hh
    have he : (I ⊓ normalizer (K1 : Set D)).relIndex (R : Subgroup D) =
        ((R : Subgroup D) ⊓ normalizer (K1 : Set D)).relIndex (R : Subgroup D) := by
      apply congrArg Subgroup.index
      ext x
      change ((x : D) ∈ I ∧ (x : D) ∈ normalizer (K1 : Set D)) ↔
        ((x : D) ∈ R ∧ (x : D) ∈ normalizer (K1 : Set D))
      constructor
      · intro hx
        exact ⟨x.property,hx.2⟩
      · intro hx
        exact ⟨hRI x.property,hx.2⟩
    exact he ▸ (hh.trans hi)
  exact ⟨S,hSI,hAS,hconj,index_for T (F.sylow_le_of_mem_Hz hI),index_for S hSI,
    hnormal,hBK,P1,hP1⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

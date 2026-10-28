module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeSquares
public import Theory.SpecificGroups.BinaryComponentResidual
public import Mathlib.Data.Nat.Prime.Factorial
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import Theory.GroupTheory.SolvableResidual.NormalSupplement
/-!
# The odd ternary remainder for a proper local A5 section

Inspect the genuine Theorem C catalogue with the literal local A5 quotient.
The alternating, low-degree linear, binary linear and sporadic rows have
two-group outer automorphism groups; the Bender row cannot contain the
proper local component. After the separately excluded binary rank-two
rows, only odd prime-field ternary groups remain. The linear parameter-five
row also has a two-group outer automorphism group.

The accompanying transport theorem retains the full Sylow intersection
and proper local section in the actual ambient two-core quotient.
Source: Aschbacher--Smith A.3.14, A.3.18 and Proposition 9.3.1,
printed pp.47--53,732--733.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.XiEmbedding.OuterModels
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem two_transfer {M : Type*} [Group M]
    (e : G ≃* M) (h : IsPGroup 2 (MulAut.Outer M)) : IsPGroup 2 (MulAut.Outer G) :=
  h.of_injective (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective
private theorem alternating_two (n : ℕ) (hn : 5 ≤ n) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin n))) := by
  by_cases he : n = 6
  · subst n
    exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
  let A := alternatingGroup (Fin n)
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard : Nat.card (Equiv.Perm (Fin n) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hcard).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨s,rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn he).surjective a
  exact ⟨QuotientGroup.mk' A s,rfl⟩
/-- The nonordinary catalogue remainder with the local quotient kept literal. -/
theorem five_section_nonordinary_model_is_odd_ternary [IsSimpleGroup G] [IsQuasisimple G]
    (S : Sylow 2 G) (K : Subgroup G) (hK : K ∈ localCComponents S)
    (hproper : K ≠ ⊤) (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hm : ChapterA.Section02.IsTheoremCModel G)
    (hout : ¬ IsPGroup 2 (MulAut.Outer G))
    (hrank : ∀ n, ¬ ChapterA.Section02.IsTheoremCRankTwoModel G n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      (ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p) := by
  cases hm with
  | alternating n _ he =>
    obtain ⟨e⟩ := he
    have hd : 5 ∣ Nat.card (alternatingGroup (Fin n)) := by
      rw [←Nat.card_congr e.toEquiv]
      exact (FiveLocalFF.SolvableQuotients.five_dvd_card K eK).trans K.card_subgroup_dvd_card
    have hf : 5 ∣ n.factorial := by
      have hh := hd.trans (alternatingGroup (Fin n)).card_subgroup_dvd_card
      simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] using hh
    exact (hout (two_transfer e (alternating_two n (Nat.prime_five.dvd_factorial.mp hf)))).elim
  | odd h =>
    cases h with
    | linear_two p n hp ho hn hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      exact (hout (two_transfer e
        (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two hp ho hn hF))).elim
    | linear_three p hp ho hm => exact ⟨p,hp,ho,.inl hm⟩
    | unitary_three p hp ho hm => exact ⟨p,hp,ho,.inr hm⟩
  | bender h =>
    have ht : (⊤ : Subgroup G).IsCComponent :=
      (show IsComponent G ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
    exact (hproper (eq_of_bender_containing_component S hK ht le_top
      (h.of_mulEquiv topEquiv))).elim
  | rank_two n h => exact (hrank n h).elim
  | linear_binary n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    let a := (e.trans (Atlas.fieldEquivPSL n eF)).trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < n))
    exact (hout (two_transfer a (Theory.SpecificGroups.BinaryComponentResidual.linear_outer_two hn))).elim
  | sporadic h =>
    rcases h with ⟨name,hne,⟨e⟩⟩ | ⟨e⟩
    · cases name with
      | m11 => exact (hout (two_transfer e Sporadic.Mathieu.m11_outer_isPGroup_two)).elim
      | m12 => exact (hout (two_transfer e (m12_outer_isPGroup_two_of_sylow_aut
          Sporadic.Mathieu.M12SmallPair.SylowAutomorphismGroup.isPGroup_two))).elim
      | m22 => exact (hout (two_transfer e (m22_outer_isPGroup_two_of_coverage
          Sporadic.Mathieu.m22DesignAutToAut_surjective))).elim
      | m23 => exact (hout (two_transfer e Sporadic.Mathieu.m23_outer_isTwoGroup)).elim
      | m24 => exact (hout (two_transfer e Sporadic.Mathieu.M24OuterRestriction.outer_isPGroup_two)).elim
      | j2 => exact (hout (two_transfer e JankoTwo.outer_isPGroup_two)).elim
      | hs => exact (hout (two_transfer e (Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
          Sporadic.LeechRelated.HS.pointStabilizer_map
          Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow))).elim
      | ru =>
        let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
        let := rudvalis_outer_subsingleton
        have ho : IsPGroup 2 (MulAut.Outer Rudvalis.Model) := fun x =>
          ⟨0,by simpa only [pow_zero,pow_one] using (Subsingleton.elim x 1)⟩
        exact (hout (two_transfer e ho)).elim
      | j3 => exact (hne rfl).elim
      | he => exact (hout (two_transfer e (Subgroup.isPGroup_outer_of_normalizer
          Held.permutationGroup 2 Held.Realization.normalizer_surjective
          Held.isPGroup_permutationNormalizerQuotient))).elim
      | j4 => exact (hout (two_transfer e Janko4.AdequateLocal.outer_isPGroup_two)).elim
    · obtain ⟨e⟩ := e
      let := Janko1.OuterCertificate.outer_subsingleton
      have ho : IsPGroup 2 (MulAut.Outer Janko1.Model) := fun x =>
        ⟨0,by simpa only [pow_zero,pow_one] using (Subsingleton.elim x 1)⟩
      exact (hout (two_transfer e ho)).elim

private theorem linear_five_outer_matrix {F : Type*} [Field F] [Finite F]
    [IsSimpleGroup PSL(3,F)] [Group.IsPerfect PSL(3,F)]
    (hF : Nat.card F = 5) : IsPGroup 2 (MulAut.Outer PSL(3,F)) := by
  open Matrix.PSL3.OuterSolvable in
  have hd : IsPGroup 2 (innerDiagonalOuter F) := by
    have hu : IsPGroup 2 Fˣ := IsPGroup.of_card (n := 2) (by rw [Nat.card_units,hF]; norm_num)
    let d : GL (Fin 3) F →* Fˣ := Matrix.GeneralLinearGroup.det
    let f := linearOuterAction F
    have hq : IsPGroup 2 (GL (Fin 3) F ⧸ d.ker) :=
      hu.of_injective (QuotientGroup.kerLift d) (QuotientGroup.kerLift_injective d)
    have hk : d.ker ≤ f.rangeRestrict.ker := by
      simpa only [MonoidHom.ker_rangeRestrict] using det_ker_le_linearOuterAction_ker F
    exact hq.of_surjective (QuotientGroup.lift d.ker f.rangeRestrict hk)
      (QuotientGroup.lift_surjective_of_surjective d.ker f.rangeRestrict
        f.rangeRestrict_surjective hk)
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup PSL(3,F)) x
  have hs := Matrix.PSL3.OuterSolvable.OddPrimeSquares.outer_square_mem
    (Group.IsPerfect.not_isSolvable _) (by decide : Nat.Prime 5) (by decide : Odd 5) hF a
  obtain ⟨n,hn⟩ := hd ⟨_,hs⟩
  refine ⟨n+1,?_⟩
  have hh := congrArg Subtype.val hn
  change ((_ : MulAut.Outer PSL(3,F))^2)^(2^n)=1 at hh
  rw [←pow_mul] at hh
  simpa only [pow_succ'] using hh

omit [Finite G] in
/-- The linear ternary parameter-five row has two-group outer automorphisms. -/
theorem linear_three_five_outer_two [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : ClassicalGroup.IsPSL G 3 5) : IsPGroup 2 (MulAut.Outer G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact two_transfer e (linear_five_outer_matrix hF)

/-- The proper local A5 section in the literal containing two-core image.
The Sylow remains the full intersection of the original quotient Sylow. -/
theorem proper_five_section_in_containing_image
    (P : Sylow 2 G) (K J : Subgroup G)
    (hJ : J.IsCComponent) (hK : K ∈ localCComponents P)
    (hKJ : K < J) (hPK : (P : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    let q := QuotientGroup.mk' (pCore 2 G)
    let I := J.map q
    let KB := K.map q
    ∃ S : Sylow 2 I,
      (S : Subgroup I) =
        ((P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))) :
          Subgroup (G ⧸ pCore 2 G)).subgroupOf I ∧
      KB.subgroupOf I ∈ localCComponents S ∧
      (S : Subgroup I) ≤ normalizer (KB.subgroupOf I : Set I) ∧
      KB.subgroupOf I ≠ ⊤ ∧
      Nonempty ((KB.subgroupOf I ⧸ pCore 2 (KB.subgroupOf I)) ≃*
        alternatingGroup (Fin 5)) := by
  intro q I KB
  let Q := pCore 2 G
  let : Group.IsNilpotent Q := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hQK : Q ≤ normalizer (K : Set G) :=
    (pCore_isPGroup.le_sylow_of_normal P).trans hPK
  let : Group.IsPerfect K := FiveLocalFF.SolvableQuotients.local_perfect hK
  let : Group.IsPerfect J := hJ.perfect
  let T := P.mapSurjective (QuotientGroup.mk'_surjective Q)
  have hIB : KB ≤ I := map_mono hKJ.le
  have hl : KB ∈ localCComponents T :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hK q
  have hTK : (T : Subgroup (G ⧸ Q)) ≤ normalizer (KB : Set (G ⧸ Q)) :=
    (map_mono hPK).trans (le_normalizer_map q)
  have hI : I.IsCComponent := hJ.map_quotient Q
  obtain ⟨S,hS,hlocal,hSK⟩ := exists_local_sylow_normalizing T hl hI.subnormal hIB hTK
  have hproper : KB.subgroupOf I ≠ ⊤ := by
    intro ht
    have he : KB = I := le_antisymm hIB (subgroupOf_eq_top.mp ht)
    have hsup : K ⊔ Q = J ⊔ Q := by
      simpa only [KB,I,q,comap_map_eq,QuotientGroup.ker_mk'] using congrArg (comap q) he
    have hJK : J ≤ K := by
      rw [←map_solvableResidual_sup_eq_of_perfect_normalized K Q hQK]
      apply le_map_solvableResidual_of_isPerfect J (K ⊔ Q)
      rw [hsup]
      exact le_sup_left
    exact hKJ.not_ge hJK
  obtain ⟨ekb⟩ := FiveLocalFF.SolvableQuotients.section_map q K hK eK
  let d : KB.subgroupOf I ≃* KB := subgroupOfEquivOfLe hIB
  let ek : (KB.subgroupOf I ⧸ pCore 2 (KB.subgroupOf I)) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans ekb
  exact ⟨S,hS,hlocal,hSK,hproper,⟨ek⟩⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

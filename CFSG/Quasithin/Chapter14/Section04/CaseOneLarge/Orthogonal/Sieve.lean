module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.NaturalModelSieve
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedM24
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedJ4
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedHeld
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedRu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OrdinaryContainment
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.Intrinsic
public import Theory.Representation.BinaryPermutation.FiveConjugation

/-!
# The complete deleted-five sieve for the orthogonal row

A Sylow-normalized deleted A₅ block cannot survive in an SQTK group with
trivial two-core. The genuine containment theorem places it in a
C-component; its elementary layer forces that component to be quasisimple.
Restriction retains the original Sylow intersection, and passage through
the component's center retains the block and its conjugation marking.
The full simple-carrier sieve excludes every row, including M₂₄, J₄, Held
and Rudvalis. No embedding-classification callback is required.

The intrinsic binary-core coordinates construct the short-group and block
premises in the final consumer. The orthogonal lift still has to construct
those coordinates on its actual normalizer-quotient image.

Source: Aschbacher--Smith, A.3.6 and A.3.14, printed pp.43--44,49--50;
the terminal embedding argument in 14.4.9, printed p.1010.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open ChapterC ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

/-- Every actual simple carrier is excluded with the original block and Sylow markings. -/
theorem no_simple_deleted_block [IsSimpleGroup G] [Group.IsPerfect G]
    (S : Sylow 2 G) (B : Subgroup G) (hB : IsAlternatingBlock B 5)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hm : ChapterA.Section02.IsTheoremCModel G) : False := by
  obtain ⟨name,hname,⟨e⟩⟩ :=
    Chapter10.FixedCenterOvercomponent.DeletedModelSieve.simple_model_remaining S B hB hl hn hm
  rcases hname with h | h | h | h <;> subst name
  · exact alternatingFiveDeleted_not_m24 e S B hB hl hn
  · exact alternatingFiveDeleted_not_j4 e S B hB hl hn
  · exact alternatingFiveDeleted_not_held e S B hB hn
  · exact alternatingFiveDeleted_not_ru e S B hB hn

/-- Passing through the center preserves the marked block and discharges the carrier premise. -/
theorem no_quasisimple_deleted_block [IsQuasisimple G]
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (S : Sylow 2 G) (B : Subgroup G) (hB : IsAlternatingBlock B 5)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hne : B ≠ ⊤) : False := by
  let := IsQuasisimple.simple (G := G)
  obtain ⟨hl',hn',hB',_⟩ := alternatingFive_block_center_image S hl hn hB hne
  exact no_simple_deleted_block
    (S.mapSurjective (QuotientGroup.mk'_surjective (center G))) _ hB' hl' hn'
    (quasisimple_center_quotient_theoremC_model hG)

/-- Containment and full-Sylow restriction reduce the original core-free SQTK group to the sieve. -/
theorem no_core_free_deleted_block
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (S : Sylow 2 G) (B : Subgroup G) (hB : IsAlternatingBlock B 5)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G)) : False := by
  obtain ⟨K,⟨hK,hBK⟩,_⟩ := existsUnique_containing_cComponent_knownSimple hG S hl
  let : IsQuasisimple K := alternatingFive_containing_component_quasisimple hG hO hK hBK hB
  obtain ⟨P,hP,hl'⟩ := exists_local_sylow_restriction S hl hBK hK.subnormal
  have hB' : IsAlternatingBlock (B.subgroupOf K) 5 :=
    hB.of_mulEquiv (subgroupOfEquivOfLe hBK).symm
  have hn' : (P : Subgroup K) ≤ normalizer (B.subgroupOf K : Set K) := by
    rw [hP, ← subgroupOf_normalizer_eq hBK]
    exact subgroupOf_mono K hn
  have hKO : pCore 2 K = ⊥ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_bot]
    exact le_bot_iff.mp (hO ▸ pCoreIn_le_of_subnormal 2 hK.subnormal)
  have hne : B.subgroupOf K ≠ ⊤ := by
    intro he
    have hb : IsAlternatingBlock K 5 :=
      hB'.of_mulEquiv ((MulEquiv.subgroupCongr he).trans topEquiv)
    exact hb.2.1.core_ne_bot hKO
  exact no_quasisimple_deleted_block (hG.subgroup K) P _ hB' hl' hn' hne

/-- The actual core action constructs the block; no short-group hypothesis is needed. -/
theorem no_core_free_binary_five
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (m : BinaryPermutation.FiveConjugation B (pCore 2 B)) : False := by
  let : Group.IsPerfect (B.subgroupOf (B ⊔ (S : Subgroup G))) := hl.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)).surjective
  have hp : IsPPerfect 2 B := by
    intro N hN hquot
    let := hN
    let : Group.IsNilpotent (B ⧸ N) := hquot.isNilpotent
    have ht := le_of_isPerfect_of_solvable_quotient (⊤ : Subgroup B) N
    exact top_le_iff.mp ht
  have hb : IsAlternatingBlock B 5 :=
    isAlternatingBlock_five_of_core_coordinates hp m.actor m.coordinates
      (fun b v => congrArg Multiplicative.toAdd (m.equivariant b v))
  exact no_core_free_deleted_block hG hO S B hb hl hn
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

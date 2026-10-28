module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.NormalizerAction.Supplement
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import CFSG.Quasithin.ChapterB.Section02.Thompson

/-!
# The literal radical supplements and their Sylow section centralizer

Set R=C_T(L/O∞(L)) and L_R=N_L(R)^∞. The commutator-preimage
construction needs only relative normality. It proves T-invariance of R
and L_R, and identifies the section centralizer for every invariant
radical supplement using O∞(B)=B∩O∞(L).

A proper normal subgroup of a C-component is solvable. Applied to
[L,J(T)], this gives the source dichotomy L=[L,J(T)] or J(T)≤R.
Here J(T) is exactly ChapterB.thompsonJ T 0, the elementary Thompson
convention. Membership of L_R in the local family, its quotient and core,
and elimination of the second alternative remain separate source steps.

Source: Aschbacher--Smith, Lemma 13.1.9, first paragraphs, printed p.869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter12.Section02 Chapter1.RadicalNormalizers
variable {G : Type*} [Group G]

/-- The actual family L₁: local C-components supplementing O∞(L). -/
@[expose] def radicalSupplements (T L : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ Chapter1.L G T ∧ (solvableRadical L).map L.subtype ⊔ B = L}

/-- The literal section centralizer C_T(L/O∞(L)); the commutator criterion
below applies when T normalizes L. No ambient normality of L is imposed. -/
@[expose] def radicalSylowCentralizer (T L : Subgroup G) : Subgroup G :=
  commutatorPreimage T L ((solvableRadical L).map L.subtype)

/-- The source subgroup L_R = N_L(R)^∞, using the solvable residual. -/
@[expose] def canonicalSupplement (T L : Subgroup G) : Subgroup G :=
  normalizerResidual L (radicalSylowCentralizer T L)

theorem radicalSylowCentralizer_le (T L : Subgroup G) : radicalSylowCentralizer T L ≤ T :=
  commutatorPreimage_le _ _ _

theorem le_radicalSylowCentralizer_iff {T L A : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G)) :
    A ≤ radicalSylowCentralizer T L ↔ A ≤ T ∧ ⁅A,L⁆ ≤ (solvableRadical L).map L.subtype :=
  le_commutatorPreimage_iff _ _ _ _
    (hTL.trans (normalizer_le_normalizer_characteristic_image L (solvableRadical L)))

theorem sylow_normalizes_radicalSylowCentralizer {T L : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G)) :
    T ≤ normalizer (radicalSylowCentralizer T L : Set G) := by
  have hTR := hTL.trans (normalizer_le_normalizer_characteristic_image L (solvableRadical L))
  exact commutatorPreimage_normalized _ _ _ _ hTR T.le_normalizer hTL hTR

theorem sylow_normalizes_canonicalSupplement {T L : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G)) :
    T ≤ normalizer (canonicalSupplement T L : Set G) :=
  le_normalizer_normalizerResidual hTL (sylow_normalizes_radicalSylowCentralizer hTL)

theorem canonicalSupplement_le (T L : Subgroup G) : canonicalSupplement T L ≤ L :=
  normalizerResidual_le _ _

variable [Finite G]

theorem canonicalSupplement_perfect (T L : Subgroup G) :
    Group.IsPerfect (canonicalSupplement T L) := normalizerResidual_perfect _ _

/-- Source radical intersection, with the actual subgroup inclusions. -/
theorem supplement_radical {L B : Subgroup G}
    (hk : (NormalizerReducedAction.componentMap L).ker = solvableRadical L)
    (hgen : (solvableRadical L).map L.subtype ⊔ B = L) :
    (solvableRadical B).map B.subtype = B ⊓ (solvableRadical L).map L.subtype := by
  have hBL : B ≤ L := hgen ▸ le_sup_right
  have hr := NormalizerReducedAction.supplement_kernel hBL hk hgen
  rw [← MonoidHom.comap_ker,hk] at hr
  ext x
  constructor
  · rintro ⟨b,hb,rfl⟩
    refine ⟨b.property,?_⟩
    have hb' : b ∈ (solvableRadical L).comap (inclusion hBL) := hr.symm ▸ hb
    exact mem_map_of_mem L.subtype (show inclusion hBL b ∈ solvableRadical L from hb')
  · rintro ⟨hb,⟨l,hl,he⟩⟩
    refine ⟨⟨x,hb⟩,?_,rfl⟩
    rw [← hr]
    change inclusion hBL ⟨x,hb⟩ ∈ solvableRadical L
    have he' : inclusion hBL ⟨x,hb⟩ = l := Subtype.ext he.symm
    exact he' ▸ hl

/-- Each invariant supplement has exactly the same section centralizer R. -/
theorem supplement_radicalSylowCentralizer {T L B : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G)) (hTB : T ≤ normalizer (B : Set G))
    (hk : (NormalizerReducedAction.componentMap L).ker = solvableRadical L)
    (hgen : (solvableRadical L).map L.subtype ⊔ B = L) :
    radicalSylowCentralizer T B = radicalSylowCentralizer T L := by
  let D := (solvableRadical L).map L.subtype
  have hBL : B ≤ L := hgen ▸ le_sup_right
  have hTD : T ≤ normalizer (D : Set G) :=
    hTL.trans (normalizer_le_normalizer_characteristic_image L (solvableRadical L))
  have hLD : L ≤ normalizer (D : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (solvableRadical L))
  have hr := supplement_radical hk hgen
  apply le_antisymm
  · apply (le_radicalSylowCentralizer_iff hTL).mpr
    refine ⟨radicalSylowCentralizer_le _ _,?_⟩
    rw [commutator_comm]
    nth_rw 1 [← hgen]
    apply commutator_sup_le_of_relative_normal L D B _ D hLD (map_subtype_le _) hBL
    · apply le_normalizer_iff_commutator_le_left.mp
      exact (radicalSylowCentralizer_le _ _).trans hTD
    · rw [commutator_comm]
      exact ((le_radicalSylowCentralizer_iff hTB).mp le_rfl).2.trans
        (hr.le.trans inf_le_right)
  · apply (le_radicalSylowCentralizer_iff hTB).mpr
    refine ⟨radicalSylowCentralizer_le _ _,?_⟩
    rw [hr]
    apply le_inf
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_left.mp
        ((radicalSylowCentralizer_le _ _).trans hTB)
    · exact (commutator_mono le_rfl hBL).trans
        ((le_radicalSylowCentralizer_iff hTL).mp le_rfl).2

/-- The normal C-component commutator dichotomy, in its intrinsic radical. -/
theorem local_commutator_eq_or_radical {T L A : Subgroup G}
    (hL : L ∈ Chapter1.L G T) (hAL : A ≤ normalizer (L : Set G)) :
    L = ⁅L,A⁆ ∨ ⁅L,A⁆ ≤ (solvableRadical L).map L.subtype := by
  classical
  have hCL : ⁅L,A⁆ ≤ L := le_normalizer_iff_commutator_le_left.mp hAL
  by_cases he : L = ⁅L,A⁆
  · exact Or.inl he
  right
  let C := ⁅L,A⁆.subgroupOf L
  let : C.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left L A)
  have hC : C ≠ ⊤ := by
    intro htop
    exact he (le_antisymm (subgroupOf_eq_top.mp htop) hCL)
  have ht : (⊤ : Subgroup L).IsCComponent := by
    simpa only [subgroupOf_self] using hL.1.subgroupOf_of_le le_rfl le_sup_left
  have hk := kernel_le_solvableRadical_of_top_isCComponent ht (QuotientGroup.mk' C)
    (by simpa only [QuotientGroup.ker_mk'] using hC)
  rw [QuotientGroup.ker_mk'] at hk
  have hm := map_mono (f := L.subtype) hk
  rwa [map_subgroupOf_eq_of_le hCL] at hm

/-- Failure of literal J(T)-movement puts J(T) in the source R. -/
theorem thompson_movement_or_le_radicalSylowCentralizer {T L : Subgroup G}
    (hL : L ∈ Chapter1.L G T) (hTL : T ≤ normalizer (L : Set G)) :
    L = ⁅L,ChapterB.thompsonJ T 0⁆ ∨
      ChapterB.thompsonJ T 0 ≤ radicalSylowCentralizer T L := by
  have hJT : ChapterB.thompsonJ T 0 ≤ T := by
    rw [ChapterB.thompsonJ_zero]
    exact sSup_le fun _ hA => hA.1
  rcases local_commutator_eq_or_radical hL (hJT.trans hTL) with he | hr
  · exact Or.inl he
  · exact Or.inr ((le_radicalSylowCentralizer_iff hTL).mpr ⟨hJT,by rwa [commutator_comm]⟩)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements

module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerNonalternatingG2
public import Theory.GroupTheory.TwoConjugateCoreProductWithFixed
public import Theory.ElementaryAbelian.Join

/-!
# G₂ core factorization from the moving root-eight index

For Q=O₂(LT), the intrinsic block layer U is central in Q and contains
[Q,L]. Its quotient by C_U(L) has order 64; no assertion that U itself
is fixed-free is made. Two conjugate moving actors with centralizer index
at most eight and generating L modulo Q therefore give Q=U C_T(L).
The previously proved elementary centralizer then makes Q elementary.

This supplies the factorization and Frattini step of Aschbacher--Smith
3.3.28, printed p.601, from the moving-actor index and generation clauses.
The source assembly retains those clauses and the final odd-action contradiction.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The actual intrinsic layer has fixed-point index 64, retaining its central kernel. -/
theorem g2Two_blockU_fixed_index (hb : ChapterC.IsG2TwoBlock L) :
    (centralizer (L : Set G)).relIndex ((ChapterC.blockU L).map L.subtype) = 64 := by
  have he : ((ChapterC.blockU L).map L.subtype) ⊓ centralizer (L : Set G) =
      (ChapterC.blockU L ⊓ center L).map L.subtype := by
    ext x
    constructor
    · rintro ⟨⟨l,hl,rfl⟩,hc⟩
      exact ⟨l,⟨hl,mem_center_iff.mpr (fun k => Subtype.ext (hc k k.property))⟩,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨mem_map_of_mem L.subtype hl.1,
        fun k hk => congrArg Subtype.val (mem_center_iff.mp hl.2 ⟨k,hk⟩)⟩
  rw [← inf_relIndex_left ((ChapterC.blockU L).map L.subtype),he,
    relIndex_map_map_of_injective (ChapterC.blockU L ⊓ center L) (ChapterC.blockU L)
      L.subtype_injective,inf_relIndex_left]
  change (ChapterC.blockFixed L).index = 64
  rw [index_eq_card]
  exact hb.module_card

/-- Two moving root-eight index bounds force the literal local core to
factor, without a fixed-free assumption or a nonsplit-extension premise. -/
theorem g2Two_core_product_of_conjugate_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsG2TwoBlock L) (A : Subgroup G) (g : G) (hg : g ∈ L)
    (hgen : L ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊔
      (A ⊔ A.map (MulAut.conj g).toMonoidHom))
    (hi : (centralizer (A : Set G)).relIndex ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 8) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      (ChapterC.blockU L).map L.subtype ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let U := (ChapterC.blockU L).map L.subtype
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hLQ : L ≤ normalizer (Q : Set G) := le_sup_left.trans
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hQL : Q ≤ normalizer (L : Set G) := hQT.trans D.sylow_normalizes_component
  have hUQ : U ≤ Q := (blockU_le_blockOmegaModule h D hescape hb.short).trans
    (blockOmegaModule_le_core h)
  have hcentral : U ≤ centralizer (Q : Set G) := le_centralizer_iff.mp
    (hb.short.normalizing_twoGroup_centralizes_blockU (isPGroup_pCoreIn 2 _) hLQ hQL)
  have hcomm : ⁅Q,L⁆ ≤ U := by
    have hk : ⁅Q,L⁆ ≤ L.pCoreIn 2 := le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 _).to_le (le_normalizer_iff_commutator_le_left.mp hLQ))
      (le_normalizer_iff_commutator_le_right.mp hQL) (normalizer_commutator_ge_right Q L)
    rw [show U = ⁅L.pCoreIn 2,L⁆ from block_module_eq_commutator]
    exact (commutator_isPPerfect_idempotent L Q hb.short.twoPerfect
      (isPGroup_pCoreIn 2 _) hLQ).symm.le.trans (commutator_mono hk le_rfl)
  have hprod := core_product_of_two_conjugate_indices_with_fixed Q U L A
    (isPGroup_pCoreIn 2 _) hb.short.twoPerfect hUQ hcentral hcomm g (hLQ hg) hgen 8 hi
      (by rw [g2Two_blockU_fixed_index hb])
  have hCQ : (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ Q := by
    dsimp only [Q]
    rw [← hb.short.sylow_centralizer_blockU_eq_pCoreIn D.sylow_normalizes_component]
    exact inf_le_inf_left _ (centralizer_le (map_subtype_le _))
  have hC : Q ⊓ centralizer (L : Set G) = (T : Subgroup G) ⊓ centralizer (L : Set G) :=
    le_antisymm (inf_le_inf_right _ hQT) (le_inf hCQ inf_le_right)
  exact hprod.trans (congrArg (U ⊔ ·) hC)

/-- The same source inputs make the original local core elementary and
kill its Frattini subgroup, using the already established centralizer theorem. -/
theorem g2Two_core_elementary_of_conjugate_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsG2TwoBlock L) (A : Subgroup G) (g : G) (hg : g ∈ L)
    (hgen : L ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊔
      (A ⊔ A.map (MulAut.conj g).toMonoidHom))
    (hi : (centralizer (A : Set G)).relIndex ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 8) :
    IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      frattini ((L ⊔ (T : Subgroup G)).pCoreIn 2) = ⊥ := by
  have he : IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
    rw [g2Two_core_product_of_conjugate_index h D hescape hb A g hg hgen hi]
    let : IsElementaryAbelian 2 ((ChapterC.blockU L).map L.subtype) := hb.short.elementary.map _
    let : IsElementaryAbelian 2 ((T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) :=
      g2Two_sylow_centralizer_elementary h D hfixed hescape hb
    exact IsElementaryAbelian.sup_of_le_centralizer
      (inf_le_right.trans (centralizer_le (map_subtype_le _)))
  let : Fact (IsPGroup 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2)) := ⟨isPGroup_pCoreIn 2 _⟩
  exact ⟨he,(frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mpr he⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer

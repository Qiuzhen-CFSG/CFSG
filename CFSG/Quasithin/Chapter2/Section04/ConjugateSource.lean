module
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import CFSG.Quasithin.Chapter2.Section04.ConjugateEscape
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource

/-!
# Applying all marked block calculations to the selected Chapter 2 block

The actual index-two overgroup normalizes the selected Sylow group. With
R equal to that literal ambient Sylow and K₁ equal to the selected block,
the preceding C.5.3–4 marked action supplies the two-block configuration.
The source escape theorem now constructs the noncommuting right conjugator;
the preceding core-centralizer identity is proved before that choice. The A₅
C.5.6 factorization, both action indices and Frattini invariance then apply
without assuming that R normalizes K₁.

The preceding marked block construction remains with C.5.3–4. Both
alternating and rank-one branches now prove U₀=O₂(L₀) and O₂(H)=U₀D
with O₂(H) maximum elementary, discharging the intermediate core-centralizer
identity internally. No conclusion of 2.4.5 is a premise.
Source: Aschbacher–Smith, printed pp.155–160 and 527–528.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The actual selected block and index-two overgroup discharge the
normalizer input in the two-block alternating source factorization. -/
theorem MinimalBlockSetup.alternating_conjugate_source
    (d : MinimalBlockSetup M) (M₀ L₂ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (hblocks : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let K₁ := d.block.map d.H.subtype
    let S := ChapterB.baumann R
    let U₁ := sourceModule K₁
    let V := U₁.map (MulAut.conj x⁻¹).toMonoidHom
    let Q₁ := (K₁ ⊔ S).pCoreIn 2
    let D₁ := S ⊓ centralizer (K₁ : Set G)
    Q₁ = U₁ ⊔ D₁ ∧ D₁ ≤ centralizer (V : Set G) ∧
    S = V ⊔ Q₁ ∧ S = Q₁ ⊔ Q₁.map (MulAut.conj x⁻¹).toMonoidHom ∧
    (centralizer (V : Set G)).relIndex U₁ = 4 ∧
    (centralizer (U₁ : Set G)).relIndex V = 4 ∧
    ⁅U₁, S⁆ = ⁅U₁, V⁆ ∧ ⁅U₁, S⁆ = U₁ ⊓ centralizer (V : Set G) ∧
    ⁅U₁, S⁆ = U₁ ⊓ V ∧ (⁅U₁, S⁆ : Subgroup G).map (MulAut.conj x⁻¹).toMonoidHom = ⁅U₁, S⁆ ∧
    ((frattini D₁).map D₁.subtype).map (MulAut.conj x⁻¹).toMonoidHom =
      (frattini D₁).map D₁.subtype := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hxR : x ∈ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn hx
  have he := hblocks.commutator_structure x hxR hnc
  exact ⟨hblocks.product, hblocks.centralizer_centralizes_conjugate x hxR hnc,
    hblocks.first_factorization x hxR hnc, hblocks.core_conjugate_span x hxR hnc,
    hblocks.module_conjugate_index x hxR hnc, hblocks.conjugate_action_index x hxR hnc,
    he.1, he.2.1, he.2.2.1, he.2.2.2, hblocks.frattini_invariant x hxR hnc⟩
end CFSG.Quasithin.Chapter2

open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.rank_one_conjugate_source
    (d : MinimalBlockSetup M) (M₀ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    {F : Type*} [Field F]
    (hblock : RankOne.Setup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) F)
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let K₁ := d.block.map d.H.subtype
    let S := ChapterB.baumann R
    let U₁ := sourceModule K₁
    let V := U₁.map (MulAut.conj x⁻¹).toMonoidHom
    let Q₁ := (K₁ ⊔ S).pCoreIn 2
    let D₁ := S ⊓ centralizer (K₁ : Set G)
    let E₁ := ⁅U₁, S⁆
    Q₁ = U₁ ⊔ D₁ ∧ D₁ ≤ centralizer (V : Set G) ∧
    S = V ⊔ Q₁ ∧ S = Q₁ ⊔ Q₁.map (MulAut.conj x⁻¹).toMonoidHom ∧
    E₁ = ⁅U₁, V⁆ ∧ E₁ = U₁ ⊓ centralizer (V : Set G) ∧ E₁ = U₁ ⊓ V ∧
    E₁.map (MulAut.conj x⁻¹).toMonoidHom = E₁ ∧
    ((frattini D₁).map D₁.subtype).map (MulAut.conj x⁻¹).toMonoidHom =
      (frattini D₁).map D₁.subtype := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hxR : x ∈ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn hx
  exact hblock.source_conclusions hxR hnc
end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original normalizer equality in 2.4.4 supplies exactly C.5.2 for
an index-two overgroup of the selected Sylow subgroup. -/
theorem MinimalBlockSetup.no_common_normal_of_index_two
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ : Subgroup G)
    (_hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (W : Subgroup G) (hWS : W ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hHW : d.H ≤ normalizer (W : Set G)) (hMW : M₀ ≤ normalizer (W : Set G)) : W = ⊥ := by
  by_contra hW
  have hWH : W ≤ d.H := hWS.trans (map_subtype_le _)
  have hn : (W.subgroupOf d.H).Normal := (normal_subgroupOf_iff_le_normalizer hWH).mpr hHW
  have he := lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST W hW hWS hn
  have hMS : M₀ ≤ (d.S : Subgroup d.H).map d.H.subtype := (le_inf hM₀T hMW).trans he.le
  have hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 1 := relIndex_eq_one.mpr hMS
  omega
end CFSG.Quasithin.Chapter2

open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.alternating_maxFamily_of_index_two
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ L₂ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (hblocks : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (hRK : (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer (d.block.map d.H.subtype : Set G))
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let K := d.block.map d.H.subtype
    let S := ChapterB.baumann R
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := (K ⊔ S).pCoreIn 2
    let D := S ⊓ centralizer (K : Set G)
    ∃ B₀ B₁ : Subgroup G,
      Stellmacher.elementaryAbelianMaxSubgroups R = {Q, V ⊔ D, B₀, B₁} ∧
      (B₀.subgroupOf (K ⊔ S)).map hblocks.action = line 0 ∧
      (B₁.subgroupOf (K ⊔ S)).map hblocks.action = line 1 := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hM₀R : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn
  have hH : d.H = K ⊔ R := by
    change d.H = d.block.map d.H.subtype ⊔ (d.S : Subgroup d.H).map d.H.subtype
    rw [← Subgroup.map_sup, d.generated, ← MonoidHom.range_eq_map, range_subtype]
  exact hblocks.family_of_index_two d.H M₀ R hSM₀ hM₀R hRK hH
    (d.no_common_normal_of_index_two T hST M₀ hSM₀ hM₀T hindex) hindex x hx hnc
end CFSG.Quasithin.Chapter2

open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.alternating_source_family_of_index_two
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ L₂ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (hblocks : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (hRK : (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer (d.block.map d.H.subtype : Set G))
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let K := d.block.map d.H.subtype
    let S := ChapterB.baumann R
    let Q := (K ⊔ S).pCoreIn 2
    let D := S ⊓ centralizer (K : Set G)
    (frattini D).map D.subtype = ⊥ ∧ S = Stellmacher.elementaryAbelianMaxJ R ∧
    ∃ A : Subgroup G, ∃ r : G,
      r ∈ R ⊓ K ∧ r ∉ S ∧ Q.relIndex A = 2 ∧
      Stellmacher.elementaryAbelianMaxSubgroups R =
        {Q, Q.map (MulAut.conj x⁻¹).toMonoidHom, A, A.map (MulAut.conj r⁻¹).toMonoidHom} := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hM₀R : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn
  have hH : d.H = K ⊔ R := by
    change d.H = d.block.map d.H.subtype ⊔ (d.S : Subgroup d.H).map d.H.subtype
    rw [← Subgroup.map_sup, d.generated, ← MonoidHom.range_eq_map, range_subtype]
  have hphi := hblocks.frattini_eq_bot_of_index_two d.H M₀ R hSM₀ hM₀R hRK hH
    (d.no_common_normal_of_index_two T hST M₀ hSM₀ hM₀T hindex) hindex x hx hnc
  exact ⟨hphi, hblocks.baumann_eq_maxJ x (hM₀R hx) hnc hphi,
    hblocks.single_block_family hRK x (hM₀R hx) hnc hphi⟩
end CFSG.Quasithin.Chapter2

open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.alternating_two_block_product
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ L₂ : Subgroup G) (hL₂H : L₂ ≤ d.H)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (h₁ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (h₂ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      L₂ (d.block.map d.H.subtype))
    (ht : ∃ t : M₀, (t : G) ∈ (d.S : Subgroup d.H).map d.H.subtype ∧
      (d.block.map d.H.subtype).conjBy (t : G) = L₂)
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let K₁ := d.block.map d.H.subtype
    let S := ChapterB.baumann R
    let U := sourceModule K₁ ⊔ sourceModule L₂
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := S ⊓ centralizer (U : Set G)
    let D := S ⊓ centralizer ((K₁ ⊔ L₂ : Subgroup G) : Set G)
    Q = U ⊔ D ∧ D ≤ centralizer (V : Set G) ∧ S = (U ⊔ V) ⊔ D ∧
      (frattini D).map D.subtype = ⊥ ∧
      D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥ ∧ IsElementaryAbelian 2 Q := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hM₀R : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn
  have hHeq : d.H = K ⊔ R := by
    change d.H = d.block.map d.H.subtype ⊔ (d.S : Subgroup d.H).map d.H.subtype
    rw [← Subgroup.map_sup, d.generated, ← MonoidHom.range_eq_map, range_subtype]
  have hH : d.H = (K ⊔ L₂) ⊔ R := by
    apply le_antisymm
    · exact hHeq.le.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    · exact sup_le (sup_le (map_subtype_le _) hL₂H) (map_subtype_le _)
  have hRKL : R ≤ normalizer ((K ⊔ L₂ : Subgroup G) : Set G) := by
    intro r hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rw [Subgroup.map_sup]
      apply sup_le
      · rcases h₁.permutes r hr with he | he
        · exact he.le.trans le_sup_left
        · exact he.le.trans le_sup_right
      · rcases h₂.permutes r hr with he | he
        · exact he.le.trans le_sup_right
        · exact he.le.trans le_sup_left
    · exact (card_map_of_injective (MulAut.conj r).injective).ge
  exact h₁.two_block_source_product h₂ d.H M₀ R hSM₀ hM₀R hRKL hH
    (d.no_common_normal_of_index_two T hST M₀ hSM₀ hM₀T hindex)
    x hx hindex h₁.permutes ht hnc
end CFSG.Quasithin.Chapter2

open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.alternating_two_block_maximum_core
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ L₂ : Subgroup G) (hL₂H : L₂ ≤ d.H)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (h₁ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (h₂ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      L₂ (d.block.map d.H.subtype))
    (ht : ∃ t : M₀, (t : G) ∈ (d.S : Subgroup d.H).map d.H.subtype ∧
      (d.block.map d.H.subtype).conjBy (t : G) = L₂)
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let K₁ := d.block.map d.H.subtype
    let S := ChapterB.baumann R
    let U := sourceModule K₁ ⊔ sourceModule L₂
    let Q := S ⊓ centralizer (U : Set G)
    Q ∈ Stellmacher.elementaryAbelianMaxSubgroups R ∧
      S = Stellmacher.elementaryAbelianMaxJ R := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hM₀R : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn
  have hHeq : d.H = K ⊔ R := by
    change d.H = d.block.map d.H.subtype ⊔ (d.S : Subgroup d.H).map d.H.subtype
    rw [← Subgroup.map_sup, d.generated, ← MonoidHom.range_eq_map, range_subtype]
  have hH : d.H = (K ⊔ L₂) ⊔ R := by
    apply le_antisymm
    · exact hHeq.le.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    · exact sup_le (sup_le (map_subtype_le _) hL₂H) (map_subtype_le _)
  have hRKL : R ≤ normalizer ((K ⊔ L₂ : Subgroup G) : Set G) := by
    intro r hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rw [Subgroup.map_sup]
      apply sup_le
      · rcases h₁.permutes r hr with he | he
        · exact he.le.trans le_sup_left
        · exact he.le.trans le_sup_right
      · rcases h₂.permutes r hr with he | he
        · exact he.le.trans le_sup_right
        · exact he.le.trans le_sup_left
    · exact (card_map_of_injective (MulAut.conj r).injective).ge
  exact h₁.two_block_maximum_core h₂ d.H M₀ R hSM₀ hM₀R hRKL hH
    (d.no_common_normal_of_index_two T hST M₀ hSM₀ hM₀T hindex)
    x hx hindex h₁.permutes ht hnc
end CFSG.Quasithin.Chapter2

open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.alternating_two_block_invariant_family
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ L₂ : Subgroup G) (hL₂H : L₂ ≤ d.H)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (h₁ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (h₂ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      L₂ (d.block.map d.H.subtype))
    (ht : ∃ t : M₀, (t : G) ∈ (d.S : Subgroup d.H).map d.H.subtype ∧
      (d.block.map d.H.subtype).conjBy (t : G) = L₂)
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let K₁ := d.block.map d.H.subtype
    let S := ChapterB.baumann R
    let U := sourceModule K₁ ⊔ sourceModule L₂
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := S ⊓ centralizer (U : Set G)
    let D := S ⊓ centralizer ((K₁ ⊔ L₂ : Subgroup G) : Set G)
    Q ∈ Stellmacher.elementaryAbelianMaxSubgroups R ∧
      S = Stellmacher.elementaryAbelianMaxJ R ∧
      V ⊔ D = Q.map (MulAut.conj x⁻¹).toMonoidHom ∧
      {A ∈ Stellmacher.elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} =
        {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom} := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hM₀R : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn
  have hHeq : d.H = K ⊔ R := by
    change d.H = d.block.map d.H.subtype ⊔ (d.S : Subgroup d.H).map d.H.subtype
    rw [← Subgroup.map_sup, d.generated, ← MonoidHom.range_eq_map, range_subtype]
  have hH : d.H = (K ⊔ L₂) ⊔ R := by
    apply le_antisymm
    · exact hHeq.le.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    · exact sup_le (sup_le (map_subtype_le _) hL₂H) (map_subtype_le _)
  have hRKL : R ≤ normalizer ((K ⊔ L₂ : Subgroup G) : Set G) := by
    intro r hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rw [Subgroup.map_sup]
      apply sup_le
      · rcases h₁.permutes r hr with he | he
        · exact he.le.trans le_sup_left
        · exact he.le.trans le_sup_right
      · rcases h₂.permutes r hr with he | he
        · exact he.le.trans le_sup_right
        · exact he.le.trans le_sup_left
    · exact (card_map_of_injective (MulAut.conj r).injective).ge
  exact h₁.two_block_invariant_family h₂ d.H M₀ R le_rfl hSM₀ hM₀R hRKL hH
    (d.no_common_normal_of_index_two T hST M₀ hSM₀ hM₀T hindex)
    x hx hindex h₁.permutes ht hnc
end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2
open Subgroup ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The selected block's full two-core is its original commutator module. -/
theorem MinimalBlockSetup.alternating_block_core_eq_module
    (d : MinimalBlockSetup M) (M₀ L₂ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (hblocks : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    (d.block.map d.H.subtype).pCoreIn 2 = sourceModule (d.block.map d.H.subtype) := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hxR : x ∈ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn hx
  exact congrArg (fun N => N.map (d.block.map d.H.subtype).subtype)
    (hblocks.block_core_eq_module x hxR hnc)
end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2
open Subgroup ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.alternating_full_module_centralizer
    (d : MinimalBlockSetup M) (M₀ L₂ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (hblocks : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let K := d.block.map d.H.subtype
    R ⊓ centralizer (sourceModule K : Set G) = sourceModule K ⊔ (R ⊓ centralizer (K : Set G)) := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hxR : x ∈ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn hx
  exact hblocks.full_module_centralizer x hxR hnc
end CFSG.Quasithin.Chapter2

open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.rank_one_two_block_invariant_family
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ L₂ : Subgroup G) (hL₂H : L₂ ≤ d.H)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    {F F' : Type*} [Field F] [Field F']
    (hKL : L₂ ≤ centralizer (d.block.map d.H.subtype : Set G))
    (hpair : ∀ r ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy r = d.block.map d.H.subtype ∨
      (d.block.map d.H.subtype).conjBy r = L₂)
    (hpair' : ∀ r ∈ (d.S : Subgroup d.H).map d.H.subtype,
      L₂.conjBy r = L₂ ∨ L₂.conjBy r = d.block.map d.H.subtype)
    (h₁ : RankOne.Setup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) F)
    (h₂ : RankOne.Setup ((d.S : Subgroup d.H).map d.H.subtype)
      L₂ F')
    (ht : ∃ t : M₀, (t : G) ∈ (d.S : Subgroup d.H).map d.H.subtype ∧
      (d.block.map d.H.subtype).conjBy (t : G) = L₂)
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let K₁ := d.block.map d.H.subtype
    let S := ChapterB.baumann R
    let U := sourceModule K₁ ⊔ sourceModule L₂
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := S ⊓ centralizer (U : Set G)
    let D := S ⊓ centralizer ((K₁ ⊔ L₂ : Subgroup G) : Set G)
    Q ∈ Stellmacher.elementaryAbelianMaxSubgroups R ∧
      S = Stellmacher.elementaryAbelianMaxJ R ∧
      V ⊔ D = Q.map (MulAut.conj x⁻¹).toMonoidHom ∧
      {A ∈ Stellmacher.elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} =
        {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom} := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hM₀R : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn
  have hHeq : d.H = K ⊔ R := by
    change d.H = d.block.map d.H.subtype ⊔ (d.S : Subgroup d.H).map d.H.subtype
    rw [← Subgroup.map_sup, d.generated, ← MonoidHom.range_eq_map, range_subtype]
  have hH : d.H = (K ⊔ L₂) ⊔ R := by
    apply le_antisymm
    · exact hHeq.le.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    · exact sup_le (sup_le (map_subtype_le _) hL₂H) (map_subtype_le _)
  have hRKL : R ≤ normalizer ((K ⊔ L₂ : Subgroup G) : Set G) := by
    intro r hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rw [Subgroup.map_sup]
      apply sup_le
      · rcases hpair r hr with he | he
        · exact he.le.trans le_sup_left
        · exact he.le.trans le_sup_right
      · rcases hpair' r hr with he | he
        · exact he.le.trans le_sup_right
        · exact he.le.trans le_sup_left
    · exact (card_map_of_injective (MulAut.conj r).injective).ge
  exact h₁.two_block_invariant_family h₂ hKL d.H M₀ R hSM₀ hM₀R hRKL hH
    (d.no_common_normal_of_index_two T hST M₀ hSM₀ hM₀T hindex)
    x hx hindex hpair ht hnc
end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The actual selected block product has no extra two-core, and its full
Sylow centralizers already lie in the Baumann subgroup. -/
theorem MinimalBlockSetup.alternating_two_block_terminal
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ L₂ : Subgroup G) (hL₂H : L₂ ≤ d.H)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (h₁ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (h₂ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      L₂ (d.block.map d.H.subtype))
    (ht : ∃ t : M₀, (t : G) ∈ (d.S : Subgroup d.H).map d.H.subtype ∧
      (d.block.map d.H.subtype).conjBy (t : G) = L₂)
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let K₁ := d.block.map d.H.subtype
    let S := ChapterB.baumann R
    let U := sourceModule K₁ ⊔ sourceModule L₂
    let Q := S ⊓ centralizer (U : Set G)
    (K₁ ⊔ L₂).pCoreIn 2 = U ∧
      R ⊓ centralizer (U : Set G) = Q ∧
      R ⊓ centralizer ((K₁ ⊔ L₂ : Subgroup G) : Set G) =
        S ⊓ centralizer ((K₁ ⊔ L₂ : Subgroup G) : Set G) := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hM₀R : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn
  have hHeq : d.H = K ⊔ R := by
    change d.H = d.block.map d.H.subtype ⊔ (d.S : Subgroup d.H).map d.H.subtype
    rw [← Subgroup.map_sup, d.generated, ← MonoidHom.range_eq_map, range_subtype]
  have hH : d.H = (K ⊔ L₂) ⊔ R := by
    apply le_antisymm
    · exact hHeq.le.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    · exact sup_le (sup_le (map_subtype_le _) hL₂H) (map_subtype_le _)
  have hRKL : R ≤ normalizer ((K ⊔ L₂ : Subgroup G) : Set G) := by
    intro r hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rw [Subgroup.map_sup]
      apply sup_le
      · rcases h₁.permutes r hr with he | he
        · exact he.le.trans le_sup_left
        · exact he.le.trans le_sup_right
      · rcases h₂.permutes r hr with he | he
        · exact he.le.trans le_sup_right
        · exact he.le.trans le_sup_left
    · exact (card_map_of_injective (MulAut.conj r).injective).ge
  exact ⟨h₁.two_block_core_eq_module h₂ M₀ R x hx (hM₀R hx) hindex h₁.permutes ht hnc,
    h₁.two_block_full_centralizer_eq h₂ d.H M₀ R hSM₀ hSM₀ hM₀R hRKL hH
      (d.no_common_normal_of_index_two T hST M₀ hSM₀ hM₀T hindex)
      x hx hindex h₁.permutes ht hnc⟩
end CFSG.Quasithin.Chapter2

open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
private theorem sourceModule_map_injective {E : Type*} [Group E]
    (K : Subgroup E) (f : E →* G) (hf : Function.Injective f) :
    (sourceModule K).map f = sourceModule (K.map f) := by
  have hK : sourceModule K = ⁅K.pCoreIn 2,K⁆ := by
    unfold sourceModule ChapterC.blockU
    rw [map_commutator,← MonoidHom.range_eq_map,range_subtype]
    rfl
  have hmap : sourceModule (K.map f) = ⁅(K.map f).pCoreIn 2,K.map f⁆ := by
    unfold sourceModule ChapterC.blockU
    rw [map_commutator,← MonoidHom.range_eq_map,range_subtype]
    rfl
  rw [hK,hmap,map_commutator,map_pCoreIn_of_injective 2 K f hf]

omit [Finite G] in
private theorem pair_closure_map {E : Type*} [Group E]
    (A T : Subgroup E) (f : E →* G) (B : Subgroup G)
    (hp : ∀ g ∈ T.map f, (A.map f).conjBy g = A.map f ∨ (A.map f).conjBy g = B)
    (ht : ∃ t ∈ T.map f, (A.map f).conjBy t = B) :
    (⨆ t : T, A.map (MulAut.conj (t : E)).toMonoidHom).map f = A.map f ⊔ B := by
  have hm (t : E) : (A.map (MulAut.conj t).toMonoidHom).map f = (A.map f).conjBy (f t) := by
    change (A.map (MulAut.conj t).toMonoidHom).map f = (A.map f).map (MulAut.conj (f t)).toMonoidHom
    rw [map_map,map_map]
    congr 1
    ext a
    simp [MulAut.conj_apply]
  apply le_antisymm
  · rw [Subgroup.map_iSup]
    apply iSup_le
    intro t
    rw [hm]
    rcases hp (f t) (mem_map_of_mem f t.property) with he | he
    · exact he.le.trans le_sup_left
    · exact he.le.trans le_sup_right
  · apply sup_le
    · exact map_mono (le_iSup_conjugates A T)
    · obtain ⟨t,⟨a,ha,rfl⟩,he⟩ := ht
      rw [← he,← hm,Subgroup.map_iSup]
      exact le_iSup (fun t : T => (A.map (MulAut.conj (t : E)).toMonoidHom).map f) ⟨a,ha⟩

omit [Finite G] in
/-- Identify the literal selected block closure and module closure with the
actual pair supplied by the preceding two-block construction. -/
theorem MinimalBlockSetup.two_block_closures
    (d : MinimalBlockSetup M) (L : Subgroup G)
    (hp : ∀ g ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy g = d.block.map d.H.subtype ∨
      (d.block.map d.H.subtype).conjBy g = L)
    (ht : ∃ t ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy t = L) :
    d.L0.map d.H.subtype = d.block.map d.H.subtype ⊔ L ∧
      d.U0.map d.H.subtype = sourceModule (d.block.map d.H.subtype) ⊔ sourceModule L := by
  refine ⟨pair_closure_map d.block (d.S : Subgroup d.H) d.H.subtype L hp ht,?_⟩
  have hm : (sourceModule d.block).map d.H.subtype = sourceModule (d.block.map d.H.subtype) :=
    sourceModule_map_injective _ _ d.H.subtype_injective
  have hpU : ∀ g ∈ (d.S : Subgroup d.H).map d.H.subtype,
      ((sourceModule d.block).map d.H.subtype).conjBy g = (sourceModule d.block).map d.H.subtype ∨
      ((sourceModule d.block).map d.H.subtype).conjBy g = sourceModule L := by
    intro g hg
    rw [hm]
    have he := sourceModule_map_equiv (d.block.map d.H.subtype) (MulAut.conj g)
    rcases hp g hg with h0 | h1
    · exact Or.inl (he.trans (congrArg sourceModule h0))
    · exact Or.inr (he.trans (congrArg sourceModule h1))
  have htU : ∃ t ∈ (d.S : Subgroup d.H).map d.H.subtype,
      ((sourceModule d.block).map d.H.subtype).conjBy t = sourceModule L := by
    obtain ⟨t,ht,he⟩ := ht
    refine ⟨t,ht,?_⟩
    rw [hm]
    exact (sourceModule_map_equiv _ (MulAut.conj t)).trans (congrArg sourceModule he)
  exact (pair_closure_map (sourceModule d.block) (d.S : Subgroup d.H) d.H.subtype (sourceModule L) hpU htU).trans
    (congrArg (fun A => A ⊔ sourceModule L) hm)

/-- The literal source 2.4.5(4) identity in the two-block A₅ branch. -/
theorem MinimalBlockSetup.alternating_U0_eq_twoCore_L0
    (d : MinimalBlockSetup M) (M₀ L₂ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (h₁ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (h₂ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      L₂ (d.block.map d.H.subtype))
    (ht : ∃ t : M₀, (t : G) ∈ (d.S : Subgroup d.H).map d.H.subtype ∧
      (d.block.map d.H.subtype).conjBy (t : G) = L₂)
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    d.U0 = d.L0.pCoreIn 2 := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hM₀R : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn
  have hc := d.two_block_closures L₂ h₁.permutes (by
    obtain ⟨t,ht,he⟩ := ht
    exact ⟨t,ht,he⟩)
  apply map_injective d.H.subtype_injective
  rw [map_pCoreIn_of_injective 2 d.L0 d.H.subtype d.H.subtype_injective,hc.1,hc.2]
  exact (h₁.two_block_core_eq_module h₂ M₀ R x hx (hM₀R hx) hindex h₁.permutes ht hnc).symm

/-- The local core fixes the entire actual conjugate-generated module. -/
theorem MinimalBlockSetup.core_centralizes_U0 (d : MinimalBlockSetup M) :
    twoCore d.H ≤ centralizer (d.U0.map d.H.subtype : Set G) := by
  have hc : d.U0 ≤ centralizer (pCore 2 d.H : Set d.H) :=
    iSup_conjugates_le_of_le_normalizer _ _ _
      (le_centralizer_iff.mp d.block_type.1.core_centralizes_blockU) le_normalizer_of_normal
  exact le_centralizer_iff.mp ((map_mono hc).trans
    (map_centralizer_le_centralizer_image _ d.H.subtype))

/-- The source product equality implies the full local core identity; it is
not retained as a C.5.4 premise in the literal Chapter 2 application. -/
private theorem MinimalBlockSetup.core_eq_of_module_core_and_centralizer
    (d : MinimalBlockSetup M) (hU : d.U0 = d.L0.pCoreIn 2)
    (hc : (d.S : Subgroup d.H).map d.H.subtype ⊓ centralizer (d.U0.map d.H.subtype : Set G) =
      d.U0.map d.H.subtype ⊔ ((d.S : Subgroup d.H).map d.H.subtype ⊓
        centralizer (d.L0.map d.H.subtype : Set G))) :
    twoCore d.H = d.U0.map d.H.subtype ⊔ ((d.S : Subgroup d.H).map d.H.subtype ⊓
      centralizer (d.L0.map d.H.subtype : Set G)) := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.L0.map d.H.subtype
  let U := d.U0.map d.H.subtype
  let D := R ⊓ centralizer (L : Set G)
  have hHL : d.H ≤ normalizer (L : Set G) := by
    let := d.L0_normal
    intro g hg
    have hn : (⟨g,hg⟩ : d.H) ∈ normalizer (d.L0 : Set d.H) := by
      rw [normalizer_eq_top]
      trivial
    exact (d.L0.le_normalizer_map d.H.subtype) (mem_map_of_mem d.H.subtype hn)
  have hUcore : U = L.pCoreIn 2 := by
    change d.U0.map d.H.subtype = (d.L0.map d.H.subtype).pCoreIn 2
    rw [hU,map_pCoreIn_of_injective 2 d.L0 d.H.subtype d.H.subtype_injective]
  have hHU : d.H ≤ normalizer (U : Set G) := by
    rw [hUcore]
    exact hHL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hRD : R ≤ normalizer (D : Set G) :=
    (le_inf R.le_normalizer (((map_subtype_le _).trans hHL).trans
      (normalizer_le_normalizer_centralizer L))).trans inf_normalizer_le_normalizer_inf
  have hLD : L ≤ normalizer (D : Set G) :=
    (le_centralizer_iff.mp (show D ≤ centralizer (L : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hHD : d.H ≤ normalizer (D : Set G) := by
    rw [← d.ambient_L0_sup_sylow]
    exact sup_le hLD hRD
  apply le_antisymm
  · exact (le_inf (pCoreIn_le_sylow d.H d.S) d.core_centralizes_U0).trans_eq hc
  · apply le_pCoreIn_of_normalizes
      ((d.S.isPGroup'.map d.H.subtype).to_le (show U ⊔ D ≤ R from hc.symm.le.trans inf_le_left))
      (sup_le (map_subtype_le _) (inf_le_left.trans (map_subtype_le _)))
    exact (le_inf hHU hHD).trans (normalizer_inf_normalizer_le_normalizer_sup U D)

/-- Source 2.4.5(2a),(4) on the actual selected two-block A₅ configuration.
The preceding core-centralizer identity is proved internally. -/
theorem MinimalBlockSetup.alternating_lemma_2_4_5_2a_4
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ L₂ : Subgroup G) (hL₂H : L₂ ≤ d.H)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (h₁ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (h₂ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      L₂ (d.block.map d.H.subtype))
    (ht : ∃ t : M₀, (t : G) ∈ (d.S : Subgroup d.H).map d.H.subtype ∧
      (d.block.map d.H.subtype).conjBy (t : G) = L₂)
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let U₀ := d.U0.map d.H.subtype
    let D := R ⊓ centralizer (d.L0.map d.H.subtype : Set G)
    d.U0 = d.L0.pCoreIn 2 ∧ twoCore d.H = U₀ ⊔ D ∧
      twoCore d.H ∈ Stellmacher.elementaryAbelianMaxSubgroups R := by
  have hc := d.two_block_closures L₂ h₁.permutes (by
    obtain ⟨t,ht,he⟩ := ht
    exact ⟨t,ht,he⟩)
  have hU := d.alternating_U0_eq_twoCore_L0 M₀ L₂ hSM₀ hindex h₁ h₂ ht x hx hnc
  have ht' := d.alternating_two_block_terminal T hST M₀ L₂ hL₂H hSM₀ hM₀T hindex h₁ h₂ ht x hx hnc
  have hp := d.alternating_two_block_product T hST M₀ L₂ hL₂H hSM₀ hM₀T hindex h₁ h₂ ht x hx hnc
  have hm := d.alternating_two_block_maximum_core T hST M₀ L₂ hL₂H hSM₀ hM₀T hindex h₁ h₂ ht x hx hnc
  have hC : (d.S : Subgroup d.H).map d.H.subtype ⊓ centralizer (d.U0.map d.H.subtype : Set G) =
      d.U0.map d.H.subtype ⊔ ((d.S : Subgroup d.H).map d.H.subtype ⊓
        centralizer (d.L0.map d.H.subtype : Set G)) := by
    rw [hc.1,hc.2,ht'.2.1,ht'.2.2]
    exact hp.1
  have hcore := d.core_eq_of_module_core_and_centralizer hU hC
  refine ⟨hU,hcore,?_⟩
  rw [hcore,hc.1,hc.2,ht'.2.2,← hp.1]
  exact hm.1
end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
/-- A normal original block has just one conjugate in both source closures. -/
theorem MinimalBlockSetup.single_block_closures (d : MinimalBlockSetup M)
    (hRK : (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer (d.block.map d.H.subtype : Set G)) :
    d.L0.map d.H.subtype = d.block.map d.H.subtype ∧
      d.U0.map d.H.subtype = sourceModule (d.block.map d.H.subtype) := by
  have hc := d.two_block_closures (d.block.map d.H.subtype)
    (fun g hg => Or.inl (mem_normalizer_iff_map_conj_eq.mp (hRK hg)))
    ⟨1,one_mem _,Subgroup.conjBy_one _⟩
  simpa only [sup_idem] using hc

/-- Source 2.4.5(2a),(4) on the actual selected single A₅ block. -/
theorem MinimalBlockSetup.alternating_single_lemma_2_4_5_2a_4
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ L₂ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (hblocks : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (hRK : (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer (d.block.map d.H.subtype : Set G))
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let U₀ := d.U0.map d.H.subtype
    let D := R ⊓ centralizer (d.L0.map d.H.subtype : Set G)
    d.U0 = d.L0.pCoreIn 2 ∧ twoCore d.H = U₀ ⊔ D ∧
      twoCore d.H ∈ Stellmacher.elementaryAbelianMaxSubgroups R := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hM₀R : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn
  have hH : d.H = K ⊔ R := by
    change d.H = d.block.map d.H.subtype ⊔ (d.S : Subgroup d.H).map d.H.subtype
    rw [← Subgroup.map_sup, d.generated, ← MonoidHom.range_eq_map, range_subtype]
  have hc := d.single_block_closures hRK
  have hU : d.U0 = d.L0.pCoreIn 2 := by
    apply map_injective d.H.subtype_injective
    rw [map_pCoreIn_of_injective 2 d.L0 d.H.subtype d.H.subtype_injective,hc.1,hc.2]
    change sourceModule K = (pCore 2 K).map K.subtype
    rw [hblocks.block_core_eq_module x (hM₀R hx) hnc]
    rfl
  have ht := hblocks.single_block_full_centralizer_eq hRK d.H M₀ R hSM₀ hM₀R hRK hH
    (d.no_common_normal_of_index_two T hST M₀ hSM₀ hM₀T hindex) x hx hindex hnc
  have hC : R ⊓ centralizer (d.U0.map d.H.subtype : Set G) =
      d.U0.map d.H.subtype ⊔ (R ⊓ centralizer (d.L0.map d.H.subtype : Set G)) := by
    rw [hc.1,hc.2,ht.1,ht.2]
    exact hblocks.core.symm.trans hblocks.product
  have hcore := d.core_eq_of_module_core_and_centralizer hU hC
  have hf := d.alternating_source_family_of_index_two T hST M₀ L₂ hSM₀ hM₀T hindex hblocks hRK x hx hnc
  obtain ⟨A,r,_,_,_,hfam⟩ := hf.2.2
  refine ⟨hU,hcore,?_⟩
  rw [hcore,hc.1,hc.2,ht.2,← hblocks.product,hfam]
  exact Set.mem_insert _ _
end CFSG.Quasithin.Chapter2

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.U0_normal (d : MinimalBlockSetup M) : d.U0.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← d.generated]
  refine sup_le ?_ d.sylow_normalizes_U0
  apply le_normalizer_iff_commutator_le_left.mpr
  exact (commutator_mono d.U0_le_core le_rfl).trans
    ((commutator_comm _ _).le.trans d.block_commutator_core_le_U0)

omit [Finite G] in
private theorem commuting_block_module_centralizer_le (K L : Subgroup G)
    (hK : ChapterC.IsShort K) (hL : ChapterC.IsShort L)
    (hc : L ≤ centralizer (K : Set G)) :
    (K ⊔ L) ⊓ centralizer (sourceModule K ⊔ sourceModule L : Subgroup G) ≤
      K.pCoreIn 2 ⊔ L.pCoreIn 2 := by
  rintro a ⟨ha,hac⟩
  have hm : a ∈ (K : Set G) * (L : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left K L (hc.trans (Subgroup.centralizer_le_normalizer _))]
    exact ha
  obtain ⟨k,hk,l,hl,rfl⟩ := hm
  have hkC : k ∈ centralizer (sourceModule K : Set G) := by
    have hh := (centralizer (sourceModule K : Set G)).mul_mem
      (centralizer_le (show sourceModule K ≤ sourceModule K ⊔ sourceModule L from le_sup_left) hac)
      ((centralizer (sourceModule K : Set G)).inv_mem ((centralizer_le (map_subtype_le _)) (hc hl)))
    simpa only [mul_inv_cancel_right] using hh
  have hlC : l ∈ centralizer (sourceModule L : Set G) := by
    have hh := (centralizer (sourceModule L : Set G)).mul_mem
      ((centralizer (sourceModule L : Set G)).inv_mem ((centralizer_le (map_subtype_le _)) ((le_centralizer_iff.mp hc) hk)))
      (centralizer_le (show sourceModule L ≤ sourceModule K ⊔ sourceModule L from le_sup_right) hac)
    simpa only [inv_mul_cancel_left] using hh
  have hkP : (⟨k,hk⟩ : K) ∈ pCore 2 K := by
    rw [← hK.centralizer_blockU]
    intro u hu
    exact Subtype.ext (hkC u (mem_map_of_mem K.subtype hu))
  have hlP : (⟨l,hl⟩ : L) ∈ pCore 2 L := by
    rw [← hL.centralizer_blockU]
    intro u hu
    exact Subtype.ext (hlC u (mem_map_of_mem L.subtype hu))
  exact mul_mem_sup (mem_map_of_mem K.subtype hkP) (mem_map_of_mem L.subtype hlP)

private theorem MinimalBlockSetup.core_centralizer_of_isPGroup
    (d : MinimalBlockSetup M) (P : Subgroup G) (hP : IsPGroup 2 P)
    (hLC : d.L0.map d.H.subtype ⊓ centralizer (d.U0.map d.H.subtype : Set G) ≤ P) :
    (d.S : Subgroup d.H).map d.H.subtype ⊓ centralizer (d.U0.map d.H.subtype : Set G) =
      twoCore d.H := by
  let U := d.U0.map d.H.subtype
  let C := d.H ⊓ centralizer (U : Set G)
  let := d.L0_normal
  have hquot : IsPGroup 2 (d.H ⧸ d.L0) := by
    exact (isPGroup_quotient_pResidual (G := d.H) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq d.L0_eq_residual).symm
  have hC : IsPGroup 2 C := by
    intro a
    let aH : d.H := ⟨a,a.property.1⟩
    obtain ⟨n,hn⟩ := hquot (QuotientGroup.mk' d.L0 aH)
    have haL : aH ^ 2^n ∈ d.L0 := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' d.L0 (aH ^ 2^n) = 1
      rwa [map_pow]
    have haP : (a : G) ^ 2^n ∈ P := hLC
      ⟨mem_map_of_mem d.H.subtype haL,(centralizer (U : Set G)).pow_mem a.property.2 _⟩
    obtain ⟨m,hm⟩ := hP ⟨_,haP⟩
    refine ⟨n+m,Subtype.ext ?_⟩
    change (a : G) ^ 2^(n+m) = 1
    rw [pow_add,pow_mul]
    exact congrArg (fun p : P => (p : G)) hm
  have hHU : d.H ≤ normalizer (U : Set G) := by
    let := d.U0_normal
    intro g hg
    have hn : (⟨g,hg⟩ : d.H) ∈ normalizer (d.U0 : Set d.H) := by
      rw [normalizer_eq_top]
      trivial
    exact (d.U0.le_normalizer_map d.H.subtype) (mem_map_of_mem d.H.subtype hn)
  have hHC : d.H ≤ normalizer (C : Set G) :=
    (le_inf d.H.le_normalizer (hHU.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  apply le_antisymm
  · exact (inf_le_inf (map_subtype_le _) le_rfl).trans (le_pCoreIn_of_normalizes hC inf_le_left hHC)
  · exact le_inf (pCoreIn_le_sylow d.H d.S) d.core_centralizes_U0

/-- C.5.4.4 on the literal two-block source, proved before choosing a conjugator. -/
theorem MinimalBlockSetup.two_block_core_centralizer
    (d : MinimalBlockSetup M) (L : Subgroup G)
    (hK : ChapterC.IsShort (d.block.map d.H.subtype)) (hL : ChapterC.IsShort L)
    (hcomm : L ≤ centralizer (d.block.map d.H.subtype : Set G))
    (hp : ∀ g ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy g = d.block.map d.H.subtype ∨
      (d.block.map d.H.subtype).conjBy g = L)
    (ht : ∃ t ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy t = L) :
    (d.S : Subgroup d.H).map d.H.subtype ⊓ centralizer (d.U0.map d.H.subtype : Set G) =
      twoCore d.H := by
  let K := d.block.map d.H.subtype
  let P := K.pCoreIn 2 ⊔ L.pCoreIn 2
  let U := d.U0.map d.H.subtype
  have hclosure := d.two_block_closures L hp ht
  have hcommP : L.pCoreIn 2 ≤ centralizer (K.pCoreIn 2 : Set G) :=
    (pCoreIn_le 2 L).trans (hcomm.trans (centralizer_le (pCoreIn_le 2 K)))
  have hP : IsPGroup 2 P := (isPGroup_pCoreIn 2 K).to_sup_of_normal_left'
    (isPGroup_pCoreIn 2 L) (hcommP.trans (Subgroup.centralizer_le_normalizer _))
  have hLC : d.L0.map d.H.subtype ⊓ centralizer (U : Set G) ≤ P := by
    change d.L0.map d.H.subtype ⊓ centralizer (d.U0.map d.H.subtype : Set G) ≤ P
    rw [hclosure.1,hclosure.2]
    exact commuting_block_module_centralizer_le K L hK hL hcomm
  exact d.core_centralizer_of_isPGroup P hP hLC

omit [Finite G] in
private theorem noncommuting_seed_of_span
    (A U M : Subgroup G) (hUW : U ≤ conjugateSpanBy A M)
    (x : G) (hx : x ∈ M)
    (hnc : ¬ U.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U : Set G)) :
    ∃ y ∈ M, ¬ A.map (MulAut.conj y⁻¹).toMonoidHom ≤ centralizer (A : Set G) := by
  classical
  by_contra! hall
  let W := conjugateSpanBy A M
  have hWA : W ≤ centralizer (A : Set G) := by
    apply (closure_le _).mpr
    rintro g ⟨m,hm,a,ha,rfl⟩
    have hh := hall m⁻¹ (M.inv_mem hm)
    simp only [inv_inv] at hh
    exact hh (mem_map_of_mem (MulAut.conj m).toMonoidHom ha)
  have hW : IsMulCommutative W := (conjugateSpanBy_commutative_iff A M).mpr (le_centralizer_iff.mp hWA)
  have hxW : W.map (MulAut.conj x⁻¹).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy A M (M.inv_mem hx))
  exact hnc (((map_mono hUW).trans_eq hxW).trans
    ((le_centralizer_iff_isMulCommutative.mpr hW).trans (centralizer_le hUW)))

/-- Construct the original noncommuting conjugator from the actual source
escape and block orbit. No terminal core or conjugate-family identity is used. -/
theorem MinimalBlockSetup.exists_two_block_noncommuting
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ L : Subgroup G)
    (hRM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (hK : ChapterC.IsShort (d.block.map d.H.subtype)) (hL : ChapterC.IsShort L)
    (hcomm : L ≤ centralizer (d.block.map d.H.subtype : Set G))
    (hp : ∀ g ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy g = d.block.map d.H.subtype ∨
      (d.block.map d.H.subtype).conjBy g = L)
    (ht : ∃ t ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy t = L) :
    ∃ x ∈ M₀, ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G) := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  let U := d.U0.map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hMR : M₀ ≤ normalizer (R : Set G) := (normal_subgroupOf_iff_le_normalizer hRM).mp hn
  have hlt : R < M₀ := lt_of_le_of_ne hRM (by
    intro he
    have hi : R.relIndex M₀ = 1 := relIndex_eq_one.mpr he.ge
    have hi2 : R.relIndex M₀ = 2 := hindex
    omega)
  obtain ⟨x,hx,_,hescape⟩ := d.exists_U0_conjugate_escape T hST M₀ hlt hMT hMR
  have hc := d.two_block_core_centralizer L hK hL hcomm hp ht
  have hnc : ¬ U.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U : Set G) := by
    intro h
    have hUR : U ≤ R := (map_mono d.U0_le_core).trans (pCoreIn_le_sylow d.H d.S)
    have hRx : R.map (MulAut.conj x⁻¹).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp (hMR (M₀.inv_mem hx))
    exact hescape ((le_inf ((map_mono hUR).trans_eq hRx) h).trans_eq hc)
  apply noncommuting_seed_of_span (sourceModule K) U M₀ ?_ x hx hnc
  have hcl := d.two_block_closures L hp ht
  change d.U0.map d.H.subtype ≤ _
  rw [hcl.2]
  refine sup_le (le_conjugateSpanBy _ _) ?_
  obtain ⟨t,ht,he⟩ := ht
  have heU : (sourceModule K).map (MulAut.conj t).toMonoidHom = sourceModule L :=
    (sourceModule_map_equiv K (MulAut.conj t)).trans (congrArg sourceModule he)
  rw [← heU]
  exact (map_mono (le_conjugateSpanBy _ _)).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy _ _ (hRM ht)))

/-- The preceding core identity in the single-block configuration. -/
theorem MinimalBlockSetup.single_block_core_centralizer
    (d : MinimalBlockSetup M)
    (hK : ChapterC.IsShort (d.block.map d.H.subtype))
    (hRK : (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer (d.block.map d.H.subtype : Set G)) :
    (d.S : Subgroup d.H).map d.H.subtype ⊓ centralizer (d.U0.map d.H.subtype : Set G) =
      twoCore d.H := by
  let K := d.block.map d.H.subtype
  apply d.core_centralizer_of_isPGroup (K.pCoreIn 2) (isPGroup_pCoreIn 2 K)
  have hc := d.single_block_closures hRK
  rw [hc.1,hc.2]
  rintro g ⟨hg,hc⟩
  have hp : (⟨g,hg⟩ : K) ∈ pCore 2 K := by
    rw [← hK.centralizer_blockU]
    intro u hu
    exact Subtype.ext (hc u (mem_map_of_mem K.subtype hu))
  exact mem_map_of_mem K.subtype hp

theorem MinimalBlockSetup.exists_single_block_noncommuting
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ : Subgroup G)
    (hRM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (hK : ChapterC.IsShort (d.block.map d.H.subtype))
    (hRK : (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer (d.block.map d.H.subtype : Set G)) :
    ∃ x ∈ M₀, ¬ (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule (d.block.map d.H.subtype) : Set G) := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let U := d.U0.map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hMR : M₀ ≤ normalizer (R : Set G) := (normal_subgroupOf_iff_le_normalizer hRM).mp hn
  have hlt : R < M₀ := lt_of_le_of_ne hRM (by
    intro he
    have hi : R.relIndex M₀ = 1 := relIndex_eq_one.mpr he.ge
    have hi2 : R.relIndex M₀ = 2 := hindex
    omega)
  obtain ⟨x,hx,_,hescape⟩ := d.exists_U0_conjugate_escape T hST M₀ hlt hMT hMR
  have hc := d.single_block_core_centralizer hK hRK
  have hcl : U = sourceModule (d.block.map d.H.subtype) := (d.single_block_closures hRK).2
  refine ⟨x,hx,?_⟩
  rw [← hcl]
  intro h
  have hUR : U ≤ R := (map_mono d.U0_le_core).trans (pCoreIn_le_sylow d.H d.S)
  have hRx : R.map (MulAut.conj x⁻¹).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (hMR (M₀.inv_mem hx))
  exact hescape ((le_inf ((map_mono hUR).trans_eq hRx) h).trans_eq hc)

/-- The literal core conclusions with the conjugator constructed internally. -/
theorem MinimalBlockSetup.alternating_two_block_core_source
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ L₂ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (h₁ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (h₂ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      L₂ (d.block.map d.H.subtype))
    (ht : ∃ t : M₀, (t : G) ∈ (d.S : Subgroup d.H).map d.H.subtype ∧
      (d.block.map d.H.subtype).conjBy (t : G) = L₂)
 :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let U₀ := d.U0.map d.H.subtype
    let D := R ⊓ centralizer (d.L0.map d.H.subtype : Set G)
    d.U0 = d.L0.pCoreIn 2 ∧ twoCore d.H = U₀ ⊔ D ∧
      twoCore d.H ∈ Stellmacher.elementaryAbelianMaxSubgroups R := by
  have ht' : ∃ t ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy t = L₂ := by
    obtain ⟨t,ht,he⟩ := ht
    exact ⟨t,ht,he⟩
  have hc := d.two_block_closures L₂ h₁.permutes ht'
  have hL₂H : L₂ ≤ d.H := (le_sup_right.trans_eq hc.1.symm).trans (map_subtype_le _)
  obtain ⟨x,hx,hnc⟩ := d.exists_two_block_noncommuting T hST M₀ L₂ hSM₀ hM₀T hindex
    h₁.block.2.1 h₂.block.2.1 h₁.commute h₁.permutes ht'
  exact d.alternating_lemma_2_4_5_2a_4 T hST M₀ L₂ hL₂H hSM₀ hM₀T hindex h₁ h₂ ht x hx hnc

/-- The literal core conclusions with the conjugator constructed internally. -/
theorem MinimalBlockSetup.alternating_single_block_core_source
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ L₂ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (hblocks : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) L₂)
    (hRK : (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer (d.block.map d.H.subtype : Set G))
 :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let U₀ := d.U0.map d.H.subtype
    let D := R ⊓ centralizer (d.L0.map d.H.subtype : Set G)
    d.U0 = d.L0.pCoreIn 2 ∧ twoCore d.H = U₀ ⊔ D ∧
      twoCore d.H ∈ Stellmacher.elementaryAbelianMaxSubgroups R := by
  obtain ⟨x,hx,hnc⟩ := d.exists_single_block_noncommuting T hST M₀ hSM₀ hM₀T hindex hblocks.block.2.1 hRK
  exact d.alternating_single_lemma_2_4_5_2a_4 T hST M₀ L₂ hSM₀ hM₀T hindex hblocks hRK x hx hnc
end CFSG.Quasithin.Chapter2

open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original rank-one pair proves 2.4.5(2a),(4), including the nonsplit
natural covers. The original escape constructs the conjugator internally. -/
theorem MinimalBlockSetup.rank_one_two_block_core_source
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ L₂ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    {F F' : Type*} [Field F] [Field F']
    (hKL : L₂ ≤ centralizer (d.block.map d.H.subtype : Set G))
    (hpair : ∀ r ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy r = d.block.map d.H.subtype ∨
      (d.block.map d.H.subtype).conjBy r = L₂)
    (h₁ : RankOne.Setup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) F)
    (h₂ : RankOne.Setup ((d.S : Subgroup d.H).map d.H.subtype) L₂ F')
    (ht : ∃ t : M₀, (t : G) ∈ (d.S : Subgroup d.H).map d.H.subtype ∧
      (d.block.map d.H.subtype).conjBy (t : G) = L₂) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let U₀ := d.U0.map d.H.subtype
    let D := R ⊓ centralizer (d.L0.map d.H.subtype : Set G)
    d.U0 = d.L0.pCoreIn 2 ∧ twoCore d.H = U₀ ⊔ D ∧
      twoCore d.H ∈ Stellmacher.elementaryAbelianMaxSubgroups R := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  have ht' : ∃ t ∈ R, K.conjBy t = L₂ := by
    obtain ⟨t,ht,he⟩ := ht
    exact ⟨t,ht,he⟩
  have hc := d.two_block_closures L₂ hpair ht'
  have hL₂H : L₂ ≤ d.H := (le_sup_right.trans_eq hc.1.symm).trans (map_subtype_le _)
  obtain ⟨x,hx,hnc⟩ := d.exists_two_block_noncommuting T hST M₀ L₂ hSM₀ hM₀T hindex
    h₁.short h₂.short hKL hpair ht'
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hM₀R : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn
  have hR : IsPGroup 2 R := d.S.isPGroup'.map d.H.subtype
  have hHeq : d.H = K ⊔ R := by
    change d.H = d.block.map d.H.subtype ⊔ (d.S : Subgroup d.H).map d.H.subtype
    rw [← Subgroup.map_sup,d.generated,← MonoidHom.range_eq_map,range_subtype]
  have hH : d.H = (K ⊔ L₂) ⊔ R := by
    apply le_antisymm
    · exact hHeq.le.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    · exact sup_le (sup_le (map_subtype_le _) hL₂H) (map_subtype_le _)
  have hRKL : R ≤ normalizer (K ⊔ L₂ : Subgroup G) := by
    rw [← hc.1]
    let := d.L0_normal
    exact (map_mono (show (d.S : Subgroup d.H) ≤ normalizer (d.L0 : Set d.H) by
      rw [normalizer_eq_top]; exact le_top)).trans (d.L0.le_normalizer_map d.H.subtype)
  have hno := d.no_common_normal_of_index_two T hST M₀ hSM₀ hM₀T hindex
  have hs := h₁.source_two_block_terminal h₂ hR hKL d.H M₀ R le_rfl hSM₀ hM₀R hRKL hH hno
    x hx hindex hpair ht hnc
  have he := h₁.source_two_block_terminal_equalities h₂ hR hKL d.H M₀ R le_rfl hSM₀ hM₀R hRKL hH hno
    x hx hindex hpair ht hnc
  have hm := h₁.two_block_maximum_core h₂ hKL d.H M₀ R hSM₀ hM₀R hRKL hH hno x hx hindex hpair ht hnc
  have hCore := d.two_block_core_centralizer L₂ h₁.short h₂.short hKL hpair ht'
  have hU : d.U0 = d.L0.pCoreIn 2 := by
    apply map_injective d.H.subtype_injective
    rw [map_pCoreIn_of_injective 2 d.L0 d.H.subtype d.H.subtype_injective,hc.1,hc.2]
    exact hs.1.symm
  refine ⟨hU,?_,?_⟩
  · rw [← hCore,hc.1,hc.2]
    exact hs.2.1
  · rw [← hCore,hc.2]
    change R ⊓ centralizer (RankOne.U K ⊔ RankOne.U L₂ : Subgroup G) ∈
      Stellmacher.elementaryAbelianMaxSubgroups R
    rw [he.2.1]
    exact hm.1

/-- The single original rank-one block proves the same literal core assertions,
with both its Sylow witness and the escaping conjugator constructed internally. -/
theorem MinimalBlockSetup.rank_one_single_block_core_source
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    {F : Type*} [Field F]
    (h : RankOne.Setup ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) F)
    (hRK : (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer (d.block.map d.H.subtype : Set G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let U₀ := d.U0.map d.H.subtype
    let D := R ⊓ centralizer (d.L0.map d.H.subtype : Set G)
    d.U0 = d.L0.pCoreIn 2 ∧ twoCore d.H = U₀ ⊔ D ∧
      twoCore d.H ∈ Stellmacher.elementaryAbelianMaxSubgroups R := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  obtain ⟨x,hx,hnc⟩ := d.exists_single_block_noncommuting T hST M₀ hSM₀ hM₀T hindex h.short hRK
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hM₀R : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn
  have hR : IsPGroup 2 R := d.S.isPGroup'.map d.H.subtype
  have hH : d.H = K ⊔ R := by
    change d.H = d.block.map d.H.subtype ⊔ (d.S : Subgroup d.H).map d.H.subtype
    rw [← Subgroup.map_sup,d.generated,← MonoidHom.range_eq_map,range_subtype]
  have hc := d.single_block_closures hRK
  have hno := d.no_common_normal_of_index_two T hST M₀ hSM₀ hM₀T hindex
  have hs := h.source_single_block_terminal hR d.H M₀ R le_rfl hSM₀ hM₀R hRK hH hno x hx hindex hnc
  have he := h.source_single_block_terminal_equalities hR d.H M₀ R le_rfl hSM₀ hM₀R hRK hH hno x hx hindex hnc
  have hphi := h.frattini_eq_bot_of_index_two d.H M₀ R hSM₀ hM₀R hRK hH hno hindex x hx hnc
  have hCore := d.single_block_core_centralizer h.short hRK
  have hU : d.U0 = d.L0.pCoreIn 2 := by
    apply map_injective d.H.subtype_injective
    rw [map_pCoreIn_of_injective 2 d.L0 d.H.subtype d.H.subtype_injective,hc.1,hc.2]
    exact hs.1.symm
  refine ⟨hU,?_,?_⟩
  · rw [← hCore,hc.1,hc.2]
    exact hs.2.1
  · rw [← hCore,hc.2]
    change R ⊓ centralizer (RankOne.U K : Set G) ∈ Stellmacher.elementaryAbelianMaxSubgroups R
    rw [he.2.1,← h.core,h.sylow_maximum_family (hM₀R hx) hnc hphi]
    exact Set.mem_insert _ _
end CFSG.Quasithin.Chapter2

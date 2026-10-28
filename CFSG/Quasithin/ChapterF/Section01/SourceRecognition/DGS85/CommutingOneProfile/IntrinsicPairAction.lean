module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.IntrinsicPairQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryCatalogue

/-!
# The elementary source pair action with both catalogues discharged

When the edge radical is Q_alpha Q_beta, the beta-core image is the whole
local alpha Sylow. Each opposite seed is elementary and normal in that image,
so the intrinsic Sylow omega calculation bounds its displacement by Q_alpha,
including the order-144 alpha possibility. The same calculation at the other
neighbor gives [Q_beta,V] <= J for the literal two-seed group and common center.

Conjugation therefore descends to the actual pair actor modulo Q_beta on V/J.
The construction retains quotient coordinates, complementary seed subspaces,
quadratic critical-center action and generation by conjugates of its fixed
space. In the elementary beta branch the established source core-product
identity supplies the only extra premise, so that consumer requires neither
local catalogue nor a supplied action. The unrestricted local exclusions and
full Chapter 11/14 marked assembly remain separate obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(a,b,h), (11.4), pp.168--172, and the corrected fixed-generation
hypothesis of (5.12), pp.113--115.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Reduction Representation.AffineNine
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (Reduction.G₀ L S))
local notation "G₀" => Reduction.G₀ L S

private theorem elementary_displacement_of_core_product (h : HypothesisF11 L S)
    {a b : Vertex F} (hab : (graph F).Adj a b)
    (hprod : (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 = Q F a ⊔ Q F b)
    (E : Subgroup G₀) [IsElementaryAbelian 2 E] (hEQ : E ≤ Q F b)
    (hnE : Q F b ≤ normalizer (E : Set G₀)) : ⁅Q F b,E⁆ ≤ Q F a := by
  let ht := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let := finite_endpoints ht
  let M := graphLocalGroup F a
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 M)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht (reduced_borel_core_sylow h) d hab
  change Sylow 2 M at T
  change (T : Subgroup M).map M.subtype = (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 at hT
  have hQT : Q F b ≤ (T : Subgroup M).map M.subtype := by
    rw [hT,hprod]
    exact le_sup_right
  have hQM : Q F b ≤ M := hQT.trans (map_subtype_le _)
  have hEM : E ≤ M := hEQ.trans hQM
  let C := (Q F b).subgroupOf M
  let A := E.subgroupOf M
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hEM
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  have hcore : (pCore 2 M).map M.subtype = Q F a := localGroup_core_eq F d a
  have hTC : (T : Subgroup M) = pCore 2 M ⊔ C := by
    apply (map_injective (f := M.subtype) M.subtype_injective)
    rw [hT,Subgroup.map_sup,hcore,map_subgroupOf_eq_of_le hQM]
    exact hprod
  have hTq : (T : Subgroup M).map q = C.map q := by
    rw [hTC,Subgroup.map_sup]
    have hk : (pCore 2 M).map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    rw [hk,bot_sup_eq]
  have hnC : C ≤ normalizer (A : Set M) := fun x hx => le_normalizer_comap M.subtype (hnE hx)
  have hAT : A ≤ (T : Subgroup M) := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hQT (hEQ hx)
    exact (Subtype.ext he : y = x) ▸ hy
  let T' := T.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hn : (T' : Subgroup (M ⧸ pCore 2 M)) ≤ normalizer (A.map q : Set (M ⧸ pCore 2 M)) := by
    change (T : Subgroup M).map q ≤ _
    rw [hTq]
    exact (map_mono hnC).trans (le_normalizer_map q)
  have hcent := reduced_normal_elementary_le_sylow_omega h a T' (A.map q) (map_mono hAT) hn
  have hcomm : ⁅(T : Subgroup M),A⁆ ≤ q.ker := by
    rw [←Subgroup.map_eq_bot_iff,map_commutator]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    intro x hx
    exact ((mem_omegaCenterIn_iff _ _).mp (hcent hx)).2.1
  have hh := map_mono (f := M.subtype) hcomm
  rw [map_commutator,map_subgroupOf_eq_of_le hEM,QuotientGroup.ker_mk',hcore] at hh
  exact (commutator_mono hQT le_rfl).trans hh

/-- The full adjacent-core product makes the beta core act trivially on
both seed factors modulo the common center, including an exceptional alpha
quotient. This is the action needed for the literal source representation. -/
theorem reduced_source_pair_core_action_of_core_product (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) (hac : a ≠ c)
    (hprod : (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 = Q F a ⊔ Q F b) :
    ⁅Q F b,pairSpan (Z F a) (Z F c) (Q F b)⁆ ≤ Z F a ⊓ Z F c := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let := source_center_elementary ht a
  let := source_center_elementary ht c
  have hab := source_critical_one_adjacent hc hb
  let E := Z F a ⊓ Q F b
  let C := Z F c ⊓ Q F b
  let D := Q F a ⊓ Q F c
  let V := pairSpan (Z F a) (Z F c) (Q F b)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  have hnE : Q F b ≤ normalizer (E : Set G₀) :=
    (le_inf (source_adjacent_core_normalizes_center ht hab) (Q F b).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hnC : Q F b ≤ normalizer (C : Set G₀) :=
    (le_inf (source_adjacent_core_normalizes_center ht hbc.symm) (Q F b).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨g,hg,hga⟩ := reduced_source_center_pair_moves h hc hb hbc
  have hgb : g • b = b := by
    apply (show Z F a ⊔ Z F c ≤ stabilizer F b from sup_le ?_ ?_) hg
    · exact (((source_Z_Q_U ht a).1.trans (map_subtype_le _)).trans
        (source_Z_Q_U ht a).2).trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)
    · exact (((source_Z_Q_U ht c).1.trans (map_subtype_le _)).trans
        (source_Z_Q_U ht c).2).trans ((ballKernel_one_le_edge _ hbc.symm).trans inf_le_right)
  have hprod' : (stabilizer F c ⊓ stabilizer F b).pCoreIn 2 = Q F c ⊔ Q F b := by
    have hh := congrArg (map (MulAut.conj g).toMonoidHom) hprod
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
      map_inf _ _ _ (MulAut.conj g).injective,Subgroup.map_sup,
      ←stabilizer_translate,←stabilizer_translate,←Q_translate,←Q_translate,hga,hgb] at hh
    exact hh
  have hED : ⁅Q F b,E⁆ ≤ D := le_inf
    ((commutator_mono le_rfl inf_le_left).trans
      ((le_normalizer_iff_commutator_le_right.mp (source_adjacent_core_normalizes_center ht hab)).trans
        ((source_Z_Q_U ht a).1.trans (map_subtype_le _))))
    (elementary_displacement_of_core_product h hbc.symm hprod' E inf_le_right hnE)
  have hCD : ⁅Q F b,C⁆ ≤ D := le_inf
    (elementary_displacement_of_core_product h hab hprod C inf_le_right hnC)
    ((commutator_mono le_rfl inf_le_left).trans
      ((le_normalizer_iff_commutator_le_right.mp (source_adjacent_core_normalizes_center ht hbc.symm)).trans
        ((source_Z_Q_U ht c).1.trans (map_subtype_le _))))
  have hnorm := source_pair_core_normalizers ht hab hbc
  have hVD : ⁅Q F b,V⁆ ≤ D := by
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal (Q F b) E C _ D
      (le_sup_right.trans hnorm.2.1) inf_le_right inf_le_right
      ((commutator_comm E _).trans_le hED) ((commutator_comm C _).trans_le hCD)
  rw [←reduced_source_pair_core_intersection h hc hb hbc hac]
  exact le_inf hVD (le_normalizer_iff_commutator_le_right.mp (le_sup_right.trans hnorm.2.2.1))

/-- In the elementary beta branch the source itself supplies the full core
product, so neither endpoint catalogue nor a displacement premise remains. -/
theorem reduced_elementary_pair_core_action (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) (hac : a ≠ c)
    (helem : ∃ hN : ((Q F b).subgroupOf
        ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) ⧸
        (Q F b).subgroupOf ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2))) :
    ⁅Q F b,pairSpan (Z F a) (Z F c) (Q F b)⁆ ≤ Z F a ⊓ Z F c := by
  exact reduced_source_pair_core_action_of_core_product h hc hb hbc hac
    (reduced_elementary_center_and_core_products h hc hb helem).2


open Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition

/-- The literal beta pair action, its complementary seed spaces, quadratic
critical-center action and fixed-space generation, with local catalogue
premises replaced by the independently proved full adjacent-core identity. -/
theorem reduced_source_pair_section_of_core_product (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b)
    (hb : DGS85.b F = 1) (hbc : (graph F).Adj b c) (hac : a ≠ c)
    (hprod : (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 = Q F a ⊔ Q F b) :
    let H := (Z F a ⊔ Z F c) ⊔ Q F b
    let V := pairSpan (Z F a) (Z F c) (Q F b)
    let J := Z F a ⊓ Z F c
    ∃ hJ : (J.subgroupOf V).Normal, letI := hJ
      ∃ hE : IsElementaryAbelian 2 (V ⧸ J.subgroupOf V), letI := hE
        ∃ hQ : ((Q F b).subgroupOf H).Normal, letI := hQ
          let π := QuotientGroup.mk' ((Q F b).subgroupOf H)
          ∃ σ : Representation (ZMod 2) (H ⧸ (Q F b).subgroupOf H)
              (Additive (V ⧸ J.subgroupOf V)),
            ∃ s : BinaryConjugationSection H V J (σ.comp π),
              (∀ x : V, (s.coordinates x).toAdd =
                Additive.ofMul (QuotientGroup.mk' (J.subgroupOf V) x)) ∧
              IsCompl (s.imageSpace (Z F a ⊓ Q F b))
                (s.imageSpace (Z F c ⊓ Q F b)) ∧
              IsQuadratic σ (((Z F a).subgroupOf H).map π) ∧
              GeneratedByFixedSpace σ (((Z F a).subgroupOf H).map π) := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let := source_center_elementary ht a
  let := source_center_elementary ht c
  let H := (Z F a ⊔ Z F c) ⊔ Q F b
  let V := pairSpan (Z F a) (Z F c) (Q F b)
  let D := Q F a ⊓ Q F c
  let J := Z F a ⊓ Z F c
  let E := Z F a ⊓ Q F b
  let C := Z F c ⊓ Q F b
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  have hab := source_critical_one_adjacent hc hb
  have hDV : D ⊓ V = J := reduced_source_pair_core_intersection h hc hb hbc hac
  have hJV : J ≤ V := hDV.ge.trans inf_le_right
  have hJQ : J ≤ Q F b := hJV.trans (pairSpan_le_core _ _ _)
  have hEF : J = E ⊓ C := le_antisymm
    (le_inf (le_inf inf_le_left hJQ) (le_inf inf_le_right hJQ))
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
  have hnorm := source_pair_core_normalizers ht hab hbc
  have hHJ : H ≤ normalizer (J : Set G₀) := by
    rw [←hDV]
    exact (le_inf hnorm.2.1 hnorm.2.2.1).trans inf_normalizer_le_normalizer_inf
  have hVH : V ≤ H := (pairSpan_le_core _ _ _).trans le_sup_right
  let hJ : (J.subgroupOf V).Normal := normal_subgroupOf_of_le_normalizer (hVH.trans hHJ)
  have hcomm : ⁅E,C⁆ ≤ J :=
    (commutator_mono (show E ≤ V from le_sup_left) (show C ≤ V from le_sup_right)).trans
      (source_pairSpan_commutator_frattini ht hab hbc).2.2.1
  let hE : IsElementaryAbelian 2 (V ⧸ J.subgroupOf V) :=
    pair_quotient_elementary V J E C le_sup_left le_sup_right hJV
      (by exact (sup_eq_left.mpr hJV).symm) hcomm
  have hHb : H ≤ stabilizer F b := by
    apply sup_le (sup_le ?_ ?_) (Q_le_stabilizer _ b)
    · exact (((source_Z_Q_U ht a).1.trans (map_subtype_le _)).trans
        (source_Z_Q_U ht a).2).trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)
    · exact (((source_Z_Q_U ht c).1.trans (map_subtype_le _)).trans
        (source_Z_Q_U ht c).2).trans ((ballKernel_one_le_edge _ hbc.symm).trans inf_le_right)
  let hQ : ((Q F b).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (hHb.trans (stabilizer_normalizes_Q _ b))
  let π := QuotientGroup.mk' ((Q F b).subgroupOf H)
  have hdisp : ⁅Q F b,V⁆ ≤ J :=
    reduced_source_pair_core_action_of_core_product h hc hb hbc hac hprod
  obtain ⟨σ,s,hs⟩ := exists_descended_actor H V J hVH hJV hnorm.2.2.1 hHJ π
    (QuotientGroup.mk'_surjective _) (by
      intro x hx v hv
      exact hdisp (commutator_mem_commutator ((QuotientGroup.eq_one_iff x).mp hx) hv))
  refine ⟨hJ,hE,hQ,σ,s,hs,s.isCompl_imageSpace E C rfl hEF,?_,?_⟩
  · apply isQuadratic_of_triple_commutator_le H V J (Z F a) σ π s
    have hh : ⁅⁅V,Z F a⁆,Z F a⁆ ≤ ⊥ :=
      (commutator_mono (commutator_mono (pairSpan_le_core _ _ _) le_rfl) le_rfl).trans
        (source_adjacent_core_center_quadratic ht hab).le
    have htriple : ⁅⁅V,Z F a⁆,Z F a⁆ ≤ J := hh.trans bot_le
    simpa only [commutator_comm] using htriple
  · obtain ⟨g,hg,hga⟩ := reduced_source_center_pair_moves h hc hb hbc
    let g₀ : H := ⟨g,mem_sup_left hg⟩
    have hgb : g • b = b := hHb g₀.property
    have hconj : C = E.conjBy (g₀ : G₀) := by
      dsimp only [E,C,conjBy,g₀]
      rw [map_inf _ _ _ (MulAut.conj g).injective,←Z_translate,←Q_translate,hga,hgb]
    apply pair_section_generated H V J E C (Z F a) σ π s le_sup_left
      (sup_eq_left.mpr hJV).symm g₀ hconj
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      ((le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative (Z F a))).trans
        (centralizer_le (show E ≤ Z F a from inf_le_left)))).le.trans bot_le

/-- The original elementary beta branch constructs the source pair section
with no local model, alpha marking or action witness among its inputs. -/
theorem reduced_elementary_pair_section (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) (hac : a ≠ c)
    (helem : ∃ hN : ((Q F b).subgroupOf
        ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) ⧸
        (Q F b).subgroupOf ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2))) :
    let H := (Z F a ⊔ Z F c) ⊔ Q F b
    let V := pairSpan (Z F a) (Z F c) (Q F b)
    let J := Z F a ⊓ Z F c
    ∃ hJ : (J.subgroupOf V).Normal, letI := hJ
      ∃ hE : IsElementaryAbelian 2 (V ⧸ J.subgroupOf V), letI := hE
        ∃ hQ : ((Q F b).subgroupOf H).Normal, letI := hQ
          let π := QuotientGroup.mk' ((Q F b).subgroupOf H)
          ∃ σ : Representation (ZMod 2) (H ⧸ (Q F b).subgroupOf H)
              (Additive (V ⧸ J.subgroupOf V)),
            ∃ s : BinaryConjugationSection H V J (σ.comp π),
              (∀ x : V, (s.coordinates x).toAdd =
                Additive.ofMul (QuotientGroup.mk' (J.subgroupOf V) x)) ∧
              IsCompl (s.imageSpace (Z F a ⊓ Q F b))
                (s.imageSpace (Z F c ⊓ Q F b)) ∧
              IsQuadratic σ (((Z F a).subgroupOf H).map π) ∧
              GeneratedByFixedSpace σ (((Z F a).subgroupOf H).map π) := by
  exact reduced_source_pair_section_of_core_product h hc hb hbc hac
    (reduced_elementary_center_and_core_products h hc hb helem).2

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

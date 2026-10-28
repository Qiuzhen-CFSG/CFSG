module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairCoreGeometry
public import Theory.GroupTheory.NormalJoinQuotientProduct
public import Theory.ElementaryAbelian.Join
public import Theory.Representation.BinaryConjugationSection.Descent
public import Theory.Representation.BinaryConjugationSection.QuadraticCorePair

/-!
# The actual two-seed quotient before alpha selection

In L Q_beta / D the two seed images commute and intersect trivially.
Multiplication gives their direct-product isomorphism, so their join is
elementary. Conjugation by the center pair identifies the two seed orders;
the opposite seed order is its exact relative index over Q_alpha. This
proves the square-order formula for V/(D intersect V).

The proved [Q_beta,V] <= D descends conjugation to L Q_beta / Q_beta.
We construct its binary representation on the literal V/(Z_alpha intersect
Z_gamma), retaining the quotient projection. The two seed image spaces
are complementary, the critical center acts quadratically, and conjugate
seed generation proves the corrected fixed-generation hypothesis of (5.12).
No action witness, alpha linear marking, field bound or core-product
identity is assumed. The fixed-point-free argument and (11.3)(h)--(11.5)
remain to be assembled from this section and the actual beta quotient row.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(a,b) and its proof, printed pp.168--171; corrected (5.12).
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The two seed images in the source quotient are elementary direct factors.
The equivalence multiplies the actual images, rather than only identifying types. -/
theorem source_rankOne_pair_image_direct_product {K : Type*} [Group K]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (π : pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) →* K)
    (hker : π.ker = (Q (family P) a ⊓ Q (family P) c).subgroupOf
      (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b))) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let E := ((Z (family P) a ⊓ Q (family P) b).subgroupOf V).map π
    let F := ((Z (family P) c ⊓ Q (family P) b).subgroupOf V).map π
    IsElementaryAbelian 2 π.range ∧ Disjoint E F ∧
      ∃ e : E × F ≃* π.range, ∀ x y, (e (x,y) : K) = (x : K) * (y : K) := by
  let := source_center_elementary h a
  let := source_center_elementary h c
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let E := Z (family P) a ⊓ Q (family P) b
  let F := Z (family P) c ⊓ Q (family P) b
  let E₀ := E.subgroupOf V
  let F₀ := F.subgroupOf V
  have hEV : E ≤ V := le_sup_left
  have hFV : F ≤ V := le_sup_right
  have hab := source_critical_one_adjacent hc hb
  have hQE : Q (family P) b ≤ normalizer (E : Set G) :=
    (le_inf (source_adjacent_core_normalizes_center h hab)
      (Q (family P) b).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hQF : Q (family P) b ≤ normalizer (F : Set G) :=
    (le_inf (source_adjacent_core_normalizes_center h hbc.symm)
      (Q (family P) b).le_normalizer).trans inf_normalizer_le_normalizer_inf
  let : E₀.Normal := normal_subgroupOf_of_le_normalizer ((pairSpan_le_core _ _ _).trans hQE)
  let : F₀.Normal := normal_subgroupOf_of_le_normalizer ((pairSpan_le_core _ _ _).trans hQF)
  have hinter := source_rankOne_pair_core_intersection h hB d hc hb hbc hac Mb
  have hk : π.ker = E₀ ⊓ F₀ := by
    rw [hker]
    ext x
    constructor
    · intro hx
      have hxJ := hinter.le ⟨hx,x.property⟩
      exact ⟨⟨hxJ.1,pairSpan_le_core _ _ _ x.property⟩,
        ⟨hxJ.2,pairSpan_le_core _ _ _ x.property⟩⟩
    · intro hx
      exact ⟨((source_Z_Q_U h a).1.trans (map_subtype_le _)) hx.1.1,
        ((source_Z_Q_U h c).1.trans (map_subtype_le _)) hx.2.1⟩
  have hgen : E₀ ⊔ F₀ = ⊤ := by
    rw [←subgroupOf_sup hEV hFV]
    exact subgroupOf_self V
  have hgenMap : (E₀ ⊔ F₀).map π = π.range := by
    rw [hgen,←MonoidHom.range_eq_map]
  obtain ⟨hdisj,e,he⟩ := normal_join_image_direct_product π E₀ F₀ hk
  have hcomm : E₀.map π ≤ centralizer (F₀.map π : Set K) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr ((commutator_le_inf E₀ F₀).trans hk.ge)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.subgroupOf hEV
  let : IsElementaryAbelian 2 F₀ := IsElementaryAbelian.subgroupOf hFV
  let : IsElementaryAbelian 2 (E₀.map π) := IsElementaryAbelian.map π
  let : IsElementaryAbelian 2 (F₀.map π) := IsElementaryAbelian.map π
  have hel : IsElementaryAbelian 2 π.range := by
    rw [←hgenMap,Subgroup.map_sup]
    exact IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hcomm)
  exact ⟨hel,hdisj,e.trans (MulEquiv.subgroupCongr hgenMap),he⟩

/-- Source (11.3)(a,b) in the literal quotient L Q_beta / D.
Both normality and the elementary direct-product decomposition are constructed. -/
theorem source_rankOne_pair_core_quotient (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
    let D := Q (family P) a ⊓ Q (family P) c
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    ∃ hD : (D.subgroupOf H).Normal, letI := hD
      let π := QuotientGroup.mk' (D.subgroupOf H)
      let E := ((Z (family P) a ⊓ Q (family P) b).subgroupOf H).map π
      let F := ((Z (family P) c ⊓ Q (family P) b).subgroupOf H).map π
      IsElementaryAbelian 2 ((V.subgroupOf H).map π) ∧ Disjoint E F ∧
        ∃ e : E × F ≃* (V.subgroupOf H).map π,
          ∀ x y, (e (x,y) : H ⧸ D.subgroupOf H) = (x : H ⧸ D.subgroupOf H) * (y : H ⧸ D.subgroupOf H) := by
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let D := Q (family P) a ⊓ Q (family P) c
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let hD : (D.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (source_pair_core_normalizers h (source_critical_one_adjacent hc hb) hbc).2.1
  refine ⟨hD,?_⟩
  let π := QuotientGroup.mk' (D.subgroupOf H)
  have hVH : V ≤ H := (pairSpan_le_core _ _ _).trans le_sup_right
  let f : V →* (H ⧸ D.subgroupOf H) := π.comp (inclusion hVH)
  have hker : f.ker = D.subgroupOf V := by
    ext x
    exact QuotientGroup.eq_one_iff ((inclusion hVH) x)
  have hmap (A : Subgroup G) (hAV : A ≤ V) :
      (A.subgroupOf V).map f = (A.subgroupOf H).map π := by
    rw [show f = π.comp (inclusion hVH) from rfl,←map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,hAV hx⟩,hx,Subtype.ext rfl⟩
  have hrange : f.range = (V.subgroupOf H).map π := by
    rw [MonoidHom.range_comp]
    have hi : (inclusion hVH).range = V.subgroupOf H := by
      ext x
      exact ⟨fun ⟨y,hy⟩ => hy ▸ y.property,fun hx => ⟨⟨x,hx⟩,Subtype.ext rfl⟩⟩
    rw [hi]
  have hs := source_rankOne_pair_image_direct_product h hB d hc hb hbc hac Mb f hker
  dsimp only at hs ⊢
  rw [hmap _ le_sup_left,hmap _ le_sup_right,hrange] at hs
  exact hs

/-- The opposite seed has the same order modulo D as its literal alpha-core
image. This is the index equality in (11.3)(a). -/
theorem source_pair_second_image_card {K : Type*} [Group K]
    (h : LocallyRankOneTriple P B) (a b c : Vertex (family P))
    (π : pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) →* K)
    (hker : π.ker = (Q (family P) a ⊓ Q (family P) c).subgroupOf
      (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b))) :
    Nat.card (((Z (family P) c ⊓ Q (family P) b).subgroupOf
      (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b))).map π) =
        (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) := by
  let F := Z (family P) c ⊓ Q (family P) b
  have hFQ : F ≤ Q (family P) c := inf_le_left.trans
    ((source_Z_Q_U h c).1.trans (map_subtype_le _))
  rw [←relIndex_ker,hker,relIndex_subgroupOf (show F ≤ pairSpan
    (Z (family P) a) (Z (family P) c) (Q (family P) b) from le_sup_right)]
  change (Q (family P) a ⊓ Q (family P) c).relIndex F = _
  rw [←inf_relIndex_right,inf_assoc,inf_eq_right.mpr hFQ,inf_relIndex_right]

/-- The source two-seed quotient has the square of the opposite seed index.
No alpha model, core-product identity or field relation is assumed. -/
theorem source_rankOne_pair_image_order {K : Type*} [Group K]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (π : pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) →* K)
    (hker : π.ker = (Q (family P) a ⊓ Q (family P) c).subgroupOf
      (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b))) :
    Nat.card π.range = ((Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b))^2 := by
  let := finite_endpoints h
  let E := Z (family P) a ⊓ Q (family P) b
  let F := Z (family P) c ⊓ Q (family P) b
  let D := Q (family P) a ⊓ Q (family P) c
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨g,hg,hga⟩ := source_rankOne_center_pair_moves h hB d hc hb hbc Mb
  have hgb : g • b = b := by
    change g ∈ stabilizer (family P) b
    apply (show Z (family P) a ⊔ Z (family P) c ≤ stabilizer (family P) b from sup_le ?_ ?_) hg
    · exact (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
        (source_Z_Q_U h a).2).trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)
    · exact (((source_Z_Q_U h c).1.trans (map_subtype_le _)).trans
        (source_Z_Q_U h c).2).trans ((ballKernel_one_le_edge _ hbc.symm).trans inf_le_right)
  have hDm : D.map (MulAut.conj g).toMonoidHom = D :=
    mem_normalizer_iff_map_conj_eq.mp
      (((source_pair_core_normalizers h hab hbc).1.trans
        (Subgroup.centralizer_le_normalizer _)) hg)
  have hEm : E.map (MulAut.conj g).toMonoidHom = F := by
    rw [map_inf _ _ _ (MulAut.conj g).injective,←Z_translate,←Q_translate,hga,hgb]
  have hi : D.relIndex E = D.relIndex F := by
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) D E (MulAut.conj g).injective
    rw [hDm,hEm] at hh
    exact hh.symm
  have hcard : Nat.card ((E.subgroupOf V).map π) = Nat.card ((F.subgroupOf V).map π) := by
    rw [←relIndex_ker,←relIndex_ker,hker,
      relIndex_subgroupOf (show E ≤ V from le_sup_left),
      relIndex_subgroupOf (show F ≤ V from le_sup_right)]
    exact hi
  obtain ⟨_,_,e,_⟩ := source_rankOne_pair_image_direct_product h hB d hc hb hbc hac Mb π hker
  rw [←Nat.card_congr e.toEquiv,Nat.card_prod,hcard,
    source_pair_second_image_card h a b c π hker,pow_two]

/-- The order of the literal elementary pair quotient, independently of its
chosen representation. -/
theorem source_rankOne_pair_quotient_order (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    [((Z (family P) a ⊓ Z (family P) c).subgroupOf
      (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b))).Normal] :
    Nat.card (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⧸
      (Z (family P) a ⊓ Z (family P) c).subgroupOf
        (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b))) =
      ((Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b))^2 := by
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let D := Q (family P) a ⊓ Q (family P) c
  let J := Z (family P) a ⊓ Z (family P) c
  have hDV : D ⊓ V = J := source_rankOne_pair_core_intersection h hB d hc hb hbc hac Mb
  let qV := QuotientGroup.mk' (J.subgroupOf V)
  have hqV : qV.ker = D.subgroupOf V := by
    rw [QuotientGroup.ker_mk']
    ext x
    exact ⟨fun hx => (hDV.ge hx).1,fun hx => hDV.le ⟨hx,x.property⟩⟩
  have ho := source_rankOne_pair_image_order h hB d hc hb hbc hac Mb qV hqV
  rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at ho
  have htopcard : Nat.card (⊤ : Subgroup (V ⧸ J.subgroupOf V)) = Nat.card (V ⧸ J.subgroupOf V) :=
    Nat.card_congr (Subgroup.topEquiv).toEquiv
  rw [htopcard] at ho
  exact ho

open Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition

/-- The actual two-seed quotient, with its descended beta actor, complementary
seed images, quadratic critical action and corrected fixed-generation condition.
The alpha row is still arbitrary in the earlier catalogue. -/
theorem source_rankOne_pair_section (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∃ hJ : (J.subgroupOf V).Normal, letI := hJ
      ∃ hE : IsElementaryAbelian 2 (V ⧸ J.subgroupOf V), letI := hE
        ∃ hQ : ((Q (family P) b).subgroupOf H).Normal, letI := hQ
          let π := QuotientGroup.mk' ((Q (family P) b).subgroupOf H)
          ∃ σ : Representation (ZMod 2) (H ⧸ (Q (family P) b).subgroupOf H)
              (Additive (V ⧸ J.subgroupOf V)),
            ∃ s : BinaryConjugationSection H V J (σ.comp π),
              (∀ x : V, (s.coordinates x).toAdd =
                Additive.ofMul (QuotientGroup.mk' (J.subgroupOf V) x)) ∧
              IsCompl (s.imageSpace (Z (family P) a ⊓ Q (family P) b))
                (s.imageSpace (Z (family P) c ⊓ Q (family P) b)) ∧
              IsQuadratic σ (((Z (family P) a).subgroupOf H).map π) ∧
              GeneratedByFixedSpace σ (((Z (family P) a).subgroupOf H).map π) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let D := Q (family P) a ⊓ Q (family P) c
  let J := Z (family P) a ⊓ Z (family P) c
  let E := Z (family P) a ⊓ Q (family P) b
  let F := Z (family P) c ⊓ Q (family P) b
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  have hab := source_critical_one_adjacent hc hb
  have hDV : D ⊓ V = J := source_rankOne_pair_core_intersection h hB d hc hb hbc hac Mb
  have hJV : J ≤ V := hDV.ge.trans inf_le_right
  have hJQ : J ≤ Q (family P) b := hJV.trans (pairSpan_le_core _ _ _)
  have hEF : J = E ⊓ F := le_antisymm
    (le_inf (le_inf inf_le_left hJQ) (le_inf inf_le_right hJQ))
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
  have hnorm := source_pair_core_normalizers h hab hbc
  have hHJ : H ≤ normalizer (J : Set G) := by
    rw [←hDV]
    exact (le_inf hnorm.2.1 hnorm.2.2.1).trans inf_normalizer_le_normalizer_inf
  have hVH : V ≤ H := (pairSpan_le_core _ _ _).trans le_sup_right
  let hJ : (J.subgroupOf V).Normal := normal_subgroupOf_of_le_normalizer (hVH.trans hHJ)
  have hcomm : ⁅E,F⁆ ≤ J :=
    (commutator_mono (show E ≤ V from le_sup_left) (show F ≤ V from le_sup_right)).trans
      (source_pairSpan_commutator_frattini h hab hbc).2.2.1
  let hE : IsElementaryAbelian 2 (V ⧸ J.subgroupOf V) :=
    pair_quotient_elementary V J E F le_sup_left le_sup_right hJV
      (by exact (sup_eq_left.mpr hJV).symm) hcomm
  have hHb : H ≤ stabilizer (family P) b := by
    apply sup_le (sup_le ?_ ?_) (Q_le_stabilizer _ b)
    · exact (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
        (source_Z_Q_U h a).2).trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)
    · exact (((source_Z_Q_U h c).1.trans (map_subtype_le _)).trans
        (source_Z_Q_U h c).2).trans ((ballKernel_one_le_edge _ hbc.symm).trans inf_le_right)
  let hQ : ((Q (family P) b).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (hHb.trans (stabilizer_normalizes_Q _ b))
  let π := QuotientGroup.mk' ((Q (family P) b).subgroupOf H)
  have hdisp : ⁅Q (family P) b,V⁆ ≤ J := by
    rw [←hDV]
    exact le_inf (source_rankOne_pair_core_action h hB d hc hb hbc Ma Mb)
      (le_normalizer_iff_commutator_le_right.mp (le_sup_right.trans hnorm.2.2.1))
  obtain ⟨σ,s,hs⟩ := exists_descended_actor H V J hVH hJV hnorm.2.2.1 hHJ π
    (QuotientGroup.mk'_surjective _) (by
      intro x hx v hv
      exact hdisp (commutator_mem_commutator ((QuotientGroup.eq_one_iff x).mp hx) hv))
  refine ⟨hJ,hE,hQ,σ,s,hs,s.isCompl_imageSpace E F rfl hEF,?_,?_⟩
  · apply isQuadratic_of_triple_commutator_le H V J (Z (family P) a) σ π s
    have hh : ⁅⁅V,Z (family P) a⁆,Z (family P) a⁆ ≤ ⊥ :=
      (commutator_mono (commutator_mono (pairSpan_le_core _ _ _) le_rfl) le_rfl).trans
        (source_adjacent_core_center_quadratic h hab).le
    have htriple : ⁅⁅V,Z (family P) a⁆,Z (family P) a⁆ ≤ J := hh.trans bot_le
    simpa only [commutator_comm] using htriple
  · obtain ⟨g,hg,hga⟩ := source_rankOne_center_pair_moves h hB d hc hb hbc Mb
    let g₀ : H := ⟨g,mem_sup_left hg⟩
    have hgb : g • b = b := hHb g₀.property
    have hconj : F = E.conjBy (g₀ : G) := by
      dsimp only [E,F,conjBy,g₀]
      rw [map_inf _ _ _ (MulAut.conj g).injective,←Z_translate,←Q_translate,hga,hgb]
    apply pair_section_generated H V J E F (Z (family P) a) σ π s le_sup_left
      (sup_eq_left.mpr hJV).symm g₀ hconj
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      ((le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative (Z (family P) a))).trans
        (centralizer_le (show E ≤ Z (family P) a from inf_le_left)))).le.trans bot_le


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

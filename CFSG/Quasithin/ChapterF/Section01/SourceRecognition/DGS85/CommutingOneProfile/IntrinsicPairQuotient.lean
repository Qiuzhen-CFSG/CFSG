module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.IntrinsicCenterIntersection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairCoreQuotient

/-!
# The literal two-seed quotient without local catalogue premises

For V = (Z_alpha intersect Q_beta)(Z_gamma intersect Q_beta) and
J = Z_alpha intersect Z_gamma, intrinsic center separation gives J <= Q_beta.
The mixed-center identities identify V intersect Q_alpha intersect Q_gamma
with J. The two normal elementary seeds then give an explicit multiplication
isomorphism from their quotient images onto V/J. Their center-pair conjugator
identifies their orders, yielding the source square-order formula.

The final applications transport the intersection and the elementary quotient
to the original completion. The quotient marking commutes with the actual
inclusion and both quotient maps. No endpoint catalogue, full core product or
representation witness is an input. The descended action is constructed in
IntrinsicPairAction when the full adjacent-core product is available.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(a,b), printed pp.168--169.
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

/-- Source (11.3)(a) with both catalogue premises removed. -/
theorem reduced_source_pair_core_intersection (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) (hac : a ≠ c) :
    (Q F a ⊓ Q F c) ⊓ pairSpan (Z F a) (Z F c) (Q F b) = Z F a ⊓ Z F c := by
  let ht := reduced_triple h
  have hab := source_critical_one_adjacent hc hb
  have hJQ := reduced_source_center_intersection_le_beta h hc hb hbc hac
  have hm := reduced_source_mixed_center_intersections h hc hb hbc
  have hn : (Z F c ⊓ Q F b : Subgroup G₀) ≤
      normalizer ((Z F a ⊓ Q F b : Subgroup G₀) : Set G₀) :=
    inf_le_right.trans ((le_inf (source_adjacent_core_normalizes_center ht hab)
      (Q F b).le_normalizer).trans inf_normalizer_le_normalizer_inf)
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ ((Z F a ⊓ Q F b : Subgroup G₀) : Set G₀) *
        ((Z F c ⊓ Q F b : Subgroup G₀) : Set G₀) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ hn]
      exact hx.2
    obtain ⟨e,he,f,hf,rfl⟩ := hx'
    have hfQa : f ∈ Q F a := by
      have hh := (Q F a).mul_mem
        ((Q F a).inv_mem (((source_Z_Q_U ht a).1.trans (map_subtype_le _)) he.1)) hx.1.1
      simpa only [inv_mul_cancel_left] using hh
    have hfJ := hm.2.le ⟨hfQa,hf.1⟩
    have heQc : e ∈ Q F c := by
      have hh := (Q F c).mul_mem hx.1.2
        ((Q F c).inv_mem (((source_Z_Q_U ht c).1.trans (map_subtype_le _)) hf.1))
      simpa only [mul_inv_cancel_right] using hh
    exact (Z F a ⊓ Z F c).mul_mem (hm.1.le ⟨he.1,heQc⟩) hfJ
  · exact le_inf (inf_le_inf ((source_Z_Q_U ht a).1.trans (map_subtype_le _))
      ((source_Z_Q_U ht c).1.trans (map_subtype_le _)))
      ((le_inf inf_le_left hJQ).trans le_sup_left)

/-- The source quotient of the actual two-seed group is elementary, with
multiplication giving its direct factors. Its order is the square of the
literal opposite-seed index. No local catalogue or representation is supplied. -/
theorem reduced_source_pair_quotient (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) (hac : a ≠ c) :
    let V := pairSpan (Z F a) (Z F c) (Q F b)
    let J := Z F a ⊓ Z F c
    ∃ hJ : (J.subgroupOf V).Normal, letI := hJ
      let π := QuotientGroup.mk' (J.subgroupOf V)
      let E := ((Z F a ⊓ Q F b).subgroupOf V).map π
      let C := ((Z F c ⊓ Q F b).subgroupOf V).map π
      IsElementaryAbelian 2 (V ⧸ J.subgroupOf V) ∧ Disjoint E C ∧
        (∃ e : E × C ≃* (V ⧸ J.subgroupOf V),
          ∀ x y, e (x,y) = (x : V ⧸ J.subgroupOf V) * (y : V ⧸ J.subgroupOf V)) ∧
        Nat.card (V ⧸ J.subgroupOf V) = ((Q F a).relIndex (Z F c ⊓ Q F b))^2 := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let := source_center_elementary ht a
  let := source_center_elementary ht c
  have hab := source_critical_one_adjacent hc hb
  let V := pairSpan (Z F a) (Z F c) (Q F b)
  let J := Z F a ⊓ Z F c
  let E := Z F a ⊓ Q F b
  let C := Z F c ⊓ Q F b
  have hJV : J ≤ V := (reduced_source_pair_core_intersection h hc hb hbc hac).ge.trans inf_le_right
  have hJQ : J ≤ Q F b := reduced_source_center_intersection_le_beta h hc hb hbc hac
  have hJE : J = E ⊓ C := le_antisymm
    (le_inf (le_inf inf_le_left hJQ) (le_inf inf_le_right hJQ))
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
  have hnE : Q F b ≤ normalizer (E : Set G₀) :=
    (le_inf (source_adjacent_core_normalizes_center ht hab) (Q F b).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hnC : Q F b ≤ normalizer (C : Set G₀) :=
    (le_inf (source_adjacent_core_normalizes_center ht hbc.symm) (Q F b).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  let E₀ := E.subgroupOf V
  let C₀ := C.subgroupOf V
  let : E₀.Normal := normal_subgroupOf_of_le_normalizer ((pairSpan_le_core _ _ _).trans hnE)
  let : C₀.Normal := normal_subgroupOf_of_le_normalizer ((pairSpan_le_core _ _ _).trans hnC)
  let hJ : (J.subgroupOf V).Normal := normal_subgroupOf_of_le_normalizer (by
    rw [hJE]
    exact (pairSpan_le_core _ _ _).trans ((le_inf hnE hnC).trans inf_normalizer_le_normalizer_inf))
  refine ⟨hJ,?_⟩
  let π := QuotientGroup.mk' (J.subgroupOf V)
  have hk : π.ker = E₀ ⊓ C₀ := by
    rw [QuotientGroup.ker_mk',hJE]
    rfl
  have hgen : E₀ ⊔ C₀ = ⊤ := by
    rw [←subgroupOf_sup (show E ≤ V from le_sup_left) (show C ≤ V from le_sup_right)]
    exact subgroupOf_self V
  have hr : (E₀ ⊔ C₀).map π = ⊤ := by
    rw [hgen,←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  obtain ⟨hdisj,e,he⟩ := normal_join_image_direct_product π E₀ C₀ hk
  let e' := e.trans ((MulEquiv.subgroupCongr hr).trans Subgroup.topEquiv)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.subgroupOf (show E ≤ V from le_sup_left)
  let : IsElementaryAbelian 2 C₀ := IsElementaryAbelian.subgroupOf (show C ≤ V from le_sup_right)
  let : IsElementaryAbelian 2 (E₀.map π) := IsElementaryAbelian.map π
  let : IsElementaryAbelian 2 (C₀.map π) := IsElementaryAbelian.map π
  let : IsElementaryAbelian 2 ((E₀.map π) × (C₀.map π)) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
      Prod.ext (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x.1.val x.1.property))
        (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x.2.val x.2.property)) }
  have hcard : Nat.card (E₀.map π) = Nat.card (C₀.map π) := by
    rw [←relIndex_ker,←relIndex_ker,QuotientGroup.ker_mk',
      relIndex_subgroupOf (show E ≤ V from le_sup_left),
      relIndex_subgroupOf (show C ≤ V from le_sup_right)]
    obtain ⟨g,hg,hga⟩ := reduced_source_center_pair_moves h hc hb hbc
    have hgb : g • b = b := by
      apply (show Z F a ⊔ Z F c ≤ stabilizer F b from sup_le ?_ ?_) hg
      · exact (((source_Z_Q_U ht a).1.trans (map_subtype_le _)).trans
          (source_Z_Q_U ht a).2).trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)
      · exact (((source_Z_Q_U ht c).1.trans (map_subtype_le _)).trans
          (source_Z_Q_U ht c).2).trans ((ballKernel_one_le_edge _ hbc.symm).trans inf_le_right)
    have hJm : J.map (MulAut.conj g).toMonoidHom = J := by
      have hcentral : Z F a ⊔ Z F c ≤ centralizer (J : Set G₀) := by
        apply sup_le
        · exact (le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative (Z F a))).trans
            (centralizer_le inf_le_left)
        · exact (le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative (Z F c))).trans
            (centralizer_le inf_le_right)
      exact mem_normalizer_iff_map_conj_eq.mp ((hcentral.trans (Subgroup.centralizer_le_normalizer _)) hg)
    have hEm : E.map (MulAut.conj g).toMonoidHom = C := by
      rw [map_inf _ _ _ (MulAut.conj g).injective,←Z_translate,←Q_translate,hga,hgb]
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) J E (MulAut.conj g).injective
    rw [hJm,hEm] at hh
    exact hh.symm
  have hindex : Nat.card (C₀.map π) = (Q F a).relIndex C := by
    apply source_pair_second_image_card ht a b c π
    rw [QuotientGroup.ker_mk']
    ext x
    have hh := reduced_source_pair_core_intersection h hc hb hbc hac
    exact ⟨fun hx => (hh.ge hx).1,fun hx => hh.le ⟨hx,x.property⟩⟩
  refine ⟨IsElementaryAbelian.of_surjective e'.toMonoidHom e'.surjective,hdisj,⟨e',he⟩,?_⟩
  rw [←Nat.card_congr e'.toEquiv,Nat.card_prod,hcard,hindex,pow_two]


/-- The original-completion intersection identity uses the same inclusion
on both cores, both centers and the corrected two-seed group. -/
theorem original_reduced_source_pair_core_intersection (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) (hac : a ≠ c) :
    ((Q F a).map (G₀).subtype ⊓ (Q F c).map (G₀).subtype) ⊓
      pairSpan ((Z F a).map (G₀).subtype) ((Z F c).map (G₀).subtype)
        ((Q F b).map (G₀).subtype) =
      (Z F a).map (G₀).subtype ⊓ (Z F c).map (G₀).subtype := by
  have hh := congrArg (map (G₀).subtype) (reduced_source_pair_core_intersection h hc hb hbc hac)
  simpa only [pairSpan,Subgroup.map_sup,map_inf _ _ _ (G₀).subtype_injective] using hh

/-- The actual original quotient is elementary of the source square order;
its marking commutes with the original inclusion and both quotient maps. -/
theorem original_reduced_source_pair_quotient (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) (hac : a ≠ c) :
    let V := pairSpan (Z F a) (Z F c) (Q F b)
    let J := Z F a ⊓ Z F c
    let V' := V.map (G₀).subtype
    let J' := (Z F a).map (G₀).subtype ⊓ (Z F c).map (G₀).subtype
    ∃ hJ : (J.subgroupOf V).Normal, letI := hJ
      ∃ hJ' : (J'.subgroupOf V').Normal, letI := hJ'
        IsElementaryAbelian 2 (V' ⧸ J'.subgroupOf V') ∧
        (∃ e : (V ⧸ J.subgroupOf V) ≃* (V' ⧸ J'.subgroupOf V'),
          ∀ x : V, e (QuotientGroup.mk' (J.subgroupOf V) x) =
            QuotientGroup.mk' (J'.subgroupOf V')
              (V.equivMapOfInjective (G₀).subtype (G₀).subtype_injective x)) ∧
        Nat.card (V' ⧸ J'.subgroupOf V') =
          (((Q F a).map (G₀).subtype).relIndex
            ((Z F c).map (G₀).subtype ⊓ (Q F b).map (G₀).subtype))^2 := by
  let V := pairSpan (Z F a) (Z F c) (Q F b)
  let J := Z F a ⊓ Z F c
  let V' := V.map (G₀).subtype
  let J' := (Z F a).map (G₀).subtype ⊓ (Z F c).map (G₀).subtype
  have hJV : J ≤ V := (reduced_source_pair_core_intersection h hc hb hbc hac).ge.trans inf_le_right
  obtain ⟨hJ,hE,_hd,_e,hcard⟩ := reduced_source_pair_quotient h hc hb hbc hac
  let := hJ
  let := hE
  let eV := V.equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  have hmap : (J.subgroupOf V).map eV.toMonoidHom = J'.subgroupOf V' := by
    have hJmap : J.map (G₀).subtype = J' := map_inf _ _ _ (G₀).subtype_injective
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hJmap ▸ mem_map_of_mem (G₀).subtype hy
    · intro hx
      obtain ⟨y,hy,he⟩ := (show (x : G) ∈ J.map (G₀).subtype from hJmap.symm ▸ hx)
      exact ⟨⟨y,hJV hy⟩,hy,Subtype.ext he⟩
  let hJ' : (J'.subgroupOf V').Normal := hmap ▸ hJ.map eV.toMonoidHom eV.surjective
  let eq := QuotientGroup.congr _ _ eV hmap
  refine ⟨hJ,hJ',IsElementaryAbelian.of_surjective eq.toMonoidHom eq.surjective,⟨eq,?_⟩,?_⟩
  · intro x
    rfl
  · have hi : (((Q F a).map (G₀).subtype).relIndex
        ((Z F c).map (G₀).subtype ⊓ (Q F b).map (G₀).subtype)) =
          (Q F a).relIndex (Z F c ⊓ Q F b) := by
      rw [←map_inf _ _ _ (G₀).subtype_injective,
        relIndex_map_map_of_injective _ _ (G₀).subtype_injective]
    rw [hi]
    exact (Nat.card_congr eq.symm.toEquiv).trans hcard

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

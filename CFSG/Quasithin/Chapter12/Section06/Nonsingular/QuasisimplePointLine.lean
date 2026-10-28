module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleOriginalAction

/-!
# The original point line in an escaping nonsingular component

Normalizer uniqueness excludes every nonidentity global L-fixed vector
from the centralizer of an escaping K_v. Projection to the original
orthogonal quotient therefore embeds C_V(K_v) in the one-dimensional
L_v-fixed space. Since v already centralizes K_v, C_V(K_v) is exactly
its line, without a quasisimplicity assumption.

For a quasisimple K_v the checked HS/Ru/J4 fixed-line results now identify
C_{V_v}(L_v) with the original point line. The original action has order
|V|/2.
The global fixed-space application is in QuasisimpleGlobalFixed.

Source: Aschbacher--Smith, proof of 12.6.12, printed pp.825--826;
normalizer uniqueness is the earlier 12.2 source theorem. All original
subgroups, actions and central projections are retained.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- An escaping component has trivial centralizer on the original global fixed space. -/
theorem SourceHypothesis.nonsingular_fixed_component_centralizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ Kv (v : G) ≤ M L) :
    ZV L V ⊓ centralizer (Kv (v : G) : Set G) = ⊥ := by
  apply bot_unique
  rintro x ⟨hx,hc⟩
  change x = 1
  by_contra hne
  have hXZ : zpowers x ≤ ZV L V := zpowers_le.mpr hx
  have hXne : zpowers x ≠ ⊥ := fun h => hne (by
    have hh := mem_zpowers x
    rwa [h,mem_bot] at hh)
  have hn : normalizer (zpowers x : Set G) ≤ M L :=
    H.chosen.normal_subgroup_normalizer_le H.source.toHypothesis1221
      (hXZ.trans (inf_le_left.trans (H.chosen.le_component.trans le_sup_left))) hXne
      (((D.join_centralizes_fixed H.chosen hTV).trans (centralizer_le hXZ)).trans
        (Subgroup.centralizer_le_normalizer _))
  exact hnot (((le_centralizer_iff.mp (zpowers_le.mpr hc)).trans
    (Subgroup.centralizer_le_normalizer _)).trans hn)

/-- The original component centralizer in V is exactly the chosen point line. -/
theorem SourceHypothesis.nonsingular_original_component_centralizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ Kv (v : G) ≤ M L) :
    V ⊓ centralizer (Kv (v : G) : Set G) = zpowers (v : G) := by
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  let C := (centralizer (Kv (v : G) : Set G)).subgroupOf V
  let ρ := alternatingNaturalRepresentation (Fin 8)
  let F := fixedSpace ρ (pointFixer i j)
  let f := D.coordinates.toLinearMap.comp (fixedSeed L V H.chosen.normalizes).toSubmodule.mkQ
  have hLC : Lv L (v : G) ≤ Kv (v : G) := Lv_le_Kv_of_A6 L _
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  have hmem (x : C) : f (Additive.ofMul x.val) ∈ F := by
    intro a
    obtain ⟨l,rfl⟩ := D.localPairMap_surjective v i j hij hp a
    have he := D.equivariant (inclusion (Lv_le_L L (v : G)) l)
      (Submodule.Quotient.mk (Additive.ofMul x.val))
    have hx : seedRepresentation L V H.chosen.normalizes
        (inclusion (Lv_le_L L (v : G)) l) (Additive.ofMul x.val) = Additive.ofMul x.val := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (l : G) * (x.val : G) * (l : G)⁻¹ = x.val
      have hcx : (l : G) * (x.val : G) = (x.val : G) * (l : G) :=
        mem_centralizer_iff.mp x.property l (hLC l.property)
      rw [hcx,mul_inv_cancel_right]
    change D.coordinates (Submodule.Quotient.mk (seedRepresentation L V H.chosen.normalizes
      (inclusion (Lv_le_L L (v : G)) l) (Additive.ofMul x.val))) = _ at he
    rw [hx] at he
    exact he.symm
  let g : C → F := fun x => ⟨f (Additive.ofMul x.val),hmem x⟩
  have hg : Function.Injective g := by
    intro x y he
    have hq := D.coordinates.injective (congrArg Subtype.val he)
    have hz := (mem_fixedSeed_iff L V H.chosen.normalizes
      (Additive.ofMul x.val - Additive.ofMul y.val)).mp ((Submodule.Quotient.eq _).mp hq)
    have hc : (x.val : G) / (y.val : G) ∈ centralizer (Kv (v : G) : Set G) :=
      (centralizer _).div_mem x.property y.property
    have hh : (x.val : G) / (y.val : G) ∈
        ZV L V ⊓ centralizer (Kv (v : G) : Set G) := ⟨hz,hc⟩
    rw [H.nonsingular_fixed_component_centralizer D v hTV hnot,mem_bot,div_eq_one] at hh
    exact Subtype.ext (Subtype.ext hh)
  have hF : Nat.card F = 2 := by
    have hd := pointFixer_fixedCodim i j hij
    have hs := Submodule.finrank_quotient_add_finrank F
    have hn := finrank_natural_even (Fin 8) (by decide)
    have hdim : Module.finrank (ZMod 2) F = 1 := by
      change Module.finrank (ZMod 2) (natural (Fin 8) ⧸ F) = 5 at hd
      change Module.finrank (ZMod 2) (natural (Fin 8)) = 6 at hn
      omega
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim,pow_one]
  have hc : Nat.card C ≤ 2 := (Nat.card_le_card_of_injective g hg).trans_eq hF
  have hle : zpowers (v : G) ≤ V ⊓ centralizer (Kv (v : G) : Set G) := by
    apply zpowers_le.mpr
    exact ⟨v.property,fun x hx => mem_centralizer_singleton_iff.mp (Kv_le_Gv (v : G) hx)⟩
  apply (eq_of_le_of_card_ge hle ?_).symm
  have hm : C.map V.subtype = V ⊓ centralizer (Kv (v : G) : Set G) := by
    dsimp only [C]
    rw [subgroupOf,map_comap_eq,range_subtype]
  rw [←hm,card_map_of_injective V.subtype_injective,Nat.card_zpowers,
    orderOf_eq_prime (p := 2) (elemPow_eq_one_of_isElementaryAbelian _ v.property)
      (fun h => nonsingular_ne_one D hv (Subtype.ext h))]
  exact hc

/-- The original local fixed line is the point itself in every escaping quasisimple row. -/
theorem SourceHypothesis.nonsingular_quasisimple_point_line
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hnot : ¬ Kv (v : G) ≤ M L) :
    ZV (Lv L (v : G)) (Vv L V (v : G)) = zpowers (v : G) ∧
      (v : G) ∈ Vv L V (v : G) := by
  let C := Kv (v : G)
  let Z := ZV (Lv L (v : G)) (Vv L V (v : G))
  have hZC : Z.subgroupOf C ≤ center C := by
    obtain ⟨name,hn,he⟩ := H.nonsingular_quasisimple_models_after_held D v hv hK
    rcases hn with rfl | rfl | rfl
    · exact (H.nonsingular_hs_fixed_line_eq_center D v hv hK he).le
    · exact (H.nonsingular_ru_fixed_line_eq_center D v hv hK he).le
    · exact (H.nonsingular_jankoFour_moved_image_card D v hv hK hTV hi
        (Classical.choice he)).1
  have hZK : Z ≤ C := inf_le_left.trans (H.nonsingular_component_rank D v hv).1
  have hZV : Z ≤ V := inf_le_left.trans (Vv_le_V H.chosen.normalizes _)
  have hZ : Z ≤ V ⊓ centralizer (C : Set G) := by
    refine le_inf hZV ?_
    intro x hx c hc
    exact congrArg Subtype.val (mem_center_iff.mp
      (hZC (show (⟨x,hZK hx⟩ : C) ∈ Z.subgroupOf C from hx)) ⟨c,hc⟩)
  rw [H.nonsingular_original_component_centralizer D v hv hTV hnot] at hZ
  have heq : Z = zpowers (v : G) := eq_of_le_of_card_ge hZ (by
    rw [D.nonsingular_moved_fixed_card H.chosen v hv,Nat.card_zpowers,
      orderOf_eq_prime (p := 2) (elemPow_eq_one_of_isElementaryAbelian _ v.property)
        (fun h => nonsingular_ne_one D hv (Subtype.ext h))])
  exact ⟨heq,(show Z ≤ Vv L V (v : G) from inf_le_left) (heq.symm ▸ mem_zpowers (v : G))⟩

/-- Every original model action has kernel the point line, including when C_V(L) is nontrivial. -/
theorem SourceHypothesis.nonsingular_original_action_card
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ Kv (v : G) ≤ M L)
    {F : Type*} [Group F] (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* F) :
    Nat.card V = 2 * Nat.card
      ((V.subgroupOf (Gv (v : G))).map (nonsingularModelAction (v : G) e)) := by
  let C := (centralizer (Kv (v : G) : Set G)).subgroupOf V
  have hm : C.map V.subtype = zpowers (v : G) := by
    dsimp only [C]
    rw [subgroupOf,map_comap_eq,range_subtype]
    exact H.nonsingular_original_component_centralizer D v hv hTV hnot
  have hc : Nat.card C = 2 := by
    rw [←card_map_of_injective V.subtype_injective,hm,Nat.card_zpowers]
    exact orderOf_eq_prime (p := 2) (elemPow_eq_one_of_isElementaryAbelian _ v.property)
      (fun h => nonsingular_ne_one D hv (Subtype.ext h))
  have hh := C.card_mul_index
  rw [hc] at hh
  have ha := (H.nonsingular_original_model_action D v hv hK e).2.1
  exact hh.symm.trans (congrArg (fun n => 2*n) ha.symm)

end CFSG.Quasithin.Chapter12.Section06

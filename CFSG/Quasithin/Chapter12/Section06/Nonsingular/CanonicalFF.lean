module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalLayers
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.PreferredBlock

/-!
# The canonical FF witness at the original preferred point

In the original augmentation cover, the preferred point controls the
centralizer of its literal moved five-space. If a complementary weight-two
point has an escaping centralizer, preference makes the original point
weight two. That point and the complementary six-letter constant vector
sum to the nonzero original global fixed vector, whose centralizer is in M
by uniqueness. Otherwise the complementary point already gives the bound.

The canonical elementary U centralizes its contained V_v. The bound places
U inside the original T_v, so local Thompson generation constructs an FF
witness for the literal action of (K_v S)/C_(K_v S)(U). No equality R=R_v
or full model-Sylow containment is assumed. PreferredCanonicalFF discharges
these premises and applies the existing A7 module recognition.

Source: Aschbacher--Smith, the preferred choice following 12.6.10 and
12.6.15, printed pp.825--826, using B.2.4--5, combined manuscript
of 1 March 2004. The source application here retains nontrivial C_V(L).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem marked_local_core_le
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (i j : Fin 8) (hij : i ≠ j)
    (hp : coreToNatural (Fin 8) (pair i j) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) (w : core (Fin 6)) :
    ((E.symm (extendSix i j hij w)).toMul : G) ∈ Vv L V (v : G) := by
  let F := E.symm.toLinearMap
  let W : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 ((Vv L V (v : G)).subgroupOf V).toAddSubgroup
  let ρ := (alternatingCoreRepresentation (Fin 8)).comp (pointFixer i j).subtype
  have hm : Coinvariants.ker ρ ≤ W.comap F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,x⟩,rfl⟩
    obtain ⟨l,rfl⟩ := D.localPairMap_surjective v i j hij hp a
    have he : E.symm (alternatingCoreRepresentation (Fin 8)
        (D.actorMap (inclusion (Lv_le_L L (v : G)) l)) x) =
        seedRepresentation L V H.chosen.normalizes (inclusion (Lv_le_L L (v : G)) l)
          (E.symm x) := by
      apply E.injective
      rw [E.apply_symm_apply,hE,E.apply_symm_apply]
    change (E.symm (alternatingCoreRepresentation (Fin 8)
      (D.actorMap (inclusion (Lv_le_L L (v : G)) l)) x - x)).toMul.val ∈ Vv L V (v : G)
    rw [map_sub,he]
    change (l : G) * ((E.symm x).toMul : G) * (l : G)⁻¹ /
      ((E.symm x).toMul : G) ∈ Vv L V (v : G)
    rw [div_eq_mul_inv]
    change ⁅(l : G),((E.symm x).toMul : G)⁆ ∈ Vv L V (v : G)
    rw [Vv,commutator_comm]
    exact commutator_mem_commutator l.property (E.symm x).toMul.property
  exact hm ((pointFixer_moved_core i j hij).ge ⟨w,rfl⟩)

/-- At the source-preferred point in the original augmentation cover,
the centralizer of the literal local moved module is controlled by M. -/
theorem SourceHypothesis.preferred_moved_centralizer_le
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (hproj : ∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w))
    (v : V) (hv : D.Nonsingular v)
    (hpref : ∀ u : V, wordWeight (E (Additive.ofMul u)).val = 2 →
      ¬ Gv (u : G) ≤ M L → wordWeight (E (Additive.ofMul v)).val = 2) :
    Gv (v : G) ⊓ centralizer (Vv L V (v : G) : Set G) ≤ M L := by
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  let a := complementLetters i j hij (0 : Fin 6)
  let b := complementLetters i j hij (1 : Fin 6)
  have hab : a ≠ b := fun h => (by decide : (0 : Fin 6) ≠ 1)
    ((complementLetters i j hij).injective h)
  let u : V := (E.symm (pair a b)).toMul
  have huW : (u : G) ∈ Vv L V (v : G) := by
    change ((E.symm (pair (complementLetters i j hij 0)
      (complementLetters i j hij 1))).toMul : G) ∈ _
    rw [←extendSix_pair]
    exact marked_local_core_le H D E hE v i j hij hp (sixPair 0 1)
  by_cases huM : Gv (u : G) ≤ M L
  · exact (inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr huW))).trans huM
  have hw : wordWeight (E (Additive.ofMul v)).val = 2 := hpref u
    (by change wordWeight (E (E.symm (pair a b))).val = 2
        rw [E.apply_symm_apply]; exact EightCoreLine.pair_weight a b hab) huM
  have hvE : E (Additive.ofMul v) = pair i j := by
    apply EightCoreLine.weight_two_projection_injective _ _ hw (EightCoreLine.pair_weight i j hij)
    exact (hproj _).trans hp.symm
  let z : core (Fin 8) := ⟨allOne (Fin 8),by change (∑ _ : Fin 8, (1 : ZMod 2)) = 0; decide⟩
  have hzrange : z - pair i j ∈ (extendSix i j hij).range := by
    rw [range_extendSix]
    constructor <;> simp [z,pair,hij,hij.symm,allOne]
  obtain ⟨w,hwz⟩ := hzrange
  let zV : V := (E.symm z).toMul
  have hzV : (zV : G) ∈ ZV L V := by
    apply (mem_fixedSeed_iff L V H.chosen.normalizes (E.symm z)).mp
    intro l
    apply E.injective
    rw [hE,E.apply_symm_apply]
    apply Subtype.ext
    exact permute_allOne (Fin 8) (D.actorMap l).val
  have hz1 : (zV : G) ≠ 1 := by
    intro he
    have hh : E.symm z = 0 := Additive.toMul.injective (Subtype.ext he)
    have hh' : z = 0 := E.symm.injective (hh.trans E.symm.map_zero.symm)
    have hc := congrArg (fun x : core (Fin 8) => x.val 0) hh'
    exact one_ne_zero hc
  have hn : normalizer (zpowers (zV : G) : Set G) ≤ M L :=
    H.chosen.normal_subgroup_normalizer_le H.source.toHypothesis1221
      ((zpowers_le.mpr hzV).trans (inf_le_left.trans (H.chosen.le_component.trans le_sup_left)))
      (fun h => hz1 (mem_bot.mp (h ▸ mem_zpowers (zV : G))))
      (((D.join_centralizes_fixed H.chosen hTV).trans
        (centralizer_le (zpowers_le.mpr hzV))).trans (Subgroup.centralizer_le_normalizer _))
  intro g hg
  have hgw : g ∈ centralizer ({((E.symm (extendSix i j hij w)).toMul : G)} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr
      (marked_local_core_le H D E hE v i j hij hp w)) hg.2
  have he : (zV : G) = ((E.symm (extendSix i j hij w)).toMul : G) * (v : G) := by
    have hh : z = extendSix i j hij w + E (Additive.ofMul v) := by rw [hwz,hvE]; abel
    have hh' := congrArg (fun x : core (Fin 8) => ((E.symm x).toMul : G)) hh
    simpa only [map_add,E.symm_apply_apply,toMul_add,toMul_ofMul,Subgroup.coe_mul] using hh'
  have hgz : g ∈ centralizer ({(zV : G)} : Set G) := by
    rw [mem_centralizer_singleton_iff,he]
    exact (show Commute g _ from mem_centralizer_singleton_iff.mp hgw).mul_right
      (show Commute g (v : G) from mem_centralizer_singleton_iff.mp hg.1)
  apply hn
  rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
  exact congrArg zpowers (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hgz))

/-- The original canonical action is FF once the preferred-point centralizer
bound is available. U is placed inside the original T_v, not a model Sylow. -/
theorem SourceHypothesis.nonsingular_canonical_ff_of_moved_control
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hctrl : Gv (v : G) ⊓ centralizer (Vv L V (v : G) : Set G) ≤ M L)
    (hgen : Lv L (v : G) = ⁅Lv L (v : G),elementaryAbelianMaxJ (Tv T (v : G))⁆)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔
        (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
          (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hlocal : ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype),Lv L (v : G)⁆ = Vv L V (v : G)) :
    let J := Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    let E := reducedTwoSubgroup J
    letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
    U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) ≤ Tv T (v : G) ∧
      IsFFModule (ChapterB.InternalThompsonAction.action E) := by
  let C := Kv (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := C ⊔ S₀
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let B := (Lv L (v : G)).subgroupOf J
  let P := (Tv T (v : G)).subgroupOf J
  have hBJ : Lv L (v : G) ≤ J := (H.nonsingular_canonical_component D v hv).2.1.trans le_sup_left
  have hPJ : Tv T (v : G) ≤ J := hTS.trans le_sup_right
  have hB : B.map J.subtype = Lv L (v : G) := map_subgroupOf_eq_of_le hBJ
  have hJE : J ≤ normalizer (E.map J.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      E.le_normalizer_map J.subtype
  have hWU : Vv L V (v : G) ≤ E.map J.subtype := by
    rw [←hlocal,hred]
    exact le_normalizer_iff_commutator_le_left.mp (hBJ.trans hJE)
  let : IsElementaryAbelian 2 (E.map J.subtype) := IsElementaryAbelian.map _
  have hUC : E.map J.subtype ≤ centralizer (Vv L V (v : G) : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hWU)
  have hUS : E.map J.subtype ≤ S₀ :=
    ((map_mono (reducedPSubgroup_le_pCore 2 J)).trans
      (core_le_R_of_sylow L C (v : G) S (Kv_le_Gv _))).trans (R_le_S L C S₀ _)
  have hUM : E.map J.subtype ≤ Mv L (v : G) :=
    le_inf ((le_inf (hUS.trans (map_subtype_le _)) hUC).trans hctrl)
      (hUS.trans (map_subtype_le _))
  have hEq : S₀ ⊓ Mv L (v : G) = Tv T (v : G) :=
    (Chapter1.isSylowIn_iff.mp hs).2.2 _
      ((S.isPGroup'.map _).to_le inf_le_left)
      (le_inf hTS (Chapter1.isSylowIn_iff.mp hs).2.1) inf_le_right
  have hUT : E.map J.subtype ≤ Tv T (v : G) := (le_inf hUS hUM).trans_eq hEq
  refine ⟨hred ▸ hUT,?_⟩
  have hEP : E ≤ P := fun e he => hUT (mem_map_of_mem J.subtype he)
  have hgen' : B = ⁅B,elementaryAbelianMaxJ P⁆ := by
    apply map_injective J.subtype_injective
    rw [map_commutator,hB,←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hPJ]
    exact hgen
  have hmove : ⁅E,B⁆ ≠ ⊥ := by
    intro hz
    have hh := congrArg (Subgroup.map J.subtype) hz
    rw [map_commutator,hB,←hred,hlocal,Subgroup.map_bot] at hh
    have hc := D.nonsingular_moved_card H.chosen v hv
    rw [hh,card_bot] at hc
    norm_num at hc
  exact ChapterB.ff_of_thompson_generated_movement E B P hEP hgen' hmove

end CFSG.Quasithin.Chapter12.Section06

module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.PreferredSevenCore
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingSeven.FixedIndex
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The original Sylow fixed line and an elementary subgroup of Q

At the same preferred escaping point, the A7 core split and its natural
module give a two-element fixed subgroup for the original L_v. The trivial
common centralizer then bounds C_T(L) by two. Since the original C_V(L)
is nontrivial and contained in it, C_T(L)=C_V(L), of order two.

The natural A7 layer W lies in Q because it centralizes R_v, which
contains V. If W were contained in V, its order64 and the K_v-fixed
point line would generate V, making K_v normalize V and contradicting
source uniqueness. An involution in W outside V therefore enlarges V to
an elementary subgroup of order256 inside the original Q. The last
application identifies Q as elementary of order256 conditional on the
remaining cohomological upper bound; it does not assume Q is a module.

Source: Aschbacher--Smith, conclusion of12.6.2, printed p.828, combined
manuscript of1 March2004. The original Q upper bound and action model,
remaining HS/J4 exclusions, general12.6.13(3), and fixed-space elimination
remain required. Neither12.6.2 nor12.6.23 is asserted here. Earlier
invariance/TI and final discharge retain their existing source owners.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem centralizer_card_le_of_direct_split
    (W C A D : Subgroup G)
    (hWC : W ≤ centralizer (C : Set G)) (hdis : Disjoint W C)
    (hCA : C ≤ centralizer (A : Set G))
    (hD : D ≤ (W ⊔ C) ⊓ centralizer (A : Set G))
    (hDC : Disjoint D C) :
    Nat.card D ≤ Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) := by
  let F := W ⊓ centralizer (A : Set G)
  have hCN : C ≤ normalizer (W : Set G) :=
    (le_centralizer_iff.mp hWC).trans (Subgroup.centralizer_le_normalizer _)
  have hDF : D ≤ F ⊔ C := by
    intro x hx
    have hprod : x ∈ (W : Set G) * (C : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left W C hCN]
      exact (hD hx).1
    obtain ⟨w,hw,c,hc,rfl⟩ := hprod
    have hwA : w ∈ centralizer (A : Set G) := by
      simpa only [mul_inv_cancel_right] using
        (centralizer (A : Set G)).mul_mem (hD hx).2
          ((centralizer (A : Set G)).inv_mem (hCA hc))
    exact mul_mem_sup ⟨hw,hwA⟩ hc
  have hFC : F ≤ normalizer (C : Set G) :=
    (inf_le_left.trans hWC).trans (Subgroup.centralizer_le_normalizer _)
  have hDCN : D ≤ normalizer (C : Set G) :=
    hDF.trans (sup_le hFC C.le_normalizer)
  have hb := card_le_of_le (show C ⊔ D ≤ C ⊔ F from sup_le le_sup_left
    (hDF.trans_eq (sup_comm F C)))
  rw [card_sup_eq_mul_of_normalizes_of_disjoint C D hDCN hDC.symm,
    card_sup_eq_mul_of_normalizes_of_disjoint C F hFC
      (hdis.mono_left inf_le_left).symm] at hb
  exact (Nat.le_of_mul_le_mul_left hb (Nat.card_pos (α := C)))

variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original A7 split bounds the Sylow centralizer of L by its nontrivial
original fixed line. All subgroup placements and commutator layers are literal. -/
theorem SourceHypothesis.nonsingular_sylow_centralizer_of_seven_split
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Kv (v : G) ≤ M L)
    (hseven : ChapterC.IsAlternatingBlock (Kv (v : G)) 7)
    (hjoin : L ⊔ Rv T L (v : G) = LT T L)
    (hWU : (ChapterC.blockU (Kv (v : G))).map (Kv (v : G)).subtype ≤
      U (Kv (v : G)) (Tv T (v : G)))
    (hm : Vv L V (v : G) ≤ (ChapterC.blockU (Kv (v : G))).map (Kv (v : G)).subtype)
    (hlocal : ⁅U (Kv (v : G)) (Tv T (v : G)),Lv L (v : G)⁆ = Vv L V (v : G))
    (hsplit : Rv T L (v : G) =
      (ChapterC.blockU (Kv (v : G))).map (Kv (v : G)).subtype ⊔
        (Tv T (v : G) ⊓ centralizer (Kv (v : G) : Set G)))
    (hdis : Disjoint ((ChapterC.blockU (Kv (v : G))).map (Kv (v : G)).subtype)
      (Tv T (v : G) ⊓ centralizer (Kv (v : G) : Set G))) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ZV L V ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) = 2 := by
  let W := (ChapterC.blockU (Kv (v : G))).map (Kv (v : G)).subtype
  let C := Tv T (v : G) ⊓ centralizer (Kv (v : G) : Set G)
  let A := Lv L (v : G)
  let B := (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hAK : A ≤ Kv (v : G) := (H.nonsingular_canonical_component D v hv).2.1
  have hmove : ⁅W,A⁆ = Vv L V (v : G) := by
    apply le_antisymm ((commutator_mono hWU le_rfl).trans_eq hlocal)
    rw [←D.local_moved_generated H.chosen v hv]
    exact commutator_mono hm le_rfl
  have hfixed := hseven.seven_ambient_fixed_card_mul_moved_card hAK
  dsimp only at hfixed
  rw [hmove,D.nonsingular_moved_card H.chosen v hv] at hfixed
  change Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) * 32 = 64 at hfixed
  have htwo : Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) = 2 := by omega
  have hBQ : B ≤ Q T L :=
    (inf_le_inf (show (T : Subgroup G) ≤ LT T L from le_sup_right)
      (centralizer_le H.chosen.le_component)).trans_eq (H.join_centralizer_eq_core hTV)
  have hcommon := H.nonsingular_common_centralizer_eq_bot_of_join hTV v he hjoin
  have hBC : Disjoint B C := (disjoint_iff.mpr hcommon).mono_right inf_le_right
  have hb : Nat.card B ≤ 2 := by
    rw [←htwo]
    exact centralizer_card_le_of_direct_split W C A B
      (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le (map_subtype_le _))))
      hdis (inf_le_right.trans (centralizer_le hAK))
      (le_inf ((hBQ.trans (Q_le_Rv H.chosen v)).trans_eq hsplit)
        (inf_le_right.trans (centralizer_le (Lv_le_L L (v : G))))) hBC
  have hZB : ZV L V ≤ B := inf_le_inf H.chosen.le_sylow le_rfl
  have hZ : 2 ≤ Nat.card (ZV L V) := (one_lt_card_iff_ne_bot _).mpr hz
  have heq : ZV L V = B := eq_of_le_of_card_ge hZB (hb.trans hZ)
  exact ⟨heq.symm,le_antisymm hb (hZ.trans (card_le_of_le hZB))⟩

/-- At the same preferred escaping point, all premises of the original
Sylow-centralizer calculation are discharged by the constructed A7 block. -/
theorem SourceHypothesis.sylow_centralizer_eq_fixed_of_nonsingular_escape
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ZV L V ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) = 2 := by
  obtain ⟨w,hw,hew,hs,hi,hlt,hnot,hL,hA,hblock,hjoin,hcommon,hidx,
    hR,hcore,hred,hlocal,hmod,hcard,hsplit,hdis,hcomm⟩ :=
    H.exists_preferred_nonsingular_seven_core_of_fixed D hTV hTI hz v hv he
  let K := Kv (w : G)
  let S := Tv T (w : G)
  let J := K ⊔ S
  let E := reducedTwoSubgroup J
  let W := (⁅U K S,K⁆ : Subgroup G)
  have hAK : Lv L (w : G) ≤ K := (H.nonsingular_canonical_component D w hw).2.1
  have hJE : J ≤ normalizer (E.map J.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using E.le_normalizer_map J.subtype
  have hWU : W ≤ U K S := by
    change ⁅U K S,K⁆ ≤ U K S
    rw [show U K S = E.map J.subtype from hred]
    exact le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hJE)
  have hm : Vv L V (w : G) ≤ W := by
    rw [←hlocal]
    exact commutator_mono le_rfl hAK
  obtain ⟨P,hP⟩ := hs
  have hres := H.nonsingular_canonical_residual_commutator D w hw hblock.2.1 P
    (by rw [hP]; exact hred) (by rw [hP]; exact hm)
  rw [hP] at hres
  change ⁅U (Kv (w : G)) (Tv T (w : G)),Kv (w : G)⁆ ≤ U K S at hWU
  change Vv L V (w : G) ≤ ⁅U (Kv (w : G)) (Tv T (w : G)),Kv (w : G)⁆ at hm
  rw [hres] at hWU hm hsplit hdis
  exact H.nonsingular_sylow_centralizer_of_seven_split D hTV hz w hw hnot hblock
    hjoin hWU hm hlocal hsplit hdis
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original natural A7 layer supplies an involution outside V inside Q.
It therefore enlarges V to an actual elementary subgroup of order256. -/
theorem SourceHypothesis.nonsingular_elementary_core_extension
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Kv (v : G) ≤ M L)
    (hseven : ChapterC.IsAlternatingBlock (Kv (v : G)) 7)
    (hcore : Rv T L (v : G) = (Kv (v : G) ⊔ Tv T (v : G)).pCoreIn 2)
    (hWU : (ChapterC.blockU (Kv (v : G))).map (Kv (v : G)).subtype ≤
      U (Kv (v : G)) (Tv T (v : G)))
    (hc : Nat.card ((ChapterC.blockU (Kv (v : G))).map (Kv (v : G)).subtype) = 64) :
    let W := (ChapterC.blockU (Kv (v : G))).map (Kv (v : G)).subtype
    W ≤ Q T L ∧ ¬ W ≤ V ∧
      ∃ B : Subgroup G, V ≤ B ∧ B ≤ Q T L ∧
        IsElementaryAbelian 2 B ∧ Nat.card B = 256 := by
  let K := Kv (v : G)
  let W := (ChapterC.blockU K).map K.subtype
  let J := K ⊔ Tv T (v : G)
  have hWC : W ≤ centralizer (V : Set G) := by
    intro w hw x hx
    have hu := hWU hw
    rw [U_eq_omegaCenter,←hcore] at hu
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hu).2.2 x
      (Q_le_Rv H.chosen v (H.chosen.le_core hx))
  have hWQ : W ≤ Q T L := by
    rw [←H.join_centralizer_eq_core hTV]
    refine le_inf ?_ hWC
    intro w hw
    have hu := hWU hw
    rw [U_eq_omegaCenter,←hcore] at hu
    exact ((pCoreIn_le 2 _).trans inf_le_left)
      ((mem_omegaOneCenterAmbient_iff _ _).mp hu).1
  have hfix : W ⊓ centralizer (K : Set G) = ⊥ := by
    apply bot_unique
    rintro x ⟨⟨u,hu,rfl⟩,hx⟩
    have hf : (⟨u,hu⟩ : ChapterC.blockU K) ∈ ChapterC.blockFixed K := by
      change u ∈ center K
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext (hx k k.property)
    rw [hseven.seven_fixed_eq_bot,mem_bot] at hf
    exact congrArg (fun z : ChapterC.blockU K => ((z : K) : G)) hf
  have hvc : (v : G) ∈ centralizer (K : Set G) :=
    fun k hk => mem_centralizer_singleton_iff.mp (Kv_le_Gv (v : G) hk)
  have hvW : (v : G) ∉ W := by
    intro hm
    have hh := hfix.le ⟨hm,hvc⟩
    exact nonsingular_ne_one D hv (Subtype.ext hh)
  have hVcard : Nat.card V = 128 := by
    obtain ⟨e,_,_⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
    rw [Nat.card_congr (Additive.ofMul : V ≃ Additive V),Nat.card_congr e.toEquiv,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,BinaryPermutation.finrank_core]
    rfl
  have hWN : K ≤ normalizer (W : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K))
  have hnot : ¬ W ≤ V := by
    intro hWV
    have hv2 : (v : G)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ v.property
    have hsup : Nat.card (W ⊔ zpowers (v : G) : Subgroup G) = 128 := by
      rw [card_sup_zpowers_of_normalizing_involution W (v : G) hv2 hvW
        (Subgroup.centralizer_le_normalizer _
          ((centralizer_le (map_subtype_le _)) hvc)),hc]
    have heq : W ⊔ zpowers (v : G) = V := eq_of_le_of_card_ge
      (sup_le hWV (zpowers_le.mpr v.property)) (by rw [hsup,hVcard])
    have hKN : K ≤ normalizer (V : Set G) := by
      rw [←heq]
      exact (le_inf hWN ((le_centralizer_iff.mp (zpowers_le.mpr hvc)).trans
        (Subgroup.centralizer_le_normalizer _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact he (hKN.trans (H.chosen.normal_subgroup_normalizer_le
      H.source.toHypothesis1221 (H.chosen.le_component.trans le_sup_left)
      H.chosen.ne_bot (sup_le H.chosen.normalizes hTV)))
  obtain ⟨w,hw,hwV⟩ := Set.not_subset.mp hnot
  let B := V ⊔ zpowers w
  let : IsElementaryAbelian 2 W := hseven.2.1.elementary.map K.subtype
  let : IsElementaryAbelian 2 (zpowers w) := IsElementaryAbelian.of_le (zpowers_le.mpr hw)
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.sup_of_le_centralizer
    (zpowers_le.mpr (hWC hw))
  refine ⟨hWQ,hnot,B,le_sup_left,sup_le H.chosen.le_core (zpowers_le.mpr (hWQ hw)),hB,?_⟩
  rw [card_sup_zpowers_of_normalizing_involution V w
    (elemPow_eq_one_of_isElementaryAbelian _ hw) hwV
    (Subgroup.centralizer_le_normalizer _ (hWC hw)),hVcard]

/-- The full source setup constructs an elementary order256 subgroup of the
original Q; its containment of the original V is retained. -/
theorem SourceHypothesis.exists_core_elementary_256_of_nonsingular_escape
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ B : Subgroup G, V ≤ B ∧ B ≤ Q T L ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 256 := by
  obtain ⟨w,hw,hew,hs,hi,hlt,hnot,hL,hA,hblock,hjoin,hcommon,hidx,
    hR,hcore,hred,hlocal,hmod,hcard,hsplit,hdis,hcomm⟩ :=
    H.exists_preferred_nonsingular_seven_core_of_fixed D hTV hTI hz v hv he
  let K := Kv (w : G)
  let S := Tv T (w : G)
  let J := K ⊔ S
  let E := reducedTwoSubgroup J
  have hAK : Lv L (w : G) ≤ K := (H.nonsingular_canonical_component D w hw).2.1
  have hJE : J ≤ normalizer (E.map J.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using E.le_normalizer_map J.subtype
  have hWU : ⁅U K S,K⁆ ≤ U K S := by
    rw [show U K S = E.map J.subtype from hred]
    exact le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hJE)
  have hm : Vv L V (w : G) ≤ ⁅U K S,K⁆ := by
    rw [←hlocal]
    exact commutator_mono le_rfl hAK
  obtain ⟨P,hP⟩ := hs
  have hres := H.nonsingular_canonical_residual_commutator D w hw hblock.2.1 P
    (by rw [hP]; exact hred) (by rw [hP]; exact hm)
  rw [hP] at hres
  change ⁅U (Kv (w : G)) (Tv T (w : G)),Kv (w : G)⁆ ≤ U K S at hWU
  rw [hres] at hWU hcard
  exact (H.nonsingular_elementary_core_extension D hTV hz w hw hnot hblock hcore hWU hcard).2.2

/-- Once the cohomological upper bound is supplied, the actual Q is elementary
of order256. The source assembly must still prove that upper bound. -/
theorem SourceHypothesis.core_elementary_of_nonsingular_escape_of_card_le
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L)
    (hq : Nat.card (Q T L) ≤ 256) :
    IsElementaryAbelian 2 (Q T L) ∧ Nat.card (Q T L) = 256 := by
  obtain ⟨B,hVB,hBQ,hB,hcard⟩ :=
    H.exists_core_elementary_256_of_nonsingular_escape D hTV hTI hz v hv he
  have hEq : B = Q T L := eq_of_le_of_card_ge hBQ (hq.trans_eq hcard.symm)
  exact ⟨hEq ▸ hB,hEq ▸ hcard⟩
end CFSG.Quasithin.Chapter12.Section06

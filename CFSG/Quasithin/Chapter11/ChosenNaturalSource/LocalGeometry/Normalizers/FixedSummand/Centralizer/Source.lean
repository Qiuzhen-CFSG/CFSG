module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair.TI
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Orbit
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.JankoCentralizers
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Setup

/-!
# The nonbinary natural C.2.8 specialization for fixed-center control

Start with the actual I=L counterexample from the genuine 4.2 constructor.
The full omega-center module, section Sylow subgroup and chosen-module
conjugator remain unchanged. The proved natural-quotient results exclude
both the contained generalized-Fitting row and every constrained row.
Ordinary placement and the full quotient order force field four. The
cubic-centralizer obstruction excludes Ru, leaving central quotient J4.
The literal projected residual also avoids every conjugate of J4's Mathieu
local, by the shared full-quotient obstruction. Its radical normalizer also
avoids the first-centralizer and symmetric-linear locals. The full residual
also avoids any local with its quotient identified as binary L5. Its radical
normalizer lies in no involution centralizer and has trivial centralizer in
the literal component quotient. In particular this
proves maximal-two-local uniqueness over L for every degree greater than two.

Under actual shortness, the C.2.8 module lies in the characteristic moved
layer of L. The short-group normal-layer dichotomy makes it that entire
layer, which is the original chosen seed. This proves the identification
of the full module; it is not an assumption in the source constructor.

The field-four J4 local exclusion remains with
qt-d-1222-natural-point-fixed-summand. Nothing here asserts uniqueness in
that row or the unrestricted source 4.2.13. The companion Assembly module
applies the proved uniqueness and centralizer control to source 11.1.5
for n>2. Final preceding-source assembly belongs to
qt-d-1222-natural-normalizer-source.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
C.3.2--5 and C.4.1--8, printed pp.149--154; 4.2.12--13, pp.610--611;
and the TI argument in 11.1.5, p.766.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
open WeakClosure.Generation Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- All contained-Fitting and constrained cases are excluded for the actual
full natural quotient. The surviving component and full cubic center are retained. -/
theorem c28_ordinary_field_four {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hstrict : M < H) (hn : M ≤ normalizer (L : Set G)) :
    S.field.degree = 2 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
        ¬ K ≤ M.subgroupOf H ∧ L.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
        (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
          Nonempty (K ⧸ center K ≃* Rudvalis.Model)) := by
  have hN : (L.subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer h.component_le).mpr hn
  have hf := OddNormalizer.pushingUp_fitting_escape D S h hstrict (MulEquiv.refl _)
  obtain ⟨K,hK,hq,hout,_,hc⟩ := h.ordinary_or_constrained_escape hf
  rcases hc with ho | hc
  · have hcover : (L : Set G) = (L : Set G) * (L.pCoreIn 2 : Set G) := by
      apply le_antisymm
      · intro x hx
        exact ⟨x,hx,1,one_mem _,mul_one x⟩
      · rintro x ⟨a,ha,b,hb,rfl⟩
        exact mul_mem ha (pCoreIn_le 2 L hb)
    obtain ⟨hm,hd,he,hz⟩ := OddNormalizer.ordinary_last_models D S h le_rfl hcover
      D.le_componentCore (MulEquiv.refl _) K ho
    exact ⟨hd,he,hz,K,ho,h.ordinary_component_normal K ho,hout,
      h.ordinary_component_contains_original K ho,
      (h.ordinary_module_placement K ho).1.trans inf_le_right,hm⟩
  · exact (OddNormalizer.no_constrained_natural D S h hN (MulEquiv.refl _)
      K hK hq hout hc).elim

/-- The actual B=L constructor has only an ordinary J4 component remaining. -/
theorem c28_ordinary_jankoFour {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hstrict : M < H) (hn : M ≤ normalizer (L : Set G)) :
    S.field.degree = 2 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
        ¬ K ≤ M.subgroupOf H ∧ L.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
        Nonempty (K ⧸ center K ≃* Janko4.Model) := by
  obtain ⟨hf,⟨a⟩,hz,K,hK,hKn,hout,hLK,hWK,hm⟩ :=
    c28_ordinary_field_four D S h hstrict hn
  exact ⟨hf,⟨a⟩,hz,K,hK,hKn,hout,hLK,hWK,
    hm.resolve_right (fun er => no_original_rudvalis_field_four D S h hf a K hK er.some)⟩

/-- Application of the shared quotient geometry to the actual B=L constructor.
This retains the full W and the source's M-intersection normalizer. -/
theorem c28_original_jankoFour_local {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hstrict : M < H) (hn : M ≤ normalizer (L : Set G)) :
    S.field.degree = 2 ∧
      ∃ (K : Subgroup H) (hK : IsComponent H K),
        Nonempty (K ⧸ center K ≃* Janko4.Model) ∧
        IsPRadical 2 ((ordinaryComponentSubgroup R K).map (QuotientGroup.mk' (center K))) ∧
        normalizer ((ordinaryCoverProjection h K hK).range : Set (K ⧸ center K)) =
          (ordinaryComponentSubgroup M K).map (QuotientGroup.mk' (center K)) := by
  obtain ⟨_,_,_,K,hK,_,_,_,_,_⟩ := c28_ordinary_field_four D S h hstrict hn
  have hN := (normal_subgroupOf_iff_le_normalizer h.component_le).mpr hn
  have hc : (L : Set G) = (L : Set G) * (L.pCoreIn 2 : Set G) := by
    apply le_antisymm
    · intro x hx
      exact ⟨x,hx,1,one_mem _,mul_one x⟩
    · rintro x ⟨a,ha,b,hb,rfl⟩
      exact mul_mem ha (pCoreIn_le 2 L hb)
  obtain ⟨hk,hf,hr,hlocal,_⟩ := c28_covering_jankoFour_local D S h hstrict hN
    le_rfl hc D.le_componentCore (MulEquiv.refl _) (fun _ => rfl) K hK
  exact ⟨hf,K,hK,hk,hr,hlocal⟩

/-- The original B=L constructor also avoids every Mathieu local of its
remaining J4 component. This is an application of the shared covering theorem. -/
theorem c28_original_jankoFour_avoids_mathieu {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hstrict : M < H) (hn : M ≤ normalizer (L : Set G)) :
    S.field.degree = 2 ∧
      ∃ (K : Subgroup H) (hK : IsComponent H K)
        (e : K ⧸ center K ≃* Janko4.Model),
        ∀ g : Janko4.Model,
          ¬ (ordinaryCoverProjection h K hK).range.map e.toMonoidHom ≤
            (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self
              Janko4.matrixB_pow_four).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨hf,_,_,K,hK,_,_,_,_,⟨e⟩⟩ := c28_ordinary_jankoFour D S h hstrict hn
  have hc : (L : Set G) = (L : Set G) * (L.pCoreIn 2 : Set G) := by
    apply le_antisymm
    · intro x hx
      exact ⟨x,hx,1,one_mem _,mul_one x⟩
    · rintro x ⟨a,ha,b,hb,rfl⟩
      exact mul_mem ha (pCoreIn_le 2 L hb)
  exact ⟨hf,K,hK,e,fun g => c28_covering_jankoFour_avoids_mathieu D S h
    le_rfl hc D.le_componentCore (MulEquiv.refl _) K hK e g⟩

/-- The literal radical normalizer in the original B=L constructor avoids
the three displayed native local placements. Exhaustive placement remains to be proved. -/
theorem c28_original_jankoFour_radical_normalizer_avoids_locals {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hstrict : M < H) (hn : M ≤ normalizer (L : Set G)) :
    S.field.degree = 2 ∧
      ∃ (K : Subgroup H) (_hK : IsComponent H K)
        (e : K ⧸ center K ≃* Janko4.Model),
        let P := ((ordinaryComponentSubgroup R K).map
          (QuotientGroup.mk' (center K))).map e.toMonoidHom
        ∀ g : Janko4.Model,
          (¬ normalizer (P : Set Janko4.Model) ≤
            (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self
              Janko4.matrixB_pow_four).map (MulAut.conj g).toMonoidHom) ∧
          (¬ normalizer (P : Set Janko4.Model) ≤
            Janko4.InvolutionCentralizers.First.centralizer.map (MulAut.conj g).toMonoidHom) ∧
          (¬ normalizer (P : Set Janko4.Model) ≤
            Janko4.LocalStructure.SymmetricLinear.max4Subgroup.map
              (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hf,_,_,K,hK,_,_,_,_,⟨e⟩⟩ := c28_ordinary_jankoFour D S h hstrict hn
  have hN := (normal_subgroupOf_iff_le_normalizer h.component_le).mpr hn
  have hc : (L : Set G) = (L : Set G) * (L.pCoreIn 2 : Set G) := by
    apply le_antisymm
    · intro x hx
      exact ⟨x,hx,1,one_mem _,mul_one x⟩
    · rintro x ⟨a,ha,b,hb,rfl⟩
      exact mul_mem ha (pCoreIn_le 2 L hb)
  exact ⟨hf,K,hK,e,c28_covering_jankoFour_radical_normalizer_avoids_locals D S h
    hstrict hN le_rfl hc D.le_componentCore (MulEquiv.refl _) (fun _ => rfl) K hK e⟩

/-- The original B=L residual avoids every actual local having the binary
L5 quotient. Recognition of such locals is a separate placement obligation. -/
theorem c28_original_jankoFour_avoids_linear_five {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hstrict : M < H) (hn : M ≤ normalizer (L : Set G)) :
    S.field.degree = 2 ∧
      ∃ (K : Subgroup H) (hK : IsComponent H K)
        (e : K ⧸ center K ≃* Janko4.Model),
        ∀ (C : Subgroup Janko4.Model),
          (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2) → ∀ g : Janko4.Model,
          ¬ (ordinaryCoverProjection h K hK).range.map e.toMonoidHom ≤
            C.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨hf,_,_,K,hK,_,_,_,_,⟨e⟩⟩ := c28_ordinary_jankoFour D S h hstrict hn
  have hc : (L : Set G) = (L : Set G) * (L.pCoreIn 2 : Set G) := by
    apply le_antisymm
    · intro x hx
      exact ⟨x,hx,1,one_mem _,mul_one x⟩
    · rintro x ⟨a,ha,b,hb,rfl⟩
      exact mul_mem ha (pCoreIn_le 2 L hb)
  exact ⟨hf,K,hK,e,fun C eC g => c28_covering_jankoFour_avoids_linear_five D S h
    le_rfl hc D.le_componentCore (MulEquiv.refl _) K hK e C eC g⟩

/-- The B=L source constructor inherits control of the full projected radical
normalizer, retaining the actual component and the entire original W. -/
theorem c28_original_jankoFour_radical_normalizer_control {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hstrict : M < H) (hn : M ≤ normalizer (L : Set G)) :
    S.field.degree = 2 ∧
      ∃ (K : Subgroup H) (hK : IsComponent H K)
        (_e : K ⧸ center K ≃* Janko4.Model),
        normalizer (((ordinaryComponentSubgroup R K).map
          (QuotientGroup.mk' (center K))) : Set (K ⧸ center K)) ≤
          normalizer ((ordinaryCoverProjection h K hK).range : Set (K ⧸ center K)) := by
  obtain ⟨hf,_,_,K,hK,_,_,_,_,⟨e⟩⟩ := c28_ordinary_jankoFour D S h hstrict hn
  have hN := (normal_subgroupOf_iff_le_normalizer h.component_le).mpr hn
  exact ⟨hf,K,hK,e,ordinary_jankoFour_radical_normalizer_le_residual_normalizer h hN K hK e⟩

/-- The original constructor's radical normalizer cannot have the first
involution-centralizer type. This applies the shared covering theorem at B=L. -/
theorem c28_original_jankoFour_radical_normalizer_not_equiv_first {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hstrict : M < H) (hn : M ≤ normalizer (L : Set G)) :
    S.field.degree = 2 ∧
      ∃ (K : Subgroup H) (_hK : IsComponent H K)
        (e : K ⧸ center K ≃* Janko4.Model),
        ¬ Nonempty (normalizer (((ordinaryComponentSubgroup R K).map
          (QuotientGroup.mk' (center K))).map e.toMonoidHom : Set Janko4.Model) ≃*
          Janko4.InvolutionCentralizers.First.centralizer) := by
  obtain ⟨hf,_,_,K,hK,_,_,_,_,⟨e⟩⟩ := c28_ordinary_jankoFour D S h hstrict hn
  have hN := (normal_subgroupOf_iff_le_normalizer h.component_le).mpr hn
  have hc : (L : Set G) = (L : Set G) * (L.pCoreIn 2 : Set G) := by
    apply le_antisymm
    · intro x hx
      exact ⟨x,hx,1,one_mem _,mul_one x⟩
    · rintro x ⟨a,ha,b,hb,rfl⟩
      exact mul_mem ha (pCoreIn_le 2 L hb)
  exact ⟨hf,K,hK,e,c28_covering_jankoFour_radical_normalizer_not_equiv_first D S h
    hstrict hN le_rfl hc D.le_componentCore (MulEquiv.refl _) (fun _ => rfl) K hK e⟩

/-- The actual B=L constructor inherits trivial centralizer of its full
projected radical normalizer and exclusion from all involution centralizers.
The shared theorem uses full W and the literal component central quotient. -/
theorem c28_original_jankoFour_radical_normalizer_centralizer {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hstrict : M < H) (hn : M ≤ normalizer (L : Set G)) :
    S.field.degree = 2 ∧
      ∃ (K : Subgroup H) (_hK : IsComponent H K)
        (e : K ⧸ center K ≃* Janko4.Model),
        centralizer (normalizer (((ordinaryComponentSubgroup R K).map
          (QuotientGroup.mk' (center K))) : Set (K ⧸ center K)) : Set (K ⧸ center K)) = ⊥ ∧
        ∀ z : Janko4.Model, orderOf z = 2 →
          ¬ normalizer (((ordinaryComponentSubgroup R K).map
            (QuotientGroup.mk' (center K))).map e.toMonoidHom : Set Janko4.Model) ≤
            centralizer ({z} : Set Janko4.Model) := by
  obtain ⟨hf,_,_,K,hK,_,_,_,_,⟨e⟩⟩ := c28_ordinary_jankoFour D S h hstrict hn
  have hN := (normal_subgroupOf_iff_le_normalizer h.component_le).mpr hn
  have hc : (L : Set G) = (L : Set G) * (L.pCoreIn 2 : Set G) := by
    apply le_antisymm
    · intro x hx
      exact ⟨x,hx,1,one_mem _,mul_one x⟩
    · rintro x ⟨a,ha,b,hb,rfl⟩
      exact mul_mem ha (pCoreIn_le 2 L hb)
  exact ⟨hf,K,hK,e,
    c28_covering_jankoFour_radical_normalizer_centralizer D S h hstrict hN
      le_rfl hc D.le_componentCore (MulEquiv.refl _) (fun _ => rfl) K hK e,
    c28_covering_jankoFour_radical_normalizer_avoids_involutions D S h hstrict hN
      le_rfl hc D.le_componentCore (MulEquiv.refl _) (fun _ => rfl) K hK e⟩

/-- Failure of uniqueness over L forces degree two, without replacing the
constructor's full omega-center module by the original chosen module. -/
theorem field_four_of_not_unique
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    S.field.degree = 2 := by
  obtain ⟨J,H,P,_,_,_,_,_,hstrict,_,hC,_⟩ :=
    Chapter4.Section03.RankOneUniqueness.exists_source_C28 D S.source.toHypothesis1221 hnot
  exact (c28_ordinary_field_four D S hC hstrict inf_le_right).1

/-- The original L is a uniqueness subgroup in every degree greater than two. -/
theorem unique_of_degree_ne_two (hn : S.field.degree ≠ 2) :
    UniqueMaximalOvergroup L (normalizer (L : Set G)) := by
  by_contra hu
  exact hn (field_four_of_not_unique D S hu)

/-- The precise centralizer premise of the TI construction, with uniqueness
over L proved rather than inferred from uniqueness over LT. -/
theorem fixedCenter_control_of_degree_ne_two (hn : S.field.degree ≠ 2)
    (R U : Subgroup G) (hU : U ≤ radicalFixedCenter R L) (hne : U ≠ ⊥) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) :=
  Pair.fixedCenter_centralizer_control_of_unique (unique_of_degree_ne_two D S hn).2.2
    U hU hne


omit S [Finite G] in
/-- Under genuine shortness the unchanged C.2.8 module is the original seed.
The equality is proved from its moved-module condition and the short-group
normal-layer dichotomy; no module is replaced in the constructor. -/
theorem c28_module_eq_seed {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hn : M ≤ normalizer (L : Set G)) (hb : ChapterC.IsShort L) : W = V := by
  have hs : conjugateSpanBy L M = L :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy L M)
  have hWL : W ≤ L := hs ▸ h.module_le
  have hmove : W = ⁅W,L⁆ := hs ▸ h.module_commutator
  have hnW : L ≤ normalizer (W : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hmove.symm.le
  have hWC : W ≤ L.pCoreIn 2 :=
    le_pCoreIn_of_normalizes h.module_elementary.isPGroup hWL hnW
  have hWU : W ≤ (ChapterC.blockU L).map L.subtype := by
    rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype]
    exact hmove.le.trans (commutator_mono hWC le_rfl)
  let A := W.subgroupOf L
  let : A.Normal := normal_subgroupOf_of_le_normalizer hnW
  have hAU : A ≤ ChapterC.blockU L := by
    intro w hw
    obtain ⟨u,hu,he⟩ := hWU hw
    exact (Subtype.ext he : u = w) ▸ hu
  rcases ChapterC.RankOne.ChiProduct.short_normal_layer_dichotomy hb A hAU with hc | he
  · have hcentral : W ≤ centralizer (L : Set G) := by
      intro w hw l hl
      exact congrArg Subtype.val
        (mem_center_iff.mp (hc (show (⟨w,hWL hw⟩ : L) ∈ A from hw)) ⟨l,hl⟩)
    exact (h.module_nontrivial (hmove.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hcentral))).elim
  · rw [PointBlocks.seed_eq_blockU D hb]
    have hm := congrArg (map L.subtype) he
    simpa only [A,map_subgroupOf_eq_of_le hWL] using hm


/-- In the surviving ordinary row the actual full module has order 64 and
no L-fixed vectors. This uses the original SL3 cohomology calculation. -/
theorem c28_field_four_module {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hstrict : M < H) (hn : M ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) :
    W ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card W = 64 := by
  obtain ⟨hd,⟨e⟩,_⟩ := c28_ordinary_field_four D S h hstrict hn
  rw [c28_module_eq_seed D h hn hb]
  exact OddNormalizer.original_module_card_of_field_four D S hd e

open Chapter4
/-- Failure of uniqueness in the actual short-block setup retains the full
omega-center module, its Sylow marking and the original ordinary factor.
The remaining local obstruction has field four and a full cubic center. -/
theorem source_field_four_of_not_unique (hb : ChapterC.IsShort L)
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)),
      let W := Section02.Unitary.fullModule L
        ((P : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L L) ∧
      L ≤ J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧ H ⊓ normalizer (L : Set G) < H ∧
      J.pCoreIn 2 ≤ (P : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
        (H ⊓ normalizer (L : Set G)) L (J.pCoreIn 2) W ∧ W = V ∧
      (W ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card W = 64) ∧
      (∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
          (P : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
        V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) ∧
      S.field.degree = 2 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        L.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
        (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
          Nonempty (K ⧸ center K ≃* Rudvalis.Model)) := by
  obtain ⟨J,H,P,hJ,hLJ,hH,hJH,hout,hstrict,hRS,hC,hmark⟩ :=
    Section03.RankOneUniqueness.exists_source_C28 D S.source.toHypothesis1221 hnot
  exact ⟨J,H,P,hJ,hLJ,hH,hJH,hout,hstrict,hRS,hC,
    c28_module_eq_seed D hC inf_le_right hb,
    c28_field_four_module D S hC hstrict inf_le_right hb,hmark,
    c28_ordinary_field_four D S hC hstrict inf_le_right⟩

/-- Any failure of the precise TI centralizer premise has field four. -/
theorem field_four_of_fixedCenter_centralizer_escape
    (R U : Subgroup G) (hU : U ≤ radicalFixedCenter R L) (hne : U ≠ ⊥)
    (hout : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    S.field.degree = 2 := by
  by_contra hn
  exact hout (fixedCenter_control_of_degree_ne_two D S hn R U hU hne)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer

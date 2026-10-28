module

public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.BinarySectionAction
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallSectionSource
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.BinaryOuterMovement
public import CFSG.Quasithin.ChapterE.Section02.Structure.LinearThree.OuterActor
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThreeResidual

/-!
# Excluding the small automizer in the original linear-three source

The actual order-eight seed generates a normal binary section with a
fully moved component action. Its image has dimension two and contains
the displacement of the original nontrivial image involution. The original
Sylow supplies a noninner component actor, so intrinsic natural–dual
recognition forces the Sylow automizer of V to have order at least eight.
This contradicts the prescribed small action. Every section, action, marking
and outer actor is constructed from the original source hypotheses.

The larger-field wrapper first uses residual centralization to force the
field to be binary. Source: Aschbacher–Smith E.2.17, printed pp.229–230.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterE.Witnesses.LinearThree
open BenderPlacement
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

theorem source_binary_small_automizer_false
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 2)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) : False := by
  obtain ⟨w, hPQ, hB, ⟨d⟩, hZn, hZc, hZP, hPL, hLQ, hLJ, hE, hLV,
    hBcard, hZcard, hfull⟩ := source_binary_small_section T hP hs K hK hgen hm V hVT hvn
      hcore hout hfit hV U hTU hU f hf hk hD hratio hres
  let P := w.pair.subgroup.pCoreIn 2
  let Z := (center P).map P.subtype
  let B := P ⊓ V
  let L := conjugateSpanBy B ⊤
  let : Z.Normal := hZn
  let : L.Normal := normalizer_eq_top_iff.mp (top_unique (le_normalizer_conjugateSpanBy _ _))
  let : IsElementaryAbelian 2 (L.map (QuotientGroup.mk' Z)) := hE
  let hEq := DihedralCubic.section_elementary_of_image L Z
  let _ := hEq
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  obtain ⟨σ, c, _, hcfull⟩ := source_binary_section_action T hP K hgen L Z
    (hZP.trans hPL) hLJ hfull
  have hLcore : L ≤ pCore 2 H :=
    conjugateSpanBy_le (inf_le_left.trans hPQ) le_normalizer_of_normal
  have hLT : L ≤ (T : Subgroup H) := hLcore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hBL : B ≤ L := le_conjugateSpanBy B ⊤
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have hNV := ChapterE.minimalParabolic_normalizer_le T hP V
    (IsElementaryAbelian.isPGroup 2 V) hTV hout
  have hsmall := w.small_quaternion_core hVT hTV hcore hNV hfit hV hTU hU f hf hk hD hratio
  have hZB : Z ≤ B := by
    have hh := w.pair.core_center_eq_marked_ambient_center hTV hfit hPQ hsmall.2.2.1 d.center_card
    exact le_inf hZP (hh.le.trans inf_le_left)
  have hdim := section_seed_finrank c hBL hZB hBcard hZcard
  have hCidx : (centralizer (V : Set H)).relIndex U = Nat.card D := by
    change ((centralizer (V : Set H)).subgroupOf U).index = _
    rw [← hk, index_ker, MonoidHom.range_eq_top.mpr hf, card_top]
  have hTidx : (centralizer (V : Set H)).relIndex (T : Subgroup H) ≤ 4 :=
    ((centralizer (V : Set H)).relIndex_le_of_le_right hTU (by exact index_ne_zero_of_finite)).trans
      (hCidx ▸ hD)
  have hPidx : (centralizer (V : Set H)).relIndex P = 4 := by
    have he : ((centralizer (V : Set H)).subgroupOf P).map P.subtype = B := by
      rw [subgroupOf_map_subtype, inf_comm]
      exact hsmall.2.2.1
    have hh := ((centralizer (V : Set H)).subgroupOf P).card_mul_index
    have hb : Nat.card ((centralizer (V : Set H)).subgroupOf P) = 8 := by
      rw [← card_map_of_injective P.subtype_injective, he]
      exact hBcard
    rw [hb, d.card] at hh
    change 8 * (centralizer (V : Set H)).relIndex P = 32 at hh
    omega
  have hLidx : (centralizer (V : Set H)).relIndex L = 4 := by
    have hlo : (centralizer (V : Set H)).relIndex P ≤
        (centralizer (V : Set H)).relIndex L :=
      (centralizer (V : Set H)).relIndex_le_of_le_right hPL (by exact index_ne_zero_of_finite)
    have hhi : (centralizer (V : Set H)).relIndex L ≤
        (centralizer (V : Set H)).relIndex (T : Subgroup H) :=
      (centralizer (V : Set H)).relIndex_le_of_le_right hLT (by exact index_ne_zero_of_finite)
    omega
  have hLC : ⁅L,B⁆ ≤ Z := (commutator_mono le_rfl (inf_le_left.trans hPQ)).trans hLQ
  have hcardL : 32 ≤ Nat.card L := by
    rw [← d.card]
    exact Nat.card_le_card_of_injective (inclusion hPL) (inclusion_injective hPL)
  have hquot : 16 ≤ Nat.card (Additive (L ⧸ Z.subgroupOf L)) := by
    have hh := c.card_section
    rw [hZcard] at hh
    omega
  have hnon : Nontrivial (Additive (L ⧸ Z.subgroupOf L)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hVC := source_binary_image_le_component T hP hs K hK hgen hm V hVT hvn
  obtain ⟨v, hv, hvJ⟩ := Set.not_subset.mp hout
  let a : K.map q := ⟨q v, hVC (mem_map_of_mem q hv)⟩
  have ha : a ^ 2 = 1 := by
    apply Subtype.ext
    change (q v) ^ 2 = 1
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv, map_one]
  have hane : a ≠ 1 := by
    intro ha
    exact hvJ ((QuotientGroup.eq_one_iff v).mp (congrArg Subtype.val ha))
  have hmove : LinearMap.range (σ (a : H ⧸ J) - LinearMap.id) ≤ c.imageSpace B := by
    exact c.displacement_range_le_imageSpace_of_commutator_le V B
      (by rwa [commutator_comm]) ⟨v, trivial⟩ hv
  let _ := hnon
  obtain ⟨e⟩ := binary_model_equiv hm
  have hmarked : subspaceCommutator
      (σ.comp ((K.map q).subtype.comp e.symm.toMonoidHom)) ⊤ ⊤ = ⊤ := by
    change subspaceCommutator ((σ.comp (K.map q).subtype).comp e.symm.toMonoidHom) ⊤ ⊤ = ⊤
    rw [subspaceCommutator_comp_map, map_top_of_surjective _ e.symm.surjective]
    exact hcfull
  obtain ⟨t, α, hα, hact⟩ := Structure.LinearThree.source_outer_sylow_actor
    T hP hs K hK hgen (n := 1) (by decide) (by simpa using hm)
  have he := eight_le_binary_section_automizer J K L Z B V (T : Subgroup H)
    σ c e hmarked a ha hane hmove hdim.le hLT hTV inf_le_right hLC hLidx t α hα hact
  omega


/-- Residual centralization reduces every even-field linear-three row to the binary exclusion. -/
theorem source_linear_three_small_automizer_false
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 (2 ^ n))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) : False := by
  have hn1 := source_linear_three_parameter_eq_one_of_residual_centralizes
    T hP hs K hK hgen hn hm V hVT hvn hout hres
  subst n
  exact source_binary_small_automizer_false T hP hs K hK hgen (by simpa using hm)
    V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio hres

end CFSG.Quasithin.ChapterE.Witnesses.LinearThree

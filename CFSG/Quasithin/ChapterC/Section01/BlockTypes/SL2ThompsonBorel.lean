module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverCoordinates
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import Theory.Representation.SL2OrthogonalCover.OffenderGeometry
public import Theory.GroupTheory.ElementaryThompsonQuotientNormalizer
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.GroupTheory.SylowNormalSupplementRecognition

/-!
# Thompson normalization by a natural-block Borel

Pass to the faithful action on the full block U. Its literal quotient
coordinates identify the layer with SL₂ and its fixed-space quotient with
the natural module. Every nontrivial maximal-elementary image is an offender,
hence the layer Sylow intersection by B.4.2. The Thompson image is therefore
either trivial or that intersection, both normalized by the Borel. The
normalizer lifts through the two-kernel contained in the Sylow subgroup.

For the actual orbit configuration, restrict S to S∩N(L). This preserves
J(S), and the normal-supplement argument applies inside L(S∩N(L)). In
particular S itself need not normalize L, and the full central cover is retained.

Source: Aschbacher--Smith B.4.2 and15.1.21(i), printed pp.86,1097--1098.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions
universe u v
variable {G : Type u} {F : Type v} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
  [Algebra (ZMod 2) F]
variable (X : Subgroup G) [X.Normal] (hs : IsShort X)
variable [IsElementaryAbelian 2 (blockU X)] [IsElementaryAbelian 2 (BlockModule X)]
variable {r : SL(2,F) →* MulAut (Multiplicative (Fin 2 → F))}
variable (m : BlockModuleModel X r)
variable (hm : ∀ g v, (r g v).toAdd = specialLinearNatural 2 g v.toAdd)

include hs m hm
-- Transport the actual normal block to its faithful centralizer quotient.
omit [Finite F] [CharP F 2] in
private theorem natural_action_contract :
    letI : IsElementaryAbelian 2 ((blockU X).map X.subtype) := IsElementaryAbelian.map X.subtype
    ∃ (H : Type u) (_ : Group H) (_ : Finite H)
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer ((blockU X).map X.subtype : Set G))
    (L : Subgroup H) (_ : L.Normal) (e : L ≃* SL(2,F))
    (f : Additive ((blockU X).map X.subtype) →ₗ[ZMod 2] (Fin 2 → F)),
    Function.Surjective f ∧ X.map q = L ∧ (q.subgroupMap X).ker = pCore 2 X ∧
      f.ker = fixedSpace (NormalElementaryQuotient.representation _ q hq hk) L ∧
      (∀ (g : L) v, f (NormalElementaryQuotient.representation _ q hq hk g v) =
        Matrix.mulVec (e g).val (f v)) ∧
      subspaceCommutator (NormalElementaryQuotient.representation _ q hq hk) ⊤ L = ⊤ := by
  let W := (blockU X).map X.subtype
  let : W.Normal := inferInstance
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map X.subtype
  let C := centralizer (W : Set G)
  let q := QuotientGroup.mk' C
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = C := QuotientGroup.ker_mk' _
  let α := NormalElementaryQuotient.representation W q hq hk
  let L := X.map q
  let : L.Normal := inferInstance
  let j : blockU X ≃* W := (blockU X).equivMapOfInjective X.subtype X.subtype_injective
  let E : Additive W ≃ₗ[ZMod 2] Additive (blockU X) :=
    { j.symm.toAdditive with map_smul' := ZMod.map_smul j.symm.toAdditive }
  let f := (modelCoverMap m).comp E.toLinearMap
  have ha : Function.Surjective (q.subgroupMap X) := q.subgroupMap_surjective X
  have hka : (q.subgroupMap X).ker = pCore 2 X := by
    ext x
    rw [MonoidHom.mem_ker]
    have he : q.subgroupMap X x = 1 ↔ q (x:G) = 1 := Subtype.ext_iff
    rw [he,←MonoidHom.mem_ker,hk,←hs.centralizer_blockU]
    change (x : G) ∈ C ↔ _
    constructor
    · intro hx u hu
      exact Subtype.ext (hx u (mem_map_of_mem X.subtype hu))
    · intro hx w hw
      obtain ⟨u,hu,rfl⟩ := hw
      exact congrArg X.subtype (hx u hu)
  let e0 : (X ⧸ pCore 2 X) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hka.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap X) ha)
  let e : L ≃* SL(2,F) := e0.symm.trans m.quotientIso
  have he0 (x : X) : e0 (QuotientGroup.mk' (pCore 2 X) x) = q.subgroupMap X x := rfl
  have he (x : X) : e (q.subgroupMap X x) = m.quotientIso (QuotientGroup.mk' (pCore 2 X) x) := by
    change m.quotientIso (e0.symm _) = _
    rw [←he0,e0.symm_apply_apply]
  have hact (x : X) (v : Additive W) :
      E (α (q (x : G)) v) = modelCoverAction hs m (m.quotientIso (QuotientGroup.mk' (pCore 2 X) x)) (E v) := by
    rw [modelCoverAction_apply]
    apply Additive.toMul.injective
    change j.symm (α (q (x : G)) v).toMul = blockConjugate X x (j.symm v.toMul)
    apply j.injective
    rw [j.apply_symm_apply]
    apply Subtype.ext
    change ((α (q (x : G)) v).toMul : G) =
      (x:G) * (((j.symm v.toMul : blockU X) : X) : G) * (x:G)⁻¹
    rw [NormalElementaryQuotient.representation_apply]
    congr 2
    exact (congrArg Subtype.val (j.apply_symm_apply v.toMul)).symm
  have hf : Function.Surjective f := (modelCoverMap_surjective m).comp E.surjective
  have hi (g : L) (v : Additive W) :
      f (α (g : G ⧸ C) v) = Matrix.mulVec (e g).val (f v) := by
    obtain ⟨x,rfl⟩ := ha g
    change modelCoverMap m (E (α (q (x:G)) v)) = _
    rw [hact,he]
    exact modelCoverMap_intertwining hs m hm _ _
  have hkf : f.ker = fixedSpace α L := by
    ext v
    rw [NormalElementaryQuotient.mem_fixedSpace_image W q hq hk X v]
    change E v ∈ (modelCoverMap m).ker ↔ _
    rw [modelCoverMap_ker]
    constructor
    · intro hv x hx
      change (j.symm v.toMul : X) ∈ center X at hv
      have hh := (mem_center_iff.mp hv) (⟨x,hx⟩ : X)
      have hh' : x * (((j.symm v.toMul : blockU X) : X) : G) =
          (((j.symm v.toMul : blockU X) : X) : G) * x := congrArg X.subtype hh
      have hj : ((((j.symm v.toMul : blockU X) : X) : G)) = v.toMul :=
        congrArg Subtype.val (j.apply_symm_apply v.toMul)
      simpa only [hj] using hh'
    · intro hv
      change (j.symm v.toMul : X) ∈ center X
      rw [mem_center_iff]
      intro x
      apply Subtype.ext
      have hj : ((((j.symm v.toMul : blockU X) : X) : G)) = v.toMul :=
        congrArg Subtype.val (j.apply_symm_apply v.toMul)
      change (x:G) * (((j.symm v.toMul : blockU X) : X) : G) =
        (((j.symm v.toMul : blockU X) : X) : G) * (x:G)
      rw [hj]
      exact hv x x.property
  have hmove : ⁅W,X⁆ = W := by
    have hh := congrArg (map X.subtype) (short_commutator hs)
    simpa only [map_commutator, ←MonoidHom.range_eq_map, range_subtype] using hh
  have hwhole : subspaceCommutator α ⊤ L = ⊤ := by
    rw [←NormalElementaryQuotient.commutatorSpace_eq W q hq hk X]
    ext v
    change (v.toMul : G) ∈ ⁅W,X⁆ ↔ True
    rw [hmove]
    exact iff_true_intro v.toMul.property
  exact ⟨G ⧸ C,inferInstance,inferInstance,q,hq,hk,L,inferInstance,e,f,hf,rfl,hka,hkf,hi,hwhole⟩
end CFSG.Quasithin.ChapterC

namespace CFSG.Quasithin.ChapterC
open Representation.SL2NaturalOffenders
variable {A : Type*} [Group A] [Finite A]

/-- A natural-block Borel normalizes the Thompson subgroup of a normal
two-group supplement containing the block Sylow subgroup. -/
theorem IsL2EvenBlock.normal_borel_normalizes_thompson (X Q : Subgroup A) [X.Normal] {n : ℕ}
    (hb : IsL2EvenBlock X n) (hQ : IsPGroup 2 Q) (hgen : X ⊔ Q = ⊤)
    (P : Sylow 2 X) (hPQ : (P : Subgroup X).map X.subtype ≤ Q) :
    (normalizer (P : Set X)).map X.subtype ≤
      normalizer (elementaryAbelianMaxJ Q : Set A) := by
  classical
  have hb' := hb
  obtain ⟨hn,hs,F,_,_,hF,_,r,⟨m⟩,hm⟩ := hb'
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : IsElementaryAbelian 2 (blockU X) := hs.elementary
  let : IsElementaryAbelian 2 (BlockModule X) := hs.module_elementary
  let W := (blockU X).map X.subtype
  let : W.Normal := inferInstance
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map X.subtype
  obtain ⟨H,_,_,q,hq,hk,L,_,e,f,hf,hL,hka,hkf,he,hwhole⟩ :=
    natural_action_contract X hs m hm
  let α := NormalElementaryQuotient.representation W q hq hk
  have hα : Function.Injective α := NormalElementaryQuotient.representation_injective W q hq hk
  have ha : Function.Surjective (q.subgroupMap X) := q.subgroupMap_surjective X
  have hkernel : IsPGroup 2 q.ker := by
    apply q.kernel_isPGroup_of_normal_supplement X Q hQ hgen
    have heq : (q.comp X.subtype).ker = (q.subgroupMap X).ker := by
      ext x
      change q (x : A) = 1 ↔ q.subgroupMap X x = 1
      constructor
      · intro hx
        exact Subtype.ext hx
      · intro hx
        exact congrArg Subtype.val hx
    rw [heq,hka]
    exact pCore_isPGroup
  obtain ⟨Q0,hQ0⟩ := exists_sylow_eq_of_normal_supplement X Q hQ hgen P hPQ
  have hkerQ : q.ker ≤ Q := hQ0 ▸ hkernel.le_sylow_of_normal Q0
  have hWQ : W ≤ Q :=
    (map_mono (blockU_le_core.trans (pCore_isPGroup.le_sylow_of_normal P))).trans hPQ
  let T := Q0.mapSurjective hq
  have hT : (T : Subgroup H) = Q.map q := by change (Q0 : Subgroup A).map q = _; rw [hQ0]
  let R := P.mapSurjective ha
  have hRL : (R : Subgroup (X.map q)).map (X.map q).subtype ≤ T := by
    change ((P : Subgroup X).map (q.subgroupMap X)).map (X.map q).subtype ≤ _
    rw [map_map]
    have heq : (X.map q).subtype.comp (q.subgroupMap X) = q.comp X.subtype := by
      ext x
      rfl
    rw [heq,←map_map,hT]
    exact map_mono hPQ
  have hRZ : (R : Subgroup (X.map q)).map (X.map q).subtype =
      (T : Subgroup H) ⊓ (X.map q) := by
    have hh : (T : Subgroup H).subgroupOf (X.map q) = (R : Subgroup (X.map q)) :=
      R.is_maximal' T.isPGroup'.comap_subtype (map_le_iff_le_comap.mp hRL)
    rw [←hh,subgroupOf_map_subtype]
  have hB : ((normalizer (P : Set X)).map X.subtype).map q ≤
      normalizer ((T : Subgroup H) ⊓ L : Set H) := by
    rw [←hL]
    have hnorm := congrArg (fun K : Subgroup H => normalizer (K : Set H)) hRZ
    refine le_trans ?_ hnorm.le
    have hn := P.normalizer_map_surjective (q.subgroupMap X) ha
    have hh' := ((R : Subgroup (X.map q)).le_normalizer_map (X.map q).subtype)
    have hh'' := (map_mono hn.le).trans hh'
    rw [map_map] at hh''
    rw [map_map]
    have heq : (X.map q).subtype.comp (q.subgroupMap X) = q.comp X.subtype := by
      ext x
      rfl
    rwa [heq] at hh''
  have hfield : 2 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 2 ≤ n)
    norm_num at hh
    omega
  let Z := (T : Subgroup H) ⊓ L
  have hmax (B : Subgroup A) (hB : B ∈ elementaryAbelianMaxSubgroups Q)
      (hne : B.map q ≠ ⊥) : B.map q = Z := by
    have hoff := NormalElementaryQuotient.maxElementary_isOffender W q hq hk Q B hWQ hB
      (fun hz => hne ((map_eq_bot_iff B).mpr hz))
    exact offender_eq_sylowInf_of_generated_cover α hα L e hfield f hf hkf he hwhole T
      (by rw [hT]; exact map_mono hB.1) hoff
  have hJle : (elementaryAbelianMaxJ Q).map q ≤ Z := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro B hB
    apply map_le_iff_le_comap.mp
    by_cases hz : B.map q = ⊥
    · rw [hz]; exact bot_le
    · exact (hmax B hB hz).le
  have hJeq : (elementaryAbelianMaxJ Q).map q = ⊥ ∨
      (elementaryAbelianMaxJ Q).map q = Z := by
    by_cases hz : (elementaryAbelianMaxJ Q).map q = ⊥
    · exact Or.inl hz
    right
    have hex : ∃ B ∈ elementaryAbelianMaxSubgroups Q, B.map q ≠ ⊥ := by
      by_contra! hno
      apply hz
      apply bot_unique
      apply map_le_iff_le_comap.mpr
      exact sSup_le fun B hB => (map_le_iff_le_comap.mp ((hno B hB).le))
    obtain ⟨B,hB,hne⟩ := hex
    exact le_antisymm hJle ((hmax B hB hne).symm.le.trans (map_mono (le_sSup hB)))
  rw [←normalizer_comap_map_maxJ Q q hq hkerQ]
  apply map_le_iff_le_comap.mp
  rcases hJeq with hz | hz
  · rw [hz,show normalizer ((⊥ : Subgroup H) : Set H) = ⊤ from normalizer_eq_top _]
    exact le_top
  · rw [hz]
    exact hB
end CFSG.Quasithin.ChapterC

namespace CFSG.Quasithin.ChapterC
variable {A : Type*} [Group A] [Finite A]

/-- Preserve the orbit situation: only J(S) must normalize L. The original
Borel still normalizes J(S), without requiring S to normalize L. -/
theorem IsL2EvenBlock.borel_normalizes_thompson (L S : Subgroup A) {n : ℕ}
    (hb : IsL2EvenBlock L n) (hS : IsPGroup 2 S)
    (P : Sylow 2 L) (hPS : (P : Subgroup L).map L.subtype ≤ S)
    (hJN : elementaryAbelianMaxJ S ≤ normalizer (L : Set A)) :
    (normalizer (P : Set L)).map L.subtype ≤
      normalizer (elementaryAbelianMaxJ S : Set A) := by
  let R := S ⊓ normalizer (L : Set A)
  let H := L ⊔ R
  let X := L.subgroupOf H
  let Q := R.subgroupOf H
  have hRH : R ≤ H := le_sup_right
  have hLH : L ≤ H := le_sup_left
  have hJN' : elementaryAbelianMaxJ S ≤ R :=
    le_inf (sSup_le fun _ hB => hB.1) hJN
  have hJR : elementaryAbelianMaxJ R = elementaryAbelianMaxJ S :=
    elementaryAbelianMaxJ_eq_of_intermediate S R hJN' inf_le_left
  have hJmap : (elementaryAbelianMaxJ Q).map H.subtype = elementaryAbelianMaxJ S := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hRH,hJR]
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer inf_le_right)
  let e : X ≃* L := subgroupOfEquivOfLe hLH
  let P' := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hP' : (P' : Subgroup X).map X.subtype ≤ Q := by
    rintro z ⟨x,⟨l,hl,rfl⟩,rfl⟩
    exact ⟨hPS (mem_map_of_mem L.subtype hl),L.le_normalizer l.property⟩
  have hgen : X ⊔ Q = ⊤ := by
    rw [←subgroupOf_sup hLH hRH]
    exact subgroupOf_self H
  have hn := IsL2EvenBlock.normal_borel_normalizes_thompson X Q (hb.of_mulEquiv e.symm)
    ((hS.to_le inf_le_left).comap_subtype) hgen P' hP'
  have hPmap : (P' : Subgroup X).map e.toMonoidHom = (P : Subgroup L) := by
    change ((P : Subgroup L).map e.symm.toMonoidHom).map e.toMonoidHom = _
    rw [map_map]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id L := by
      apply MonoidHom.ext
      intro l
      exact e.apply_symm_apply l
    rw [he,map_id]
  have hBmap : ((normalizer (P' : Set X)).map X.subtype).map H.subtype =
      (normalizer (P : Set L)).map L.subtype := by
    have hh := map_equiv_normalizer_eq (P' : Subgroup X) e
    rw [hPmap] at hh
    change (normalizer (P' : Set X)).map e.toMonoidHom = normalizer (P : Set L) at hh
    rw [←hh,map_map,map_map]
    rfl
  have hh := (map_mono hn).trans ((elementaryAbelianMaxJ Q).le_normalizer_map H.subtype)
  rwa [hBmap,hJmap] at hh
end CFSG.Quasithin.ChapterC

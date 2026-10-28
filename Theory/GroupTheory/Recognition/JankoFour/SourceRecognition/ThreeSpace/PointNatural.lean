module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.PointImage
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Conjugation

/-!
# The natural four-space in the source three-space radical

The literal point image RQ_z/Q_z is carried into the native quintet using
faithful embeddings of both pair groups in Aut(M22). Its order sixteen and
normality identify it with the native inner core: its intersection with that
irreducible four-space is nonzero inside the elementary core of order 32.

The induced quotient map S/R to the native quintet quotient has its actual
representative formula. Composing with the original SQuotientEquiv retains
its full S5 marking. The native natural actor is the alternating subgroup of
that same five-part quotient. Transport through the opposite pair section
therefore identifies the ORIGINAL multiplicity space with the natural F4
plane, equivariantly for the originally marked A5. No abstract classification
of four-dimensional A5 modules or assumed geometric data is used.

Source: Aschbacher--Segev, *The uniqueness of groups of type J4*, Invent.
Math. 105 (1991), (4.4), printed pp.597--598, DOI 10.1007/BF01232280.
The imported native quintet and hexacode calculations retain their ATLAS
attribution and license; this module adds no finite computation certificate.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open Sporadic.Mathieu MathieuCode MathieuCode.M22Quintet
open MathieuCode.M22Quintet.CocodeTransfer
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
namespace PointNative

private theorem quintet_core_card : Nat.card (pCore 2 Q) = 32 := by
  have he := M22ChapterH.Quintet.core_card
  change Nat.card ((pCore 2 Q).map Q.subtype) = 32 at he
  rwa [card_map_of_injective Q.subtype_injective] at he

theorem quintet_card : Nat.card Q = 3840 := by
  have hi : (pCore 2 Q).index = 120 := by
    change Nat.card (Q ⧸ pCore 2 Q) = _
    rw [Nat.card_congr M22ChapterH.Quintet.quotientEquiv.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  rw [← (pCore 2 Q).card_mul_index,quintet_core_card,hi]

/-- The native quintet is recognized through its actual embedding in Aut(M22). -/
def quintetPairEquiv : Q ≃* M22ValueBound.Concrete.outerFirst :=
  (aut_card3840_equiv_pair
    (m22PairStabilizerEquivAut.toMonoidHom.comp Q.subtype)
    (m22PairStabilizerEquivAut.injective.comp Q.subtype_injective) quintet_card).some

/-- The irreducible inner four-space is the unique invariant sixteen-subgroup in the native core. -/
theorem invariant_sixteen_eq_inner (U : Subgroup MathieuCode.m22PairStabilizer)
    (hU : U ≤ K) (hn : Q ≤ normalizer (U : Set MathieuCode.m22PairStabilizer))
    (hc : Nat.card U = 16) : U = A0 := by
  let I : Subrepresentation (innerConjugation M22ChapterH.Quintet.innerInputs) := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 (U.subgroupOf A0).toAddSubgroup
    apply_mem_toSubmodule := by
      intro g v hv
      change (innerConjugation M22ChapterH.Quintet.innerInputs g v).toMul.val ∈ U
      rw [innerConjugation_apply]
      exact (mem_normalizer_iff.mp (hn g.property) v.toMul.val).mp hv }
  rcases M22ChapterH.Quintet.innerConjugation_isIrreducible.eq_bot_or_eq_top I with hi | hi
  · have hinter : A0 ⊓ U = ⊥ := by
      apply bot_unique
      intro v hv
      have hm : Additive.ofMul (⟨v,hv.1⟩ : A0) ∈ I := hv.2
      rw [hi] at hm
      have he : Additive.ofMul (⟨v,hv.1⟩ : A0) = 0 := hm
      exact mem_bot.mpr (congrArg (fun x : Additive A0 => x.toMul.val) he)
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A0 U
      ((hU.trans (Subgroup.map_subtype_le _)).trans
        M22ChapterH.Quintet.innerIntersection_normalizer)
    have hbound := Nat.card_le_card_of_injective
      (inclusion (show A0 ⊔ U ≤ K from sup_le inf_le_left hU)) (inclusion_injective _)
    rw [hinter,card_bot,M22ChapterH.Quintet.innerIntersection_card,hc,one_mul] at hprod
    rw [M22ChapterH.Quintet.core_card] at hbound
    omega
  · have hle : A0 ≤ U := by
      intro v hv
      have hm : Additive.ofMul (⟨v,hv⟩ : A0) ∈ I := by rw [hi]; trivial
      exact hm
    exact (eq_of_le_of_card_ge hle (by rw [hc,M22ChapterH.Quintet.innerIntersection_card])).symm

theorem twoCore_le_inner_ker : pCore 2 Q ≤
    (innerConjugation M22ChapterH.Quintet.innerInputs).ker := by
  intro g hg
  apply LinearMap.ext
  intro v
  apply innerInclusion_injective
  rw [innerInclusion_equivariant]
  have he : kernelConjugation g = 1 := M22ChapterH.Quintet.twoCore_le_kernelConjugation_ker hg
  rw [he]
  rfl

/-- The actual native inner action descends through the same E32 core. -/
def innerQuotientAction : Representation (ZMod 2) (Q ⧸ pCore 2 Q) (Additive A0) :=
  Representation.quotientOfLEKer (innerConjugation M22ChapterH.Quintet.innerInputs)
    (pCore 2 Q) twoCore_le_inner_ker

@[simp] theorem innerQuotientAction_mk (g : Q) :
    innerQuotientAction (QuotientGroup.mk' _ g) =
      innerConjugation M22ChapterH.Quintet.innerInputs g := rfl

/-- The full native five-part permutation action, retaining its quotient convention. -/
def innerFiveAction : Representation (ZMod 2) (Equiv.Perm (Fin 5)) (Additive A0) :=
  innerQuotientAction.comp M22ChapterH.Quintet.quotientEquiv.symm.toMonoidHom

@[simp] theorem innerFiveAction_q (g : Q) :
    innerFiveAction (NaturalQuotient.q g) = innerConjugation M22ChapterH.Quintet.innerInputs g := by
  rw [← M22ChapterH.Quintet.quotientEquiv_mk]
  change innerQuotientAction (M22ChapterH.Quintet.quotientEquiv.symm
    (M22ChapterH.Quintet.quotientEquiv _)) = _
  rw [MulEquiv.symm_apply_apply, innerQuotientAction_mk]

/-- The native natural actor is the actual alternating subgroup of the five-part quotient. -/
theorem naturalFivePart_eq_alternating :
    M22ChapterH.Quintet.naturalFivePartGroup = alternatingGroup (Fin 5) := by
  have hc : Nat.card M22ChapterH.Quintet.naturalFivePartGroup = 60 := by
    rw [Nat.card_congr M22ChapterH.Quintet.naturalFivePartModelEquiv.toEquiv,
      ← Nat.card_congr Hexacode.ZeroNatural.modelEquiv.toEquiv]
    exact Atlas.Codes.hexPointKernel_card _
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have hh := M22ChapterH.Quintet.naturalFivePartGroup.card_mul_index
  rw [hc,Nat.card_perm,Nat.card_fin] at hh
  norm_num at hh
  omega

/-- The actual alternating-five subgroup, with the native natural matrix marking. -/
def nativeAlternatingEquiv : alternatingGroup (Fin 5) ≃* SL2FourNatural.SL :=
  (MulEquiv.subgroupCongr naturalFivePart_eq_alternating.symm).trans
    M22ChapterH.Quintet.naturalFivePartModelEquiv

theorem innerFiveAction_natural (a : alternatingGroup (Fin 5)) (v : Additive A0) :
    M22ChapterH.Quintet.innerCoreNaturalEquiv (innerFiveAction a.val v) =
      SL2FourNatural.action (nativeAlternatingEquiv a)
        (M22ChapterH.Quintet.innerCoreNaturalEquiv v) := by
  have ha : a.val ∈ M22ChapterH.Quintet.naturalFivePartGroup :=
    naturalFivePart_eq_alternating.symm ▸ a.property
  obtain ⟨g,hg⟩ := ha
  have he : (M22ChapterH.Quintet.naturalActorFivePartEquiv (QuotientGroup.mk g)) =
      (MulEquiv.subgroupCongr naturalFivePart_eq_alternating.symm a) := by
    apply Subtype.ext
    exact hg
  rw [←hg,MonoidHom.comp_apply,innerFiveAction_q]
  have hh := M22ChapterH.Quintet.innerCore_fivePart_natural g v
  rw [he] at hh
  exact hh
end PointNative

namespace ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)
attribute [local instance] R_normal_in_S_intrinsic

theorem point_r_noncentral (h : IsTypeJ4 z) : d.rInCore ∉ center (core z) := by
  have hz1 : z ≠ 1 := by intro he; have hi := h.involution; simp [he] at hi
  have hr1 : d.r ≠ 1 := by intro he; exact hz1 (isConj_one_left.mp (he ▸ d.r_conj))
  intro hc
  have hm : d.r ∈ zpowers z := by
    rw [← LocalGeometry.core_center_image h]
    exact mem_map_of_mem _ (mem_map_of_mem _ hc)
  obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : zpowers z)).mp
    ((Nat.card_zpowers z).trans h.involution)
  exact d.r_ne (congrArg Subtype.val ((hw ⟨_,hm⟩
    (fun he => hr1 (congrArg Subtype.val he))).trans
      (hw ⟨z,mem_zpowers z⟩ (fun he => hz1 (congrArg Subtype.val he))).symm))

/-- The original pair image is recognized by its faithful cubic projection. -/
def pairNativeEquiv (h : IsTypeJ4 z) : d.pairImage ≃* Q := by
  let := h.extraspecial
  have hf : Function.Injective (e.projection.comp d.pairImage.subtype) := by
    change Function.Injective (e.projection.comp
      ((Subgroup.centralizer ({(d.rInCore : centralizer z)} : Set (centralizer z))).map
        (QuotientGroup.mk' (core z))).subtype)
    rw [←coreVectorStabilizer_eq_centralizer_image h d.rInCore (d.point_r_noncentral h)]
    exact coreVectorStabilizer_projection_injective h e d.rInCore (d.point_r_noncentral h)
  exact (aut_card3840_equiv_pair (e.projection.comp d.pairImage.subtype) hf
    (d.pairImage_structure h).1).some.trans PointNative.quintetPairEquiv.symm

/-- The literal point image, carried into the native pair stabilizer. -/
def pointNativeImage (h : IsTypeJ4 z) : Subgroup MathieuCode.m22PairStabilizer :=
  d.pointImage.map (Q.subtype.comp (d.pairNativeEquiv h).toMonoidHom)

theorem pointNativeImage_eq (h : IsTypeJ4 z) : d.pointNativeImage h = A0 := by
  have he := pCore_map_iso 2 (d.pairNativeEquiv h)
  have hle : d.pointNativeImage h ≤ MathieuCode.M22Quintet.K := by
    change d.pointImage.map _ ≤ (pCore 2 Q).map Q.subtype
    rw [←he,Subgroup.map_map]
    exact map_mono (d.pointImage_le_twoCore h)
  have hn : Q ≤ normalizer (d.pointNativeImage h : Set MathieuCode.m22PairStabilizer) := by
    let := d.pointImage_normal h
    have hnormal : (d.pointImage.map (d.pairNativeEquiv h).toMonoidHom).Normal :=
      (inferInstance : d.pointImage.Normal).map _ (d.pairNativeEquiv h).surjective
    have hh := (d.pointImage.map (d.pairNativeEquiv h).toMonoidHom).le_normalizer_map Q.subtype
    rw [normalizer_eq_top, ←MonoidHom.range_eq_map, range_subtype, map_map] at hh
    exact hh
  apply PointNative.invariant_sixteen_eq_inner _ hle hn
  change Nat.card (d.pointImage.map
    (Q.subtype.comp (d.pairNativeEquiv h).toMonoidHom)) = 16
  exact (card_map_of_injective
    (show Function.Injective (Q.subtype.comp (d.pairNativeEquiv h).toMonoidHom) from
      Q.subtype_injective.comp (d.pairNativeEquiv h).injective)).trans (d.pointImage_card h)

/-- A group equivalence with the exact native inner core. -/
def pointNativeEquiv (h : IsTypeJ4 z) : d.pointImage ≃* A0 :=
  (d.pointImage.equivMapOfInjective
    (Q.subtype.comp (d.pairNativeEquiv h).toMonoidHom)
    (Q.subtype_injective.comp (d.pairNativeEquiv h).injective)).trans
      (MulEquiv.subgroupCongr (d.pointNativeImage_eq h))

@[simp] theorem pointNativeEquiv_apply (h : IsTypeJ4 z) (u : d.pointImage) :
    (d.pointNativeEquiv h u).val = (d.pairNativeEquiv h u.val).val := rfl

/-- This equivalence intertwines actual conjugation, not only the group structures. -/
theorem pointNativeEquiv_intertwines (h : IsTypeJ4 z) (p : d.pairImage) (u : d.pointImage) :
    Additive.ofMul (d.pointNativeEquiv h (d.pointImageAction h p u)) =
      innerConjugation M22ChapterH.Quintet.innerInputs (d.pairNativeEquiv h p)
        (Additive.ofMul (d.pointNativeEquiv h u)) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [innerConjugation_apply]
  change (d.pairNativeEquiv h (p*u.val*p⁻¹)).val =
    (d.pairNativeEquiv h p).val * (d.pairNativeEquiv h u.val).val *
      (d.pairNativeEquiv h p).val⁻¹
  simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv]

/-- The marked S/R quotient into the native quintet quotient uses the literal induced map. -/
def pointNativeFactorEquiv (h : IsTypeJ4 z) :
    (d.S ⧸ d.R.subgroupOf d.S) ≃* (Q ⧸ pCore 2 Q) :=
  (d.pointFactorEquiv h).trans
    (QuotientGroup.congr _ _ (d.pairNativeEquiv h) (pCore_map_iso 2 (d.pairNativeEquiv h)))

@[simp] theorem pointNativeFactorEquiv_mk (h : IsTypeJ4 z) (s : d.S) :
    d.pointNativeFactorEquiv h (QuotientGroup.mk' _ s) =
      QuotientGroup.mk' (pCore 2 Q)
        (d.pairNativeEquiv h (d.pairProjection (inclusion d.S_le_pairCentralizer s))) := rfl


/-- The original S5 marking compared with the literal native five-part quotient. -/
def markedNativeFiveEquiv (h : IsTypeJ4 z) :
    Equiv.Perm (Fin 5) ≃* Equiv.Perm (Fin 5) :=
  ((d.SQuotientEquiv h).symm.trans (d.pointNativeFactorEquiv h)).trans
    M22ChapterH.Quintet.quotientEquiv

@[simp] theorem markedNativeFiveEquiv_mk (h : IsTypeJ4 z) (s : d.S) :
    d.markedNativeFiveEquiv h (d.SQuotientEquiv h (QuotientGroup.mk' _ s)) =
      NaturalQuotient.q
        (d.pairNativeEquiv h (d.pairProjection (inclusion d.S_le_pairCentralizer s))) := by
  change M22ChapterH.Quintet.quotientEquiv (d.pointNativeFactorEquiv h
    ((d.SQuotientEquiv h).symm (d.SQuotientEquiv h (QuotientGroup.mk' _ s)))) = _
  rw [MulEquiv.symm_apply_apply,d.pointNativeFactorEquiv_mk,
    M22ChapterH.Quintet.quotientEquiv_mk]

/-- One choice of the proved transport from the original pair section to RQ/Q. -/
def multiplicityPointEquiv (h : IsTypeJ4 z) : d.multiplicitySpace ≃* d.pointImage :=
  (d.exists_multiplicity_pointImage_equiv h).choose

theorem multiplicityPointEquiv_intertwines (h : IsTypeJ4 z)
    (a : d.S ⧸ d.R.subgroupOf d.S) (w : d.multiplicitySpace) :
    d.multiplicityPointEquiv h (d.multiplicityAction h a w) =
      d.pointQuotientAction h a (d.multiplicityPointEquiv h w) :=
  (d.exists_multiplicity_pointImage_equiv h).choose_spec a w

/-- The same pair section, with its actual action, is the native inner four-space. -/
def multiplicityNativeEquiv (h : IsTypeJ4 z) : d.multiplicitySpace ≃* A0 :=
  (d.multiplicityPointEquiv h).trans (d.pointNativeEquiv h)

theorem multiplicityNativeEquiv_intertwines (h : IsTypeJ4 z)
    (a : Equiv.Perm (Fin 5)) (w : d.multiplicitySpace) :
    Additive.ofMul (d.multiplicityNativeEquiv h (d.markedMultiplicityAction h a w)) =
      PointNative.innerFiveAction (d.markedNativeFiveEquiv h a)
        (Additive.ofMul (d.multiplicityNativeEquiv h w)) := by
  obtain ⟨a,rfl⟩ := (d.SQuotientEquiv h).surjective a
  obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective (d.R.subgroupOf d.S) a
  rw [d.markedMultiplicityAction_quotient,d.markedNativeFiveEquiv_mk,
    PointNative.innerFiveAction_q]
  change Additive.ofMul (d.pointNativeEquiv h
    (d.multiplicityPointEquiv h (d.multiplicityAction h _ w))) = _
  rw [d.multiplicityPointEquiv_intertwines,d.pointQuotientAction_mk]
  exact d.pointNativeEquiv_intertwines h _ _

/-- The full S5 marking preserves its characteristic alternating subgroup. -/
theorem markedNativeFive_alternating (h : IsTypeJ4 z) :
    (alternatingGroup (Fin 5)).map (d.markedNativeFiveEquiv h).toMonoidHom =
      alternatingGroup (Fin 5) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  exact ((alternatingGroup (Fin 5)).index_map_equiv (d.markedNativeFiveEquiv h)).trans
    alternatingGroup.index_eq_two

/-- The original marked A5, via the actual quotient comparison, acts as SL2(4). -/
def markedNaturalActorEquiv (h : IsTypeJ4 z) :
    alternatingGroup (Fin 5) ≃* SL2FourNatural.SL :=
  (((d.markedNativeFiveEquiv h).subgroupMap (alternatingGroup (Fin 5))).trans
    (MulEquiv.subgroupCongr (d.markedNativeFive_alternating h))).trans
      PointNative.nativeAlternatingEquiv

/-- The binary coordinates of the original four-space in the native F4 plane. -/
def multiplicityNaturalEquiv (h : IsTypeJ4 z) :
    letI := d.multiplicitySpace_elementary h
    Additive d.multiplicitySpace ≃ₗ[ZMod 2] SL2FourNatural.V := by
  let := d.multiplicitySpace_elementary h
  let F := (d.multiplicityNativeEquiv h).toAdditive
  exact (F.toLinearEquiv (ZMod.map_smul F)).trans M22ChapterH.Quintet.innerCoreNaturalEquiv

/-- AS91 (4.4): the SAME multiplicity space is natural for the original marked A5. -/
theorem multiplicityNaturalEquiv_intertwines (h : IsTypeJ4 z) :
    letI := d.multiplicitySpace_elementary h
    ∀ (a : alternatingGroup (Fin 5)) (w : Additive d.multiplicitySpace),
      d.multiplicityNaturalEquiv h
        (Additive.ofMul (d.markedMultiplicityAction h a.val w.toMul)) =
      SL2FourNatural.action (d.markedNaturalActorEquiv h a) (d.multiplicityNaturalEquiv h w) := by
  let := d.multiplicitySpace_elementary h
  intro a w
  change M22ChapterH.Quintet.innerCoreNaturalEquiv
    (Additive.ofMul (d.multiplicityNativeEquiv h (d.markedMultiplicityAction h a.val w.toMul))) = _
  rw [d.multiplicityNativeEquiv_intertwines]
  let a' : alternatingGroup (Fin 5) :=
    (((d.markedNativeFiveEquiv h).subgroupMap (alternatingGroup (Fin 5))).trans
      (MulEquiv.subgroupCongr (d.markedNativeFive_alternating h))) a
  exact PointNative.innerFiveAction_natural a' _

/-- Simultaneous natural coordinates and group marking, with no extra premise. -/
theorem exists_multiplicity_natural_equiv (h : IsTypeJ4 z) :
    letI := d.multiplicitySpace_elementary h
    ∃ (A : alternatingGroup (Fin 5) ≃* SL2FourNatural.SL)
      (F : Additive d.multiplicitySpace ≃ₗ[ZMod 2] SL2FourNatural.V),
      ∀ (a : alternatingGroup (Fin 5)) (w : Additive d.multiplicitySpace),
        F (Additive.ofMul (d.markedMultiplicityAction h a.val w.toMul)) =
          SL2FourNatural.action (A a) (F w) := by
  let := d.multiplicitySpace_elementary h
  exact ⟨d.markedNaturalActorEquiv h,d.multiplicityNaturalEquiv h,
    d.multiplicityNaturalEquiv_intertwines h⟩

end ThreeSpaceData
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end

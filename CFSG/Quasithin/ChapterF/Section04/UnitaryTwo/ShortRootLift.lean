module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ShortRootRecognition
public import Theory.GroupTheory.CentralExtensionAbelianSylowSection

/-!
# Lifting the recognized A₅ through the original short-root line

Take the full preimage of the normal A₅ recognized in C_G(t)/⟨t⟩. Its
Sylow preimage is contained in the original elementary eight-group V.
The abelian Sylow central-extension theorem therefore splits its derived
subgroup over A₅. This derived subgroup is normal in C_G(t), and the
original quotient restricts to an isomorphism on it.

The actual Sylow four-group of this lift lies in V. These are the central
cover and marking steps of Aschbacher–Smith F.4.42, printed p.295.
-/

open Subgroup
open scoped IsMulCommutative
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.ShortRootLift
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open CFSG.Quasithin.ChapterF.UnitaryTwo
open ShortRootFixedFour ShortRootQuotient ShortRootFusion ShortRootRecognition
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
  (amalgam 1 hn) (G := G0)) (i : G0 →* G)
local notation "H" => ambientShortCentralizer c i
local notation "U" => ambientLine c i
local notation "Hq" => H ⧸ U
local notation "q" => QuotientGroup.mk' U

/-- The actual eight-group before quotienting by the marked short root. -/
def ambientEight : Subgroup H := ShortRoot.orthogonalInCentralizer.map (shortCentralizerEmbedding c i)

instance ambientEight_elementary : IsElementaryAbelian 2 (ambientEight c i) :=
  IsElementaryAbelian.map (shortCentralizerEmbedding c i)

omit [Finite G] in
theorem ambientLine_le_eight : U ≤ ambientEight c i := by
  apply zpowers_le.mpr
  exact ⟨ShortRoot.mark,ShortRoot.centralLine_le_orthogonal (mem_zpowers _),
    shortCentralizerEmbedding_mark c i⟩

omit [Finite G] in
theorem ambientEight_map : (ambientEight c i).map q = sourceFour c i := by
  rw [ambientEight,map_map]
  rfl

omit [Finite G] in
theorem sourceFour_comap : (sourceFour c i).comap q = ambientEight c i := by
  rw [← ambientEight_map]
  apply le_antisymm
  · intro x hx
    obtain ⟨y,hy,he⟩ := hx
    have hk : y⁻¹ * x ∈ U := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (y⁻¹ * x) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    simpa only [mul_inv_cancel_left] using (ambientEight c i).mul_mem hy
      (ambientLine_le_eight c i hk)
  · exact le_comap_map q (ambientEight c i)

/-- The recognized simple normal subgroup in the actual quotient. -/
def quotientClosure : Subgroup Hq := normalClosure (sourceFour c i : Set Hq)

/-- Its full preimage in the actual short-root centralizer. -/
def closurePreimage : Subgroup H := (quotientClosure c i).comap q

instance closurePreimage_normal : (closurePreimage c i).Normal := inferInstanceAs
  ((normalClosure (sourceFour c i : Set Hq)).comap q).Normal

/-- The actual quotient restriction, with all of its central kernel retained. -/
def closureProjection : closurePreimage c i →* quotientClosure c i :=
  ((q).comp (closurePreimage c i).subtype).codRestrict _ fun x => x.property

omit [Finite G] in
theorem closureProjection_surjective : Function.Surjective (closureProjection c i) := by
  intro a
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective U a.val
  exact ⟨⟨x,by change q x ∈ quotientClosure c i; rw [hx]; exact a.property⟩,Subtype.ext hx⟩

omit [Finite G] in
theorem closureProjection_ker : (closureProjection c i).ker = (U).subgroupOf (closurePreimage c i) := by
  ext x
  change (⟨q x.val,x.property⟩ : quotientClosure c i) = 1 ↔ x.val ∈ U
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

omit [Finite G] in
omit [Finite G] in
theorem closureProjection_ker_central :
    (closureProjection c i).ker ≤ center (closurePreimage c i) := by
  intro x hx
  have hline : x.val ∈ U := by
    rw [closureProjection_ker] at hx
    exact hx
  have hcen : x.val ∈ center H := (zpowers_le.mpr (ambientMark_central c i)) hline
  exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hcen y.val)

omit [Finite G] in
omit [Finite G] in
theorem closureProjection_ker_two (hi : Function.Injective i) : IsPGroup 2 (closureProjection c i).ker := by
  have hm : orderOf (ambientMark c i) = 2 := by
    rw [← shortCentralizerEmbedding_mark]
    exact (orderOf_injective (shortCentralizerEmbedding c i) (shortCentralizerEmbedding_injective c i hi) _).trans ShortRoot.mark_order
  have hu : IsPGroup 2 U := IsPGroup.of_card (n := 1) (by rw [ambientLine,Nat.card_zpowers,hm,pow_one])
  rw [closureProjection_ker]
  exact hu.comap_subtype

omit [Finite G] in
theorem sourceFour_le_closure : sourceFour c i ≤ quotientClosure c i :=
  subset_normalClosure

/-- The four-group V* is a Sylow subgroup of its recognized A₅ closure. -/
def closureSylow (hi : Function.Injective i)
    (e : quotientClosure c i ≃* alternatingGroup (Fin 5)) : Sylow 2 (quotientClosure c i) :=
  Sylow.ofCard ((sourceFour c i).subgroupOf (quotientClosure c i)) (by
    have hL : Nat.card (quotientClosure c i) = 60 := by rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]; norm_num
    rw [Nat.card_congr (subgroupOfEquivOfLe (sourceFour_le_closure c i)).toEquiv,
      sourceFour_card c i hi,hL]
    rw [show 60 = 2 ^ 2 * 15 by decide, Nat.factorization_mul (by decide) (by decide),
      Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
    rfl)

theorem closureSylow_preimage_commutative (hi : Function.Injective i)
    (e : quotientClosure c i ≃* alternatingGroup (Fin 5)) :
    IsMulCommutative ((closureSylow c i hi e : Subgroup (quotientClosure c i)).comap (closureProjection c i)) := by
  let P := ((closureSylow c i hi e : Subgroup (quotientClosure c i)).comap (closureProjection c i))
  have hp (x : P) : x.val.val ∈ ambientEight c i := by
    rw [← sourceFour_comap]
    exact x.property
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun a : ambientEight c i => a.val) (mul_comm (⟨x.val.val,hp x⟩ : ambientEight c i)
    (⟨y.val.val,hp y⟩ : ambientEight c i))


local notation "E" => closurePreimage c i
omit [Finite G] in
/-- The recognized A₅ is perfect, and its full preimage has abelian Sylow
preimage given by the original elementary eight-group. -/
theorem closure_quotient_perfect
    (e : quotientClosure c i ≃* alternatingGroup (Fin 5)) :
    Group.IsPerfect (quotientClosure c i) := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem closure_sylow_preimage
    (hi : Function.Injective i)
    (e : quotientClosure c i ≃* alternatingGroup (Fin 5)) :
    IsMulCommutative ((closureSylow c i hi e : Subgroup (quotientClosure c i)).comap (closureProjection c i)) := by
  exact closureSylow_preimage_commutative c i hi e

theorem closure_section
    (hi : Function.Injective i)
    (e : quotientClosure c i ≃* alternatingGroup (Fin 5)) :
    ∃ s : quotientClosure c i →* E,
      (closureProjection c i).comp s = MonoidHom.id _ ∧ s.range = commutator E := by
  let : Group.IsPerfect (quotientClosure c i) := closure_quotient_perfect c i e
  have hsurj := closureProjection_surjective c i
  have hker := closureProjection_ker_central c i
  have hpker := closureProjection_ker_two c i hi
  exact CentralExtension.exists_derived_section_of_abelian_sylow_preimage
    (closureProjection c i) hsurj hker hpker (closureSylow c i hi e)
    (closure_sylow_preimage c i hi e)

/-- The actual normal A₅ lift is the derived subgroup of the full preimage. -/
def liftedA : Subgroup H := ⁅closurePreimage c i,closurePreimage c i⁆

instance liftedA_normal : (liftedA c i).Normal := by
  dsimp only [liftedA]
  infer_instance

theorem liftedA_equiv
    (hi : Function.Injective i)
    (e : quotientClosure c i ≃* alternatingGroup (Fin 5)) :
    Nonempty (liftedA c i ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨s,hs,hr⟩ := closure_section c i hi e
  have hsi : Function.Injective s := by
    intro a b he
    have ha := DFunLike.congr_fun hs a
    have hb := DFunLike.congr_fun hs b
    exact ha.symm.trans ((congrArg (closureProjection c i) he).trans hb)
  have hm : s.range.map (closurePreimage c i).subtype = liftedA c i := by
    rw [hr,Subgroup.map_subtype_commutator]
    rfl
  exact ⟨(MulEquiv.subgroupCongr hm.symm).trans
    (((s.range).equivMapOfInjective (closurePreimage c i).subtype Subtype.val_injective).symm.trans
      ((MonoidHom.ofInjective hsi).symm.trans e))⟩



/-- The lifted A₅ maps isomorphically onto the recognized quotient closure. -/
theorem liftedA_projection
    (hi : Function.Injective i)
    (e : quotientClosure c i ≃* alternatingGroup (Fin 5)) :
    (liftedA c i).map q = quotientClosure c i ∧
      Function.Injective ((q).comp (liftedA c i).subtype) := by
  obtain ⟨s,hs,hr⟩ := closure_section c i hi e
  have hsi : Function.Injective s := by
    intro a b he
    exact (DFunLike.congr_fun hs a).symm.trans
      ((congrArg (closureProjection c i) he).trans (DFunLike.congr_fun hs b))
  have hm : s.range.map (closurePreimage c i).subtype = liftedA c i := by
    rw [hr,Subgroup.map_subtype_commutator]
    rfl
  have hcomp : (q).comp ((closurePreimage c i).subtype.comp s) = (quotientClosure c i).subtype := by
    ext a
    exact congrArg Subtype.val (DFunLike.congr_fun hs a)
  constructor
  · rw [← hm,← MonoidHom.range_comp,← MonoidHom.range_comp,hcomp,range_subtype]
  · intro a b hab
    have ha : a.val ∈ s.range.map (closurePreimage c i).subtype := hm.symm ▸ a.property
    obtain ⟨x,hx,hxa⟩ := ha
    have hb : b.val ∈ s.range.map (closurePreimage c i).subtype := hm.symm ▸ b.property
    obtain ⟨y,hy,hyb⟩ := hb
    obtain ⟨u,rfl⟩ := hx
    obtain ⟨v,rfl⟩ := hy
    have huv : u = v := by
      apply Subtype.ext
      have hu := DFunLike.congr_fun hcomp u
      have hv := DFunLike.congr_fun hcomp v
      change q ((s u).val) = u.val at hu
      change q ((s v).val) = v.val at hv
      change q a.val = q b.val at hab
      rw [← hxa,← hyb] at hab
      change q ((s u).val) = q ((s v).val) at hab
      rw [hu,hv] at hab
      exact hab
    apply Subtype.ext
    exact hxa.symm.trans ((congrArg (fun a => (s a).val) huv).trans hyb)

/-- The original source hypotheses produce an actual normal A₅ in C_G(t),
not merely a projective quotient or an assumed central cover. -/
theorem source_lifted_alternating_five
    (hi : Function.Injective i)
    (z : pointParabolic 1 hn) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    (hnot : ¬ ambientShortCentralizer c i ≤ (i.comp c.right).range) :
    Nonempty (liftedA c i ≃* alternatingGroup (Fin 5)) ∧
      (liftedA c i).map q = quotientClosure c i ∧
      Function.Injective ((q).comp (liftedA c i).subtype) := by
  obtain ⟨e⟩ := source_quotient_normalClosure_alternating_five c i hi z hz hzroot hc hnorm hnot
  exact ⟨liftedA_equiv c i hi e,liftedA_projection c i hi e⟩



/-- Restriction of the original quotient to the actual lifted A₅. -/
def liftedProjection : liftedA c i →* quotientClosure c i :=
  ((QuotientGroup.mk' U).comp (liftedA c i).subtype).codRestrict _ (by
    intro x
    have hx : x.val ∈ closurePreimage c i := commutator_le_left _ _ x.property
    exact hx)

theorem liftedProjection_bijective (hi : Function.Injective i)
    (e : quotientClosure c i ≃* alternatingGroup (Fin 5)) :
    Function.Bijective (liftedProjection c i) := by
  have hp := liftedA_projection c i hi e
  constructor
  · intro x y he
    apply hp.2
    exact congrArg Subtype.val he
  · intro x
    have hx : x.val ∈ (liftedA c i).map q := hp.1.symm ▸ x.property
    obtain ⟨a,ha,he⟩ := hx
    exact ⟨⟨a,ha⟩,Subtype.ext he⟩

/-- The original four-group lifts to a Sylow subgroup of the normal A₅. -/
def liftedSylow (hi : Function.Injective i)
    (e : quotientClosure c i ≃* alternatingGroup (Fin 5)) : Sylow 2 (liftedA c i) :=
  (closureSylow c i hi e).comapOfInjective (liftedProjection c i) (liftedProjection_bijective c i hi e).1
    (by rw [MonoidHom.range_eq_top.mpr (liftedProjection_bijective c i hi e).2]; exact le_top)

theorem liftedSylow_le_eight (hi : Function.Injective i)
    (e : quotientClosure c i ≃* alternatingGroup (Fin 5)) :
    (liftedSylow c i hi e : Subgroup (liftedA c i)).map (liftedA c i).subtype ≤ ambientEight c i := by
  rintro a ⟨x,hx,rfl⟩
  rw [← sourceFour_comap]
  exact hx

end CFSG.Quasithin.ChapterF.UnitaryTwo.ShortRootLift

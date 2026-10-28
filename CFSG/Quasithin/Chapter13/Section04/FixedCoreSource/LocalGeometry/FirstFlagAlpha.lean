module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FirstFlagImages
public import CFSG.Quasithin.ChapterC.Section01.AugmentationSixControl.SylowBaumann
public import Theory.GroupTheory.PerfectCenterFrattini
/-!
# Full-image Baumann decomposition on the original first flag core

The literal central quotient identifies the component centralizer inside
O₂,Z(L). Quasisimplicity puts its image in the Frattini subgroup of L/O₂(L),
discharging the remaining structural hypothesis of B.2.19. The full-kernel
augmentation theorem then gives the alpha decomposition and centralizer
Sylow conclusion on exactly the source R₁.

When the covered Baumann normalizer escapes, the previously constructed
S₆ action supplies both required images. Sylow maximality immediately
gives R₁ ∩ L Baum(R₁) = Baum(R₁). The full characteristic-subgroup/normalizer
bound and covered residual selection remain subsequent source steps;
R₁ has not been identified with O₂(L₁T), and the central three is retained.

Source: Aschbacher--Smith B.2.19, printed pp.81--82;
C.1.37, pp.142--143; 13.2.2(7), pp.877--878.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable Nonsolvable
open ChapterB ChapterB.BaumannArgument
open Section08.TransvectionRecognition.Component.ModelExtension
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal residual of LT is L in either quotient row. -/
theorem firstFlag_product_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V) :
    pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G) =
      L.subgroupOf (L ⊔ (T : Subgroup G)) := by
  let X := L ⊔ (T : Subgroup G)
  let Li := L.subgroupOf X
  let Ti := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let : Li.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hcmp : Li.IsCComponent := h.maximal_faithful.1.1.1
  let : Group.IsPerfect Li := hcmp.perfect
  have hpL : IsPPerfect 2 Li := by
    intro N hn hquot
    let : N.Normal := hn
    by_contra hne
    let : Nontrivial (Li ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (Li ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (Li ⧸ N) := hquot.isNilpotent
    exact Group.IsPerfect.not_isSolvable (Li ⧸ N) inferInstance
  have hprod (x : X) : ∃ l ∈ Li, ∃ t ∈ (Ti : Subgroup X), l*t=x := by
    apply mem_sup_of_normal_left.mp
    rw [Sylow.coe_subtype,←subgroupOf_sup (show L ≤ X from le_sup_left)
      (show (T : Subgroup G) ≤ X from le_sup_right),subgroupOf_self]
    exact mem_top x
  exact pResidual_eq_of_subnormal_product Li (Ti : Subgroup X)
    hcmp.subnormal hpL Ti.isPGroup' hprod

/-- The genuine central quotient puts C_L(V) in O₂,Φ(L), without
removing the covering center. -/
theorem firstFlag_component_centralizer_frattini
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    L ⊓ centralizer (V : Set G) ≤ coreFrattini L := by
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  rintro x ⟨hx,hc⟩
  let l : L := ⟨x,hx⟩
  have he : BinaryPermutation.coreRepresentation (Fin 6)
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val = 1 := by
    apply LinearMap.ext
    intro w
    obtain ⟨v,hv⟩ := m.coordinate.surjective (Multiplicative.ofAdd w)
    have hh := m.equivariant l v
    have hvf : V.normalizerMonoidHom ⟨l.val,D.normalizes l.property⟩ v = v := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hc v.val v.property).symm
    rw [hvf,hv] at hh
    exact hh.symm
  have hp : (m.quotient (QuotientGroup.mk' (centralCore L) l)).val = 1 :=
    BinaryPermutation.SixCoreNormalizer.action_injective (he.trans (map_one _).symm)
  have hq : QuotientGroup.mk' (centralCore L) l = 1 :=
    m.quotient.injective (by rw [map_one];exact Subtype.ext hp)
  have hz : l ∈ centralCore L := (QuotientGroup.eq_one_iff l).mp hq
  exact ⟨l,center_le_frattini_of_isPerfect hz,rfl⟩

/-- The source Frattini hypothesis on the actual LT, transported through
its literal residual identification. -/
theorem firstFlag_product_centralizer_frattini
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    let X := L ⊔ (T : Subgroup G)
    let U := V.subgroupOf X
    pResidual 2 X ⊓ centralizer (U : Set X) ≤ coreFrattini (pResidual 2 X) := by
  let X := L ⊔ (T : Subgroup G)
  let Li := L.subgroupOf X
  let U := V.subgroupOf X
  have hLX : L ≤ X := le_sup_left
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  let ek : Li ≃* L := subgroupOfEquivOfLe hLX
  let eq := QuotientGroup.congr (pCore 2 Li) (pCore 2 L) ek (pCore_map_iso 2 ek)
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let : IsQuasisimple (Li ⧸ pCore 2 Li) := IsQuasisimple.of_mulEquiv eq.symm
  change pResidual 2 X ⊓ centralizer (U : Set X) ≤ coreFrattini (pResidual 2 X)
  rw [firstFlag_product_residual h D]
  rintro x ⟨hx,hc⟩
  have hcG : x.val ∈ centralizer (V : Set G) := by
    intro v hv
    exact congrArg Subtype.val (hc ⟨v,hVX hv⟩ hv)
  have hf := firstFlag_component_centralizer_frattini h D m ⟨hx,hcG⟩
  obtain ⟨l,hl,hlx⟩ := hf
  have hlz : QuotientGroup.mk' (pCore 2 L) l ∈ frattini (L ⧸ pCore 2 L) := hl
  let li : Li := ⟨x,hx⟩
  have he : ek li = l := Subtype.ext hlx.symm
  have hq : eq (QuotientGroup.mk' (pCore 2 Li) li) = QuotientGroup.mk' (pCore 2 L) l := by
    change QuotientGroup.mk' (pCore 2 L) (ek li) = _
    rw [he]
  refine ⟨li,?_,rfl⟩
  change QuotientGroup.mk' (pCore 2 Li) li ∈ frattini (Li ⧸ pCore 2 Li)
  have hm := frattini_le_comap_frattini_of_surjective
    (φ := eq.symm.toMonoidHom) eq.symm.surjective hlz
  change eq.symm (QuotientGroup.mk' (pCore 2 L) l) ∈ frattini (Li ⧸ pCore 2 Li) at hm
  rwa [←hq,eq.symm_apply_apply] at hm


/-- The full-image alpha decomposition on the original R₁, in both
quotient rows. The centralizer conclusion is Sylow, not kernel equality. -/
theorem firstFlagCore_full_baumann_alpha
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd)
    (honto : Function.Surjective q) (a : alternatingGroup (Fin 6))
    (hR : ((firstFlagCore h structural D m).subgroupOf (L ⊔ (T : Subgroup G))).map q =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj a.val).toMonoidHom)
    (hJ : ((elementaryAbelianMaxJ (firstFlagCore h structural D m)).subgroupOf
      (L ⊔ (T : Subgroup G))).map q =
        ((firstFlagCore h structural D m).subgroupOf (L ⊔ (T : Subgroup G))).map q) :
    let R := firstFlagCore h structural D m
    L.pCoreIn 2 ≤ baumann R ∧
      thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (L : Set G)) ⊔
        (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) ∧
      IsSylowSubgroupIn (baumann R ⊓ centralizer (V : Set G))
        ((L ⊔ baumann R) ⊓ centralizer (V : Set G)) := by
  let X := L ⊔ (T : Subgroup G)
  let Li := L.subgroupOf X
  let U := V.subgroupOf X
  let R := firstFlagCore h structural D m
  let Ri := R.subgroupOf X
  have hLX : L ≤ X := le_sup_left
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  have hRT : R ≤ T := map_subtype_le _
  have hRX : R ≤ X := hRT.trans le_sup_right
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.normalizes ((structural G T L h).2.2 V D).1)
  let := D.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVX
  let eu : U ≃* V := subgroupOfEquivOfLe hVX
  let e := eu.trans m.coordinate
  have he (x : X) (v : U) : (e (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd := hq x (eu v)
  obtain ⟨hQR,hRC⟩ := firstFlagCore_kernel h structural D m
  have hVR : U ≤ Ri := comap_mono (D.le_core.trans hQR)
  have hcore : Ri ⊓ centralizer (U : Set X) = pCore 2 X := by
    apply map_injective X.subtype_injective
    rw [←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hVX]
    exact hRC
  have hJmap : (elementaryAbelianMaxJ Ri).map X.subtype = elementaryAbelianMaxJ R := by
    rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hRX]
  have hJi : elementaryAbelianMaxJ Ri = (elementaryAbelianMaxJ R).subgroupOf X := by
    rw [←hJmap]
    ext x
    exact (mem_map_iff_mem X.subtype_injective).symm
  have hb := ChapterC.AugmentationSixControl.conjugate_point_baumann_of_kernel_sylow
    U Ri q honto e he ((T.isPGroup'.to_le hRT).comap_subtype) hVR hcore
    (firstFlagCore_kernel_sylow h structural D m q hq) a hR (hJi.symm ▸ hJ)
    (firstFlag_product_centralizer_frattini h D m)
  rw [firstFlag_product_residual h D] at hb
  have hLm : Li.map X.subtype = L := map_subgroupOf_eq_of_le hLX
  have hBm : (baumann Ri).map X.subtype = baumann R := by
    rw [ChapterC.RankOne.SymmetricSix.baumann_map X X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hRX]
  have ham : (thompsonAlpha Ri).map X.subtype = thompsonAlpha R := by
    unfold thompsonAlpha
    rw [←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hRX]
  refine ⟨?_,?_,?_⟩
  · have hh := map_mono (f := X.subtype) hb.1
    rw [map_pCoreIn_of_injective 2 Li X.subtype X.subtype_injective,hLm,hBm] at hh
    exact hh
  · have hh := congrArg (map X.subtype) hb.2.1
    rw [Subgroup.map_sup,←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      ←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      ham,hLm,map_subgroupOf_eq_of_le hVX,hJmap] at hh
    exact hh
  · have hh := (Chapter1.IsSylowIn.map_iff X.subtype X.subtype_injective).mpr hb.2.2
    rw [←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      ←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      Subgroup.map_sup,hLm,hBm,map_subgroupOf_eq_of_le hVX] at hh
    exact hh

/-- Covered normalizer escape supplies the entire full-image alpha and
Sylow calculation on the original source R₁, without an action callback. -/
theorem covered_firstFlagCore_alpha_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hescape : ¬ normalizer (baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G)) :
    let R := firstFlagCore h structural D m
    L.pCoreIn 2 ≤ baumann R ∧
      thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (L : Set G)) ⊔
        (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) ∧
      IsSylowSubgroupIn (baumann R ⊓ centralizer (V : Set G))
        ((L ⊔ baumann R) ⊓ centralizer (V : Set G)) := by
  obtain ⟨q,hq,hLq,honto,a,hJ,hB,hR⟩ :=
    covered_firstFlagCore_full_image_of_escape h structural D m hc z hz hzL hescape
  exact firstFlagCore_full_baumann_alpha h structural D m q hq honto a hR (hJ.trans hR.symm)


/-- The source Sylow conclusion saturates the intersection with LB on the
same R₁. Odd elements in the full centralizer do not enter this equality. -/
theorem covered_firstFlagCore_product_intersection_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hescape : ¬ normalizer (baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G)) :
    let R := firstFlagCore h structural D m
    R ⊓ (L ⊔ baumann R) = baumann R := by
  obtain ⟨q,hq,_,honto,a,hJ,hB,hR⟩ :=
    covered_firstFlagCore_full_image_of_escape h structural D m hc z hz hzL hescape
  have hs := (firstFlagCore_full_baumann_alpha h structural D m q hq honto a hR
    (hJ.trans hR.symm)).2.2
  let X := L ⊔ (T : Subgroup G)
  let R := firstFlagCore h structural D m
  let B := baumann R
  let J := L ⊔ B
  have hRT : R ≤ T := map_subtype_le _
  have hRX : R ≤ X := hRT.trans le_sup_right
  have hBR : B ≤ R := inf_le_left
  have hBJ : B ≤ J := le_sup_right
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  let U := V.subgroupOf X
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.normalizes ((structural G T L h).2.2 V D).1)
  let eu : U ≃* V := subgroupOfEquivOfLe hVX
  let e := eu.trans m.coordinate
  have he (x : X) (v : U) : (e (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd := hq x (eu v)
  have hk := ChapterB.Offenders.SixCorePoint.kernel_centralizer U q e he
  have hK : (R ⊓ J) ⊓ centralizer (V : Set G) = B ⊓ centralizer (V : Set G) := by
    apply (Chapter1.isSylowIn_iff.mp hs).2.2
    · exact (T.isPGroup'.to_le hRT).to_le (inf_le_left.trans inf_le_left)
    · exact inf_le_inf_right _ (le_inf hBR hBJ)
    · exact inf_le_inf_right _ inf_le_right
  apply le_antisymm ?_ (le_inf hBR hBJ)
  intro r hr
  have hqr : q ⟨r,hRX hr.1⟩ ∈ (B.subgroupOf X).map q := by
    rw [hB,←hR]
    exact mem_map_of_mem q hr.1
  obtain ⟨b,hb,hbr⟩ := hqr
  let x : X := ⟨r,hRX hr.1⟩ * b⁻¹
  have hx : x ∈ q.ker := by
    change q (⟨r,hRX hr.1⟩ * b⁻¹) = 1
    rw [map_mul,map_inv,hbr,mul_inv_cancel]
  have hxc : x.val ∈ centralizer (V : Set G) := by
    rw [hk] at hx
    intro v hv
    exact congrArg Subtype.val (hx ⟨v,hVX hv⟩ hv)
  have hxR : x.val ∈ R := R.mul_mem hr.1 (R.inv_mem (hBR hb))
  have hxJ : x.val ∈ J := J.mul_mem hr.2 (J.inv_mem (hBJ hb))
  have hxB : x.val ∈ B := (hK ▸ show x.val ∈ (R ⊓ J) ⊓ centralizer (V : Set G)
    from ⟨⟨hxR,hxJ⟩,hxc⟩).1
  have hh := B.mul_mem hxB hb
  change (r * b.val⁻¹) * b.val ∈ B at hh
  simpa only [inv_mul_cancel_right] using hh

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry

module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourCenterKernel
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongFixed
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms

/-!
# The original U₄ fixed line and quadratic field image

The specified broad marking identifies the same selected L with the plane
residual and R with the point residual. Transporting the literal left-core
conjugation gives the Hermitian four-space. The center of O₂(R) is central
in R, lies in the common Sylow T∩L and centralizes O₂(L); characteristic
two in L puts it in O₂(L). Both it and the Hermitian Sylow fixed space have
order q, so they are equal as ambient subgroups.

The preceding normalized-Borel argument makes all of the original S fix
this line pointwise. Hermitian scalar rigidity forces the square of every
left-quotient automorphism to be inner. Thus the actual field image has
order at most two. Its exact kernel is S∩(L O₂(LS)), by the original
quotient-action kernel theorem; the resulting index bound retains O₂(LS).
No equality S=T, R=O²(H), or O₂(LS)=O₂(L) is assumed or concluded.

The full extension bound still requires removing the enlargement of the
left join-core. Constructing both full-Borel comparison squares, DGS
exhaustiveness, uniqueness and unconditional GlobalExit remain necessary.
The companion Chapter 12 module applies these results to every original
preparation and selected perfect R, retaining q=4 and both input orientations.

The private Hermitian transport adapts `UnitarySource/AmbientThompson.lean`
and `SingularCenter.lean`; the central-root calculation adapts
`UnitaryFourFactors.lean`. Source: Aschbacher--Smith F.1.12, pp.263--264,
F.4.29, p.289, and 5.2.6--7, pp.650--651 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
local instance originalUnitaryFourFixedFieldAlgebra (m : ℕ) : Algebra (ZMod 2) (fixedField m) :=
  ZMod.algebra _ 2
local instance originalUnitaryFourSpaceModule (m : ℕ) [NeZero m] : Module (ZMod 2) (Space m) :=
  Module.compHom (Space m) (algebraMap (ZMod 2) (fixedField m))
namespace OriginalUnitaryFour.FixedLine
omit [Finite G] in
private theorem core_model (m : ℕ) (hm : 1 ≤ m) [NeZero m] (e : L ≃* L2 m hm) :
    IsConjugationModel L (L.pCoreIn 2) (SL2.BinarySmall.hermitian m) := by
  let targetGroup : Group (L2 m hm) := inferInstance
  let eq := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans (L2QuotientEquivSL2 m hm)
  let ec := (e.subgroupMap (pCore 2 L)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  let ei : pCore 2 L ≃* L.pCoreIn 2 :=
    (pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective
  let f := ei.symm.trans (ec.trans (L2TwoCoreEquiv m hm).symm)
  refine ⟨eq,f,?_⟩
  intro l v
  have hconj : ec (MulAut.conjNormal l (ei.symm v)) =
      MulAut.conjNormal (e l) (ec (ei.symm v)) := by
    apply Subtype.ext
    change e (l * (ei.symm v : L) * l⁻¹) =
      e l * e (ei.symm v : L) * (e l)⁻¹
    exact (e.map_mul _ _).trans (congrArg₂ (· * ·) (e.map_mul _ _)
      (@MulEquiv.map_inv L (L2 m hm) inferInstance (@Group.toDivisionMonoid _ targetGroup) e l))
  have he := L2TwoCoreEquiv_symm_conj m hm (e l) (ec (ei.symm v))
  rw [←hconj] at he
  have hf : f (ei (MulAut.conjNormal l (ei.symm v))) =
      Multiplicative.ofAdd (SL2.BinarySmall.hermitian m
        (eq (QuotientGroup.mk' (pCore 2 L) l)) (f v).toAdd) := by
    change (L2TwoCoreEquiv m hm).symm (ec (ei.symm (ei _))) = _
    rw [ei.symm_apply_apply]
    exact he
  rw [←hf,f.symm_apply_apply]
  have hv : ((ei.symm v : pCore 2 L) : G) = (v : G) :=
    congrArg Subtype.val (ei.apply_symm_apply v)
  change (l : G) * ((ei.symm v : pCore 2 L) : G) * (l : G)⁻¹ = _
  rw [hv]

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
section MatrixCenter
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "R" => radical F σ hσ
local notation "L" => localSU F (form F σ hσ)
local notation "κ" => coordinatesOfRadical F σ hσ

omit [Finite F] in
private theorem center_radical_central (hnt : ∃ u, σ u ≠ u) :
    (center R).map (radical F σ hσ).subtype ≤ center L := by
  rintro x ⟨r,hr,rfl⟩
  obtain ⟨hx,hy⟩ := (mem_center_radical_iff F σ hσ hnt r).mp hr
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  have hmat : r.val.val.val.val = radicalMatrix F σ (κ r) := by
    exact congrArg (fun x : R => x.val.val.val.val)
      ((radicalCoordinatesEquiv F σ hσ).apply_symm_apply r).symm
  have hg := (mem_localSU F _ g.val).mp g.property
  have hl := last_row F σ hσ g.val g.property
  change g.val.val.val * r.val.val.val.val = r.val.val.val.val * g.val.val.val
  rw [hmat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalMatrix, hx,hy, Matrix.mul_apply, Fin.sum_univ_succ,
      hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,hl.2.1,hl.2.2.1,hl.2.2.2,add_comm]


end MatrixCenter

private theorem core_center_transport
    {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hc : (center (pCore 2 X)).map (pCore 2 X).subtype ≤ center X) :
    (center (pCore 2 Y)).map (pCore 2 Y).subtype ≤ center Y := by
  let c := (e.subgroupMap (pCore 2 X)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  rw [←center_map_equiv c,Subgroup.map_map,←center_map_equiv e]
  change (center (pCore 2 X)).map (e.toMonoidHom.comp (pCore 2 X).subtype) ≤ _
  rw [←Subgroup.map_map]
  exact map_mono hc

/-- The point residual centralizes the center of its own two-core. -/
private theorem point_core_center_central (m : ℕ) (hm : 1 ≤ m) :
    (center (pCore 2 (PointLocal.ProjectiveLocal m hm))).map
      (pCore 2 (PointLocal.ProjectiveLocal m hm)).subtype ≤
        center (PointLocal.ProjectiveLocal m hm) := by
  apply core_center_transport (PointLocal.localEquiv m hm)
  rw [←PointLocal.radical_eq_twoCore m hm]
  exact center_radical_central (MatrixField m) (fieldConj m)
    (fieldConj_involutive m hm) (PointLocal.fieldConj_nontrivial m hm)

section FixedSpace
variable (m : ℕ) [NeZero m]
variable (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field m))
  (f : L.pCoreIn 2 ≃* Multiplicative (Space m))
  (hf : ∀ (l : L) (v : L.pCoreIn 2),
    (f.symm (Multiplicative.ofAdd (action m (e (QuotientGroup.mk' (pCore 2 L) l))
      (f v).toAdd)) : G) = (l : G)*(v : G)*(l : G)⁻¹)
include hf
omit [Finite G] in
private theorem core_action_fixed_iff (l : L) (v : L.pCoreIn 2) :
    action m (e (QuotientGroup.mk' (pCore 2 L) l)) (f v).toAdd=(f v).toAdd ↔
      Commute l.val v.val := by
  constructor
  · intro hx
    have hh := hf l v
    rw [hx] at hh
    have he := congrArg Subtype.val (f.symm_apply_apply v)
    exact mul_inv_eq_iff_eq_mul.mp (hh.symm.trans he)
  · intro hx
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    exact (hf l v).trans (by
      rw [hx.eq,mul_inv_cancel_right]
      exact (congrArg Subtype.val (f.symm_apply_apply v)).symm)

private theorem core_sylow_fixed_card (P : Sylow 2 L) :
    Nat.card (L.pCoreIn 2 ⊓ centralizer (((P : Subgroup L).map L.subtype) : Set G) : Subgroup G)=2^m := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := P.mapSurjective hq
  let Q := L.pCoreIn 2
  let J := Q ⊓ centralizer (((P : Subgroup L).map L.subtype) : Set G)
  have hfix (v : Q) : v.val ∈ centralizer (((P : Subgroup L).map L.subtype) : Set G) ↔
      ∀ g ∈ (R : Subgroup _), action m g (f v).toAdd=(f v).toAdd := by
    constructor
    · intro hv g hg
      obtain ⟨l,hl,rfl⟩ := hg
      exact (core_action_fixed_iff m e f hf l v).mpr
        (mem_centralizer_iff.mp hv l.val (mem_map_of_mem L.subtype hl))
    · intro hv
      apply mem_centralizer_iff.mpr
      rintro _ ⟨l,hl,rfl⟩
      exact (core_action_fixed_iff m e f hf l v).mp (hv (q l) ⟨l,hl,rfl⟩)
  let j : J ≃ {X : Space m // ∀ g ∈ (R : Subgroup _), action m g X=X} :=
    { toFun v := ⟨(f ⟨v.val,v.property.1⟩).toAdd,(hfix _).mp v.property.2⟩
      invFun X := ⟨(f.symm (Multiplicative.ofAdd X.val)).val,
        (f.symm (Multiplicative.ofAdd X.val)).property,
        (hfix _).mpr (by rw [f.apply_symm_apply]; exact X.property)⟩
      left_inv v := by
        apply Subtype.ext
        change (f.symm (f ⟨v.val,v.property.1⟩)).val=v.val
        exact congrArg (fun w : Q => w.val) (f.symm_apply_apply _)
      right_inv X := Subtype.ext (congrArg Multiplicative.toAdd (f.apply_symm_apply _)) }
  exact (Nat.card_congr j).trans (Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularFixed.sylow_fixed_card m R)

end FixedSpace
end OriginalUnitaryFour.FixedLine
namespace Preparation
variable (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (mark : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))
include d h hTH hp mark

/-- The original left core has its actual Hermitian conjugation coordinates. -/
theorem original_unitaryFour_hermitian_model [NeZero m] :
    IsConjugationModel L (L.pCoreIn 2) (Representation.SL2.BinarySmall.hermitian m) := by
  obtain ⟨_,⟨a⟩,_,_⟩ := d.original_unitaryFour_factors h hTH hp m hm point mark
  exact OriginalUnitaryFour.FixedLine.core_model m hm a

/-- The center of the selected right two-core is central in that same R. -/
theorem original_unitaryFour_core_center_central :
    (center (pCore 2 R)).map (pCore 2 R).subtype ≤ center R := by
  obtain ⟨_,_,⟨b⟩,_⟩ := d.original_unitaryFour_factors h hTH hp m hm point mark
  exact OriginalUnitaryFour.FixedLine.core_center_transport b.symm
    (OriginalUnitaryFour.FixedLine.point_core_center_central m hm)

/-- The whole Hermitian fixed line is the embedded center of the selected right core. -/
theorem original_unitaryFour_fixed_core_eq_right_core_center :
    L.pCoreIn 2 ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) =
      ((center (pCore 2 R)).map (pCore 2 R).subtype).map R.subtype := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨e,f,hf⟩ := d.original_unitaryFour_hermitian_model h hTH hp m hm point mark
  let S₀ := (T : Subgroup G) ⊓ L
  let Z := ((center (pCore 2 R)).map (pCore 2 R).subtype).map R.subtype
  have hcentral : Z ≤ (center R).map R.subtype :=
    map_mono (d.original_unitaryFour_core_center_central h hTH hp m hm point mark)
  have hS₀ : S₀ = sourceS L H ⊓ R :=
    d.left_intersection.symm.trans (d.original_unitaryFour_intersections h hTH hp m hm point mark)
  have hZcore : Z ≤ R.pCoreIn 2 := map_mono (map_subtype_le _)
  obtain ⟨PR,hPR⟩ := d.sylow 1
  have hZS : Z ≤ S₀ := hZcore.trans ((pCoreIn_le_sylow R PR).trans_eq (hPR.trans hS₀.symm))
  obtain ⟨PL,hPL⟩ := exists_sylow_component h.sylow_normalizes
  have hQS : L.pCoreIn 2 ≤ S₀ := (pCoreIn_le_sylow L PL).trans_eq hPL
  have hZC : Z ≤ centralizer (S₀ : Set G) := by
    rintro z hz s hs
    obtain ⟨k,hk,hkz⟩ := hcentral hz
    rw [←hkz]
    exact congrArg Subtype.val (mem_center_iff.mp hk (⟨s,(hS₀.le hs).2⟩ : R))
  have hchar : L ⊓ centralizer (L.pCoreIn 2 : Set G) ≤ L.pCoreIn 2 :=
    (inf_centralizer_pCoreIn_le_iff 2 L).mpr
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp h.local_mem.2.2.2.1)
  have hZQ : Z ≤ L.pCoreIn 2 :=
    (le_inf (hZS.trans inf_le_right) (hZC.trans (centralizer_le hQS))).trans hchar
  have hcJ : Nat.card (L.pCoreIn 2 ⊓ centralizer (S₀ : Set G) : Subgroup G)=2^m := by
    dsimp only [S₀]
    rw [←hPL]
    exact OriginalUnitaryFour.FixedLine.core_sylow_fixed_card m e f hf PL
  have hcZ : Nat.card Z=2^m := by
    obtain ⟨_,_,⟨b⟩,_⟩ := d.original_unitaryFour_factors h hTH hp m hm point mark
    let bc := (b.subgroupMap (pCore 2 R)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 b))
    rw [card_map_of_injective R.subtype_injective,card_map_of_injective (pCore 2 R).subtype_injective]
    exact (Nat.card_congr (centerCongr bc).toEquiv).trans (PointLocal.projectiveTwoCore_center_card m hm)
  exact (eq_of_le_of_card_ge (le_inf hZQ hZC) (by rw [hcJ,hcZ])).symm


/-- Every original S actor has inner square on the actual left quotient. -/
theorem original_unitaryFour_left_quotient_square_inner (u : sourceS L H) :
    (quotientAut (pCore 2 L)
      (L.normalizerMonoidHom ⟨u.val,
        ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes) u.property⟩))^2 ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨e,f,hf⟩ := d.original_unitaryFour_hermitian_model h hTH hp m hm point mark
  have hfix := d.original_unitaryFour_source_centralizes_center h hTH hp m hm point mark u.property
  have hcentral : ((center (pCore 2 R)).map (pCore 2 R).subtype).map R.subtype ≤
      (center R).map R.subtype :=
    map_mono (d.original_unitaryFour_core_center_central h hTH hp m hm point mark)
  let Q := L.pCoreIn 2
  let a : normalizer (L : Set G) := ⟨u.val,(sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes u.property⟩
  let c := L.normalizerMonoidHom a
  have hN : normalizer (L : Set G) ≤ normalizer (Q : Set G) :=
    normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  let b := Q.normalizerMonoidHom (inclusion hN a)
  let k := f.symm.trans (b.trans f)
  let E : Space m ≃+ Space m :=
    { toFun x := (k (Multiplicative.ofAdd x)).toAdd
      invFun x := (k.symm (Multiplicative.ofAdd x)).toAdd
      left_inv x := congrArg Multiplicative.toAdd (k.symm_apply_apply (Multiplicative.ofAdd x))
      right_inv x := congrArg Multiplicative.toAdd (k.apply_symm_apply (Multiplicative.ofAdd x))
      map_add' x y := congrArg Multiplicative.toAdd (k.map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)) }
  let φ := (MulAut.congr e).toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom)
  let α := φ a
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let coord : Space m → G := fun x => (f.symm (Multiplicative.ofAdd x)).val
  have hcoord : Function.Injective coord :=
    Q.subtype_injective.comp (f.symm.injective.comp Multiplicative.ofAdd.injective)
  have hcoordf (x : Q) : coord (f x).toAdd=x.val :=
    congrArg Subtype.val (f.symm_apply_apply x)
  have hcoordE (x : Space m) : coord (E x)=u.val*coord x*u.val⁻¹ := by
    change (f.symm (f (b (f.symm (Multiplicative.ofAdd x))))).val = _
    rw [f.symm_apply_apply]
    exact normalizerMonoidHom_apply_apply_coe _ _ _
  have hcoordAct (l : L) (x : Space m) :
      coord (action m (q l) x)=l.val*coord x*l.val⁻¹ := by
    have hh := hf l (f.symm (Multiplicative.ofAdd x))
    rw [f.apply_symm_apply] at hh
    exact hh
  have hαq (l : L) : α (q l)=q (c l) := by
    change e ((quotientAut (pCore 2 L) c)
      (e.symm (e (QuotientGroup.mk' (pCore 2 L) l)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hinter (g : Matrix.SpecialLinearGroup (Fin 2) (Field m)) (x : Space m) :
      E (action m g x)=action m (α g) (E x) := by
    obtain ⟨l,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
    change E (action m (q l) x)=action m (α (q l)) (E x)
    apply hcoord
    rw [hcoordE,hcoordAct,hαq,hcoordAct,hcoordE]
    have hcval : (c l).val=u.val*l.val*u.val⁻¹ :=
      normalizerMonoidHom_apply_apply_coe _ _ _
    rw [hcval]
    group
  obtain ⟨P,hP⟩ := exists_sylow_component h.sylow_normalizes
  let S := (T : Subgroup G) ⊓ L
  let Z := ((center (pCore 2 R)).map (pCore 2 R).subtype).map R.subtype
  let Pq := P.mapSurjective (show Function.Surjective q from
    e.surjective.comp (QuotientGroup.mk'_surjective _))
  let U := Representation.invariants ((action m).comp (Pq : Subgroup _).subtype)
  have hR : Z=Q ⊓ centralizer (S : Set G) :=
    (d.original_unitaryFour_fixed_core_eq_right_core_center h hTH hp m hm point mark).symm
  have hcoords (x : Space m) : coord x ∈ Z ↔ x ∈ U := by
    rw [hR]
    constructor
    · intro hx g
      obtain ⟨l,hl,he⟩ := g.property
      change action m g.val x=x
      rw [←he]
      apply hcoord
      rw [hcoordAct]
      have hlS : l.val ∈ S := by
        change l.val ∈ (T : Subgroup G) ⊓ L
        rw [←hP]
        exact mem_map_of_mem L.subtype hl
      exact mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_iff.mp hx.2 l.val hlS)
    · intro hx
      refine ⟨(f.symm (Multiplicative.ofAdd x)).property,mem_centralizer_iff.mpr ?_⟩
      intro l hl
      have hmap : l ∈ (P : Subgroup L).map L.subtype := by
        rw [hP]
        exact hl
      obtain ⟨k,hk,rfl⟩ := hmap
      have hh := congrArg coord (hx (⟨q k,⟨k,hk,rfl⟩⟩ : Pq))
      change coord (action m (q k) x)=coord x at hh
      rw [hcoordAct] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
  let : Nontrivial U := Module.nontrivial_of_finrank_eq_succ
    (Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongFixed.sylow_fixed_finrank m Pq)
  obtain ⟨X,hX⟩ := exists_ne (0 : U)
  have hXne : X.val ≠ 0 := fun hh => hX (Subtype.ext hh)
  have hfixed (a : fixedField m) : E (a • X.val)=a • X.val := by
    apply hcoord
    rw [hcoordE]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hfix _
      (hcentral ((hcoords _).mpr (U.smul_mem a X.property)))).symm
  obtain ⟨g,hg⟩ := Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongFixed.square_inner_of_fixed_line
    m α E hinter X.val hXne hfixed
  have hmapped : (MulAut.congr e) ((quotientAut (pCore 2 L) c)^2) ∈
      MulAut.innerSubgroup (Matrix.SpecialLinearGroup (Fin 2) (Field m)) := by
    rw [map_pow]
    exact ⟨g,hg.symm⟩
  rw [←MulAut.map_innerSubgroup_congr e] at hmapped
  exact (mem_map_iff_mem (MulAut.congr e).injective).mp hmapped

/-- The literal field action of the original S on a marked left quotient. -/
@[expose] def originalUnitaryFourLeftFieldAction
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F) : sourceS L H →* (F ≃+* F) :=
  (Theory.PSL2.fieldProjection F).comp ((MulAut.congr q).toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp
      (inclusion ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes)))))

/-- Every original S field coefficient has square one in any specified PSL₂ coordinates. -/
theorem original_unitaryFour_left_field_square
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F) (u : sourceS L H) :
    (originalUnitaryFourLeftFieldAction h hTH q u)^2=1 := by
  obtain ⟨g,hg⟩ := d.original_unitaryFour_left_quotient_square_inner h hTH hp m hm point mark u
  let c := L.normalizerMonoidHom ⟨u.val,
    ((sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes) u.property⟩
  change (Theory.PSL2.fieldProjection F ((MulAut.congr q) (quotientAut (pCore 2 L) c)))^2=1
  rw [←map_pow,←map_pow,←hg,MulAut.congr_conj]
  apply MonoidHom.mem_ker.mp
  rw [Theory.PSL2.fieldProjection_ker]
  exact ⟨q g,rfl⟩

/-- The original left-quotient field image has degree at most two. -/
theorem original_unitaryFour_left_field_card_le_two
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F) :
    Nat.card (originalUnitaryFourLeftFieldAction h hTH q).range ≤ 2 := by
  classical
  let ψ := originalUnitaryFourLeftFieldAction h hTH q
  let I := ψ.range
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  let := Fintype.ofFinite I
  have hsquare (x : I) : x^2=1 := by
    obtain ⟨a,ha⟩ := x.property
    apply Subtype.ext
    change x.val^2=1
    rw [←ha]
    exact d.original_unitaryFour_left_field_square h hTH hp m hm point mark q a
  have hb := IsCyclic.card_pow_eq_one_le (α := I) (n := 2) (by decide)
  have he : (Finset.univ.filter (fun a : I => a^2=1))=Finset.univ := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hsquare]
  rw [he,Finset.card_univ] at hb
  simpa only [Nat.card_eq_fintype_card] using hb

omit d hp m hm point mark in
include h hTH in
/-- The field kernel retains the entire original left join-core. The
remaining extension bound must still remove any enlargement of that core. -/
theorem original_unitaryFour_left_field_kernel
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F) :
    (originalUnitaryFourLeftFieldAction h hTH q).ker =
      (L ⊔ (L ⊔ sourceS L H).pCoreIn 2).subgroupOf (sourceS L H) := by
  let S := sourceS L H
  let M := L ⊔ S
  have hn : S ≤ normalizer (L : Set G) :=
    (sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes
  let f := pCoreJoinAction 2 hn
  let I := MulAut.innerSubgroup (L ⧸ pCore 2 L)
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply map_injective (f := q.toMonoidHom) q.injective
    rw [center_map_equiv,Subgroup.map_bot]
    apply bot_unique
    intro x hx
    apply Theory.PSL2.psl2_conj_eq_one_implies x
    ext y
    change x*y*x⁻¹=y
    rw [←mem_center_iff.mp hx y,mul_inv_cancel_right]
  have hk : f.ker=pCore 2 M := pCoreJoinAction_kernel 2 hn
    (pCore_isPGroup.map _) hz
  have hi (a : MulAut (L ⧸ pCore 2 L)) :
      MulAut.congr q a ∈ Theory.PSL2.inner F ↔ a ∈ I := by
    change MulAut.congr q a ∈ MulAut.innerSubgroup (Theory.PSL2.Group F) ↔ _
    rw [←MulAut.map_innerSubgroup_congr q]
    exact mem_map_iff_mem (MulAut.congr q).injective
  have hpre (x : M) : f x ∈ I ↔ x.val ∈ L ⊔ M.pCoreIn 2 := by
    constructor
    · rintro ⟨z,hzinner⟩
      obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
      have he : f (inclusion le_sup_left l)=f x :=
        (pCoreJoinAction_on_component 2 hn l).trans hzinner
      have hx : x*(inclusion le_sup_left l)⁻¹ ∈ f.ker := by
        change f (x*(inclusion le_sup_left l)⁻¹)=1
        rw [map_mul,map_inv,he,mul_inv_cancel]
      rw [hk] at hx
      have hxc : x.val*l.val⁻¹ ∈ M.pCoreIn 2 := mem_map_of_mem M.subtype hx
      have hh := (L ⊔ M.pCoreIn 2).mul_mem (mem_sup_right hxc) (mem_sup_left l.property)
      simpa only [inv_mul_cancel_right] using hh
    · intro hx
      let D := (I.comap f).map M.subtype
      have hLD : L ≤ D := by
        intro l hl
        refine ⟨inclusion le_sup_left (⟨l,hl⟩ : L),?_,rfl⟩
        change f (inclusion le_sup_left (⟨l,hl⟩ : L)) ∈ I
        rw [pCoreJoinAction_on_component]
        exact ⟨_,rfl⟩
      have hQD : M.pCoreIn 2 ≤ D := by
        rintro _ ⟨y,hy,rfl⟩
        refine ⟨y,?_,rfl⟩
        change f y ∈ I
        rw [MonoidHom.mem_ker.mp (hk.symm ▸ hy)]
        exact I.one_mem
      exact (mem_map_iff_mem M.subtype_injective).mp ((sup_le hLD hQD) hx)
  ext s
  change Theory.PSL2.fieldProjection F ((MulAut.congr q)
    (f (inclusion le_sup_right s)))=1 ↔ s.val ∈ L ⊔ M.pCoreIn 2
  rw [←MonoidHom.mem_ker,Theory.PSL2.fieldProjection_ker,hi,hpre]
  rfl

/-- The original S has index at most two over its inner part together
with the actual left join-core; the latter is not silently discarded. -/
theorem original_unitaryFour_left_core_quotient_index_le_two :
    (L ⊔ (L ⊔ sourceS L H).pCoreIn 2).relIndex (sourceS L H) ≤ 2 := by
  obtain ⟨F,_,_,hF,⟨q⟩⟩ := h.linear
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  change ((L ⊔ (L ⊔ sourceS L H).pCoreIn 2).subgroupOf (sourceS L H)).index ≤ 2
  rw [←original_unitaryFour_left_field_kernel h hTH q,index_ker]
  exact d.original_unitaryFour_left_field_card_le_two h hTH hp m hm point mark q

end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

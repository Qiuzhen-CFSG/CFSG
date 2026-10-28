module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FixedSylowGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Nonfusion
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularFixed

/-!
# Long-root invariance for the full represented U₅(4) fixed Sylow

The binary PSL₂ quotient makes the derived group of S lie in the plane
core. Consequently Z(C_T(t))∩C_T(t)′ lies in the original plane-core center.
A noncentral involution in the actual Sp₄ unipotent group shows that C_S(t)
cannot lie in the plane core, whose involutions are all central.

The Hermitian fixed line of the whole inner Sylow is exactly the original
long-root group, by containment and its order four. A noncore element of
C_S(t) detects that line among singular vectors. Ambient Hermitian nonfusion
therefore preserves its intersection with the characteristic derived center.
The proved nontrivial intersection and TI property put the full normalizer
of C_T(t) inside N_G(O²(H)), without discarding any outer actors.

Source: Aschbacher--Smith F.4.35,37, printed pp.292--293 of refs/quasithin.pdf.
The local saturation still has to be transported to obtain ambient Sylow
placement. Both F.4.42 applications and same-extension completion remain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive.Descent Theory.SpecificGroups.UnitaryFive.GraphFixed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
open Representation.OrthogonalFourMinus.FiniteModel
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularFixed
namespace UnitaryFiveFixedRoot
variable {Vcore : Subgroup G}
variable (m : ℕ) [NeZero m]
variable (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field m))
  (f : Vcore ≃* Multiplicative (Space m))
  (hf : ∀ (l : L) (v : Vcore),
    (f.symm (Multiplicative.ofAdd (action m (e (QuotientGroup.mk' (pCore 2 L) l))
      (f v).toAdd)) : G) = (l : G)*(v : G)*(l : G)⁻¹)

include hf
omit [Finite G] in
private theorem core_action_fixed_iff (l : L) (v : Vcore) :
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
    Nat.card (Vcore ⊓ centralizer (((P : Subgroup L).map L.subtype) : Set G) : Subgroup G)=2^m := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := P.mapSurjective hq
  let Q := Vcore
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
  exact (Nat.card_congr j).trans (sylow_fixed_card m R)

private theorem singular_fixed_inner_iff (P : Sylow 2 L)
    (u : P) (hu : u.val ∉ pCore 2 L) (z : Vcore)
    (hz : Commute u.val.val z.val) :
    form m (f z).toAdd=0 ↔
      z.val ∈ centralizer (((P : Subgroup L).map L.subtype) : Set G) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := P.mapSurjective hq
  let a : R := ⟨q u.val,⟨u.val,u.property,rfl⟩⟩
  have ha : a.val ≠ 1 := by
    intro hh
    apply hu
    apply (QuotientGroup.eq_one_iff (N := pCore 2 L) _).mp
    exact e.injective (hh.trans e.map_one.symm)
  have hfixed := (core_action_fixed_iff m e f hf u.val z).mpr hz
  rw [singular_fixed_member_iff m R a ha (f z).toAdd hfixed]
  constructor
  · intro hs
    apply mem_centralizer_iff.mpr
    rintro _ ⟨l,hl,rfl⟩
    exact (core_action_fixed_iff m e f hf l z).mp (hs (q l) ⟨l,hl,rfl⟩)
  · intro hs g hg
    obtain ⟨l,hl,rfl⟩ := hg
    exact (core_action_fixed_iff m e f hf l z).mpr
      (mem_centralizer_iff.mp hs l.val (mem_map_of_mem L.subtype hl))
end UnitaryFiveFixedRoot

variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
include d h hH hp hc

theorem Preparation.unitaryFive_sourceS_derived_le_plane_core :
    (_root_.commutator (sourceS L H)).map (sourceS L H).subtype ≤ L.pCoreIn 2 := by
  obtain ⟨K,_,_,hK,⟨e⟩⟩ := h.linear
  obtain ⟨P,hP⟩ := exists_sylow_component h.sylow_normalizes
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hq
  obtain ⟨a⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hK Q
  let : IsMulCommutative Q := ⟨⟨fun x y => a.symm.injective (by
    simp only [map_mul]
    exact mul_comm _ _)⟩⟩
  let : CommGroup Q := IsMulCommutative.instCommGroup
  let f : P →* Q := (q.comp (P : Subgroup L).subtype).codRestrict Q
    (fun x => ⟨x.val,x.property,rfl⟩)
  have hder : (_root_.commutator P).map (P : Subgroup L).subtype ≤ pCore 2 L := by
    rintro _ ⟨x,hx,rfl⟩
    apply (QuotientGroup.eq_one_iff (N := pCore 2 L) x.val).mp
    apply e.injective
    have hh := congrArg (fun y : Q => y.val) (Abelianization.commutator_subset_ker f hx)
    exact hh.trans e.map_one.symm
  rw [map_subtype_commutator] at hder
  have hm := map_mono (f := L.subtype) hder
  rw [map_commutator,hP] at hm
  rw [map_subtype_commutator,d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc]
  exact hm

theorem Preparation.unitaryFive_represented_fixed_core_geometry
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
      r.extension.amalgam.reverse)
    (P : Sylow 2 r.extension.middle)
    (hinner : (P : Subgroup r.extension.middle) ⊓
      (inner U.Carrier).comap r.extension.middle.subtype =
      ((sourceS L H).subgroupOf (normalizer (L : Set G) ⊓ normalizer (residual H : Set G))).map
        F.middle.toMonoidHom)
    (t : ↥(normalizer (L : Set G) ⊓ normalizer (residual H : Set G)))
    (ht : orderOf t=2) (u : U.form.unitarySubgroup)
    (hf : (F.middle t).val=unitaryConj U.form u*projectiveAut U.form U.matrix)
    (hsat : let j := inclusion (inf_le_left.trans r.extension.left_le :
        r.extension.middle ≤ r.extension.carrier)
      ∃ R : Sylow 2 (r.extension.baseHom.range ⊓
          centralizer ({j (F.middle t)} : Set r.extension.carrier) : Subgroup r.extension.carrier),
        (R : Subgroup _).map (r.extension.baseHom.range ⊓
          centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
          ((P : Subgroup r.extension.middle).map j) ⊓
            (r.extension.baseHom.range ⊓ centralizer ({j (F.middle t)} : Set r.extension.carrier))) :
    let I := sourceS L H ⊓ centralizer ({t.val} : Set G)
    let Q := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
    let Z := (center Q ⊓ _root_.commutator Q).map Q.subtype
    Z ≤ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧ ¬ I ≤ L.pCoreIn 2 := by
  let I := sourceS L H ⊓ centralizer ({t.val} : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
  let Z := (center Q ⊓ _root_.commutator Q).map Q.subtype
  have hfixed := d.unitaryFive_represented_fixed_derived_center h hH hp U hc
    r F P hinner t ht u hf hsat
  have hZI : Z ≤ (center I).map I.subtype := hfixed.2.2.2.2.2.2.1
  have hZcore : Z ≤ L.pCoreIn 2 := by
    rw [←hfixed.1,map_subtype_commutator] at hZI
    have hS := d.unitaryFive_sourceS_derived_le_plane_core h hH hp U hc
    rw [map_subtype_commutator] at hS
    exact hZI.trans ((commutator_mono inf_le_left inf_le_left).trans hS)
  refine ⟨d.unitaryFive_plane_core_elementary_le_center h hH hp U hc Z hZcore
    hfixed.2.2.2.2.1,?_⟩
  intro hIC
  obtain ⟨e⟩ := Preparation.unitaryFive_represented_inner_sylow_equiv
    h hH U r F P hinner t ht u hf hsat
  let v := Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element
    (1 : FixedBy.subfield U.F U.form.conj) 0 0 0
  have hv2 : v^2=1 := by
    rw [Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_square]
    simpa only [mul_zero,Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.theta] using
      (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_zero
        (F := FixedBy.subfield U.F U.form.conj))
  let x := e.symm v
  have hx2 : x^2=1 := by
    change (e.symm v)^2=1
    rw [←map_pow,hv2,map_one]
  let y : L.pCoreIn 2 := ⟨x.val,hIC x.property⟩
  have hy2 : y^2=1 := Subtype.ext (congrArg (fun a : I => a.val) hx2)
  have hyc := ((d.unitaryFive_plane_core_structure h hH hp U hc).2.2.2.2 y).mp hy2
  have hxc : x ∈ center I := mem_center_iff.mpr (fun a => Subtype.ext
    (congrArg (fun b : L.pCoreIn 2 => b.val)
      (mem_center_iff.mp hyc ⟨a.val,hIC a.property⟩)))
  have hvc : v ∈ center (Theory.SpecificGroups.SymplecticFour.unipotent
      (F := FixedBy.subfield U.F U.form.conj)) := by
    have hc' : e x ∈ center (Theory.SpecificGroups.SymplecticFour.unipotent
        (F := FixedBy.subfield U.F U.form.conj)) := (centerCongr e ⟨x,hxc⟩).property
    simpa only [x,e.apply_symm_apply] using hc'
  have hbad := (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.mem_center_iff_coordinates
    (1 : FixedBy.subfield U.F U.form.conj) 0 0 0).mp hvc
  exact one_ne_zero hbad.1

theorem Preparation.unitaryFive_inner_fixed_plane_center_eq_right_center :
    (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ⊓
      centralizer (sourceS L H : Set G) = (center (residual H)).map (residual H).subtype := by
  let Vcore := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
  let R := (center (residual H)).map (residual H).subtype
  have hS := d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc
  have hSL : sourceS L H ≤ L := hS ▸ inf_le_right
  have hcoreT : L.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 L).le_sylow_of_normalized T
      (h.sylow_normalizes.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hVS : Vcore ≤ sourceS L H := by
    rw [hS]
    exact (map_subtype_le _).trans (le_inf hcoreT (pCoreIn_le 2 L))
  obtain ⟨hR,_,_⟩ := d.unitaryFive_long_root_center_sourceS h hH hp U hc
  have hRS : R ≤ sourceS L H := hR.trans (map_subtype_le _)
  have hRC : R ≤ centralizer (sourceS L H : Set G) := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := hR hz
    exact mem_centralizer_iff.mpr (fun s hs =>
      congrArg (fun a : sourceS L H => a.val) (mem_center_iff.mp hx ⟨s,hs⟩))
  have hRcore : R ≤ L.pCoreIn 2 := by
    rw [←d.unitaryFive_plane_center_centralizer h hH hp U hc]
    exact le_inf (hRS.trans hSL) (hRC.trans (centralizer_le hVS))
  have hRV : R ≤ Vcore := d.unitaryFive_plane_core_elementary_le_center
    h hH hp U hc R hRcore (d.unitaryFive_right_center_fusion h hH hp U hc).1
  have hRJ : R ≤ Vcore ⊓ centralizer (sourceS L H : Set G) := le_inf hRV hRC
  obtain ⟨e,f,hf⟩ := d.unitaryFive_plane_center_hermitian_model h hH hp U hc
  obtain ⟨P,hP⟩ := exists_sylow_component h.sylow_normalizes
  have hcard : Nat.card (Vcore ⊓ centralizer (sourceS L H : Set G) : Subgroup G)=4 := by
    rw [hS,←hP]
    exact UnitaryFiveFixedRoot.core_sylow_fixed_card 2 e f hf P
  have hcardR : Nat.card R=4 := by
    change Nat.card ((center (residual H)).map (residual H).subtype)=4
    rw [card_map_of_injective (residual H).subtype_injective]
    exact d.unitaryFive_right_center_card h hH hp U hc
  exact (eq_of_le_of_card_ge hRJ (by rw [hcard,hcardR])).symm

theorem Preparation.unitaryFive_singular_fixed_iff_right_center
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field 2))
    (f : (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ≃* Multiplicative (Space 2))
    (hf : ∀ (l : L) (v : (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype),
      (f.symm (Multiplicative.ofAdd (action 2 (e (QuotientGroup.mk' (pCore 2 L) l))
        (f v).toAdd)) : G) = (l : G)*(v : G)*(l : G)⁻¹)
    (u : G) (hu : u ∈ sourceS L H) (huQ : u ∉ L.pCoreIn 2)
    (z : (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype) (hz : Commute u z.val) :
    form 2 (f z).toAdd=0 ↔ z.val ∈ (center (residual H)).map (residual H).subtype := by
  have hS := d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc
  have hu' : u ∈ (T : Subgroup G) ⊓ L := hS ▸ hu
  obtain ⟨P,hP⟩ := exists_sylow_component h.sylow_normalizes
  have huP : (⟨u,hu'.2⟩ : L) ∈ (P : Subgroup L) := by
    have hum : u ∈ (P : Subgroup L).map L.subtype := hP.symm ▸ hu'
    exact (mem_map_iff_mem L.subtype_injective).mp hum
  have huPcore : (⟨u,hu'.2⟩ : L) ∉ pCore 2 L :=
    fun hh => huQ (mem_map_of_mem L.subtype hh)
  have hh := UnitaryFiveFixedRoot.singular_fixed_inner_iff 2 e f hf P
    ⟨⟨u,hu'.2⟩,huP⟩ huPcore z hz
  rw [hP,←hS] at hh
  rw [←d.unitaryFive_inner_fixed_plane_center_eq_right_center h hH hp U hc,mem_inf]
  exact hh.trans (and_iff_right z.property).symm

theorem Preparation.unitaryFive_long_intersection_normalizer
    (Z : Subgroup G) (hZV : Z ≤ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
    (u : G) (hu : u ∈ sourceS L H) (huQ : u ∉ L.pCoreIn 2)
    (huZ : u ∈ centralizer (Z : Set G)) :
    normalizer (Z : Set G) ≤
      normalizer ((Z ⊓ (center (residual H)).map (residual H).subtype : Subgroup G) : Set G) := by
  obtain ⟨e,f,hf,hfusion⟩ := d.unitaryFive_hermitian_fusion h hH hp U hc
  have hroot (z : G) (hz : z ∈ Z) :
      form 2 (f ⟨z,hZV hz⟩).toAdd=0 ↔
        z ∈ (center (residual H)).map (residual H).subtype :=
    d.unitaryFive_singular_fixed_iff_right_center h hH hp U hc e f hf u hu huQ
      ⟨z,hZV hz⟩ (mem_centralizer_iff.mp huZ z hz).symm
  have hinv (g : G) (hg : g ∈ normalizer (Z : Set G))
      (z : G) (hz : z ∈ Z ⊓ (center (residual H)).map (residual H).subtype) :
      g*z*g⁻¹ ∈ Z ⊓ (center (residual H)).map (residual H).subtype := by
    have hz' := (mem_normalizer_iff.mp hg z).mp hz.1
    refine ⟨hz',(hroot _ hz').mp ?_⟩
    apply (hfusion ⟨z,hZV hz.1⟩ ⟨g*z*g⁻¹,hZV hz'⟩ ?_).mp
      ((hroot z hz.1).mpr hz.2)
    exact isConj_iff.mpr ⟨g,rfl⟩
  intro g hg
  apply mem_normalizer_iff.mpr
  intro z
  constructor
  · exact hinv g hg z
  · intro hz
    have hh := hinv g⁻¹ ((normalizer (Z : Set G)).inv_mem hg) _ hz
    simpa only [inv_inv,inv_mul_cancel_left,mul_inv_cancel_right,mul_assoc,inv_mul_cancel,mul_one] using hh

theorem Preparation.unitaryFive_represented_fixed_normalizer_le_right
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
      r.extension.amalgam.reverse)
    (P : Sylow 2 r.extension.middle)
    (hinner : (P : Subgroup r.extension.middle) ⊓
      (inner U.Carrier).comap r.extension.middle.subtype =
      ((sourceS L H).subgroupOf (normalizer (L : Set G) ⊓ normalizer (residual H : Set G))).map
        F.middle.toMonoidHom)
    (t : ↥(normalizer (L : Set G) ⊓ normalizer (residual H : Set G)))
    (htT : t.val ∈ (T : Subgroup G))
    (ht : orderOf t=2) (u : U.form.unitarySubgroup)
    (hf : (F.middle t).val=unitaryConj U.form u*projectiveAut U.form U.matrix)
    (hsat : let j := inclusion (inf_le_left.trans r.extension.left_le :
        r.extension.middle ≤ r.extension.carrier)
      ∃ R : Sylow 2 (r.extension.baseHom.range ⊓
          centralizer ({j (F.middle t)} : Set r.extension.carrier) : Subgroup r.extension.carrier),
        (R : Subgroup _).map (r.extension.baseHom.range ⊓
          centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
          ((P : Subgroup r.extension.middle).map j) ⊓
            (r.extension.baseHom.range ⊓ centralizer ({j (F.middle t)} : Set r.extension.carrier))) :
    normalizer (((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) : Set G) ≤
      normalizer (residual H : Set G) := by
  let I := sourceS L H ⊓ centralizer ({t.val} : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
  let Z := (center Q ⊓ _root_.commutator Q).map Q.subtype
  have hgeo := d.unitaryFive_represented_fixed_core_geometry h hH hp U hc
    r F P hinner t ht u hf hsat
  obtain ⟨v,hv,hvQ⟩ := SetLike.not_le_iff_exists.mp hgeo.2
  have hvZ : v ∈ centralizer (Z : Set G) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨z,hz,rfl⟩
    exact congrArg Subtype.val
      ((mem_center_iff.mp hz.1 (⟨v,sourceS_le_sylow h.sylow_normalizes hH.1.1.2 hv.1,hv.2⟩ : Q)).symm)
  have hNZ := normalizer_le_normalizer_characteristic_image Q (center Q ⊓ _root_.commutator Q)
  have hNR := d.unitaryFive_long_intersection_normalizer h hH hp U hc Z hgeo.1 v hv.1 hvQ hvZ
  have hne := d.unitaryFive_represented_fixed_derived_meets_root h hH hp U hc
    r F P hinner t htT ht u hf hsat
  obtain ⟨_,hti,heq⟩ := d.unitaryFive_right_center_fusion h hH hp U hc
  exact (hNZ.trans hNR).trans ((hti.normalizer_le_of_ne_bot hne inf_le_right).trans_eq heq)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

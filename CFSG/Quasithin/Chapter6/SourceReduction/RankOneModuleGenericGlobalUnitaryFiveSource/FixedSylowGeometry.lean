module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.FixedSylowStructure
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraphCenter
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.AmbientClasses
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# The characteristic root subgroup of the full fixed Sylow in U₅(4)

Inner saturation transports C_S(t) to the actual symplectic unipotent group
at q=4. Its derived subgroup is its elementary center, of order sixteen.
The original cyclic field quotient puts the derived subgroup of C_T(t) in S,
so its intersection with its center is a nontrivial elementary subgroup of
that sixteen-element center, preserved by the full ambient normalizer.

The original long-root group R=Z(O²(H)) is central in S and normalized by T.
A nonidentity point of R in Z(T) belongs to the center of C_S(t), hence to its
derived subgroup and to Z(C_T(t))∩C_T(t)′. This proves the nontrivial long-root
intersection while retaining every outer actor in C_T(t).

Source: Aschbacher--Smith F.4.37(4), printed p.293 of refs/quasithin.pdf.
Invariance of the long-root intersection and ambient Sylow placement remain
separate steps; no equality S=T or source completion is asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive.Descent Theory.SpecificGroups.UnitaryFive.GraphFixed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
private theorem fixed_derived_meets_normal_root
    (S R : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hRS : R ≤ S) (hn : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hR : R ≠ ⊥) (t : G) (ht : t ∈ (T : Subgroup G))
    (hderived : _root_.commutator (S ⊓ centralizer ({t} : Set G) : Subgroup G) =
      center (S ⊓ centralizer ({t} : Set G) : Subgroup G)) :
    let Q := (T : Subgroup G) ⊓ centralizer ({t} : Set G)
    ((center Q ⊓ _root_.commutator Q).map Q.subtype) ⊓ R ≠ ⊥ := by
  let I := S ⊓ centralizer ({t} : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer ({t} : Set G)
  have hRT := hRS.trans hST
  let RT := R.subgroupOf (T : Subgroup G)
  let : RT.Normal := normal_subgroupOf_of_le_normalizer hn
  have hRTne : RT ≠ ⊥ := by
    intro he
    have hm := congrArg (fun B : Subgroup T => B.map (T : Subgroup G).subtype) he
    rw [map_subgroupOf_eq_of_le hRT,Subgroup.map_bot] at hm
    exact hR hm
  let : Nontrivial RT := (nontrivial_iff_ne_bot RT).mpr hRTne
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨x,hx,hxc⟩ := exists_nontrivial_center_mem_normal (p := 2) RT
  let z : G := x.val.val
  have hzR : z ∈ R := x.property
  have hzT : z ∈ (T : Subgroup G) := x.val.property
  have hzc (y : G) (hy : y ∈ (T : Subgroup G)) : y*z=z*y :=
    congrArg (fun a : T => a.val) (mem_center_iff.mp hxc ⟨y,hy⟩)
  have hzt : z ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hzc t ht).symm
  have hzI : z ∈ I := ⟨hRS hzR,hzt⟩
  have hzQ : z ∈ Q := ⟨hzT,hzt⟩
  have hzIc : (⟨z,hzI⟩ : I) ∈ center I := mem_center_iff.mpr (fun i =>
    Subtype.ext (hzc i.val (hST i.property.1)))
  have hzQc : (⟨z,hzQ⟩ : Q) ∈ center Q := mem_center_iff.mpr (fun q =>
    Subtype.ext (hzc q.val q.property.1))
  have hIQ : I ≤ Q := inf_le_inf_right _ hST
  have hm : (_root_.commutator I).map I.subtype ≤ (_root_.commutator Q).map Q.subtype := by
    rw [map_subtype_commutator,map_subtype_commutator]
    exact commutator_mono hIQ hIQ
  have hzder : z ∈ (_root_.commutator Q).map Q.subtype :=
    hm ⟨⟨z,hzI⟩,hderived.symm ▸ hzIc,rfl⟩
  obtain ⟨q,hq,hqz⟩ := hzder
  have hqeq : q = ⟨z,hzQ⟩ := Subtype.ext hqz
  rw [hqeq] at hq
  change ((center Q ⊓ _root_.commutator Q).map Q.subtype) ⊓ R ≠ ⊥
  intro he
  have hmem : z ∈ ((center Q ⊓ _root_.commutator Q).map Q.subtype) ⊓ R :=
    ⟨⟨⟨z,hzQ⟩,⟨hzQc,hq⟩,rfl⟩,hzR⟩
  rw [he,mem_bot] at hmem
  exact hx (Subtype.ext (Subtype.ext hmem))

variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
include d h hH hp hc

omit d hp hc in
theorem Preparation.unitaryFive_represented_inner_sylow_equiv
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
    Nonempty ((sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≃*
      Theory.SpecificGroups.SymplecticFour.unipotent (F := FixedBy.subfield U.F U.form.conj)) := by
  let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  have hTD : (T : Subgroup G) ≤ D :=
    le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
  have hSD := (sourceS_le_sylow h.sylow_normalizes hH.1.1.2).trans hTD
  have he : (sourceS L H ⊓ centralizer ({t.val} : Set G)).subgroupOf D =
      (sourceS L H).subgroupOf D ⊓ centralizer ({t} : Set D) := by
    ext x
    change (x.val ∈ sourceS L H ∧ x.val ∈ centralizer ({t.val} : Set G)) ↔
      (x.val ∈ sourceS L H ∧ x ∈ centralizer ({t} : Set D))
    simp only [mem_centralizer_singleton_iff,Subtype.ext_iff,Subgroup.coe_mul]
  obtain ⟨e⟩ := five_represented_inner_sylow_equiv U r.extension F.middle _ P hinner t
    (by rw [←ht]; exact pow_orderOf_eq_one t) u hf hsat
  exact ⟨((subgroupOfEquivOfLe (inf_le_left.trans hSD :
    sourceS L H ⊓ centralizer ({t.val} : Set G) ≤ D)).symm.trans
      (MulEquiv.subgroupCongr he)).trans e⟩

/-- The original field-action kernel contains the derived group of the full T. -/
theorem Preparation.unitaryFive_sylow_commutator_le_sourceS :
    (_root_.commutator T).map (T : Subgroup G).subtype ≤ sourceS L H := by
  obtain ⟨K,_,_,hK,⟨e⟩⟩ := h.linear
  let := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let : IsCyclic (K ≃+* K) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : CommGroup (K ≃+* K) := IsCyclic.commGroup
  rintro _ ⟨x,hx,rfl⟩
  have hh := Abelianization.commutator_subset_ker
    (unitaryFiveSylowFieldAction h.sylow_normalizes e) hx
  rw [d.unitaryFive_sylow_field_kernel h hH hp U hc e] at hh
  exact hh

/-- The original long-root group is central in S and normalized by T.
The residual index is odd; no formula for an outer actor is needed here. -/
theorem Preparation.unitaryFive_long_root_center_sourceS :
    let R := (center (residual H)).map (residual H).subtype
    R ≤ (center (sourceS L H)).map (sourceS L H).subtype ∧
      (T : Subgroup G) ≤ normalizer (R : Set G) ∧ R ≠ ⊥ := by
  let R := (center (residual H)).map (residual H).subtype
  have hSK : sourceS L H ≤ residual H := by
    rcases hc with ho | hr
    · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U ho).elim
    obtain ⟨e⟩ := hr
    let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
    have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
    have hb := IsPGroup.le_normal_of_index_primeTo U.leftLocal
      (((sourceS L H).subgroupOf P).map e.right.toMonoidHom)
      (((pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype).map e.right.toMonoidHom)
      (by rw [U.leftLocal_index_eq_three]; decide)
    have heq : U.leftLocal = solvableResidual U.leftParabolic := rfl
    rw [heq, ← map_solvableResidual_eq e.right.toMonoidHom e.right.surjective,
      map_le_map_iff_of_injective e.right.injective] at hb
    have hm := map_mono (f := P.subtype) hb
    rw [map_subgroupOf_eq_of_le hSP] at hm
    exact hm.trans_eq (d.parabolic_residuals h hH.1.1.2 hp 1)
  have hnorm : H ≤ normalizer (R : Set G) :=
    (le_normalizer_residual H).trans
      (normalizer_le_normalizer_characteristic_image (residual H) (center (residual H)))
  have hTR := hH.1.1.2.trans hnorm
  let : IsElementaryAbelian 2 R := (d.unitaryFive_right_center_fusion h hH hp U hc).1
  have hRp : IsPGroup 2 R := IsElementaryAbelian.isPGroup (p := 2) (G := R)
  have hRT : R ≤ (T : Subgroup G) := hRp.le_sylow_of_normalized T hTR
  have hRI : R ≤ intersection L H := hRT.trans (le_inf h.sylow_normalizes hH.1.1.2)
  have hRS : R ≤ sourceS L H :=
    le_pCoreIn_of_normalizes hRp hRI (inf_le_right.trans hnorm)
  refine ⟨?_,hTR,?_⟩
  · rintro x ⟨z,hz,rfl⟩
    refine ⟨⟨z.val,hRS ⟨z,hz,rfl⟩⟩,mem_center_iff.mpr ?_,rfl⟩
    intro s
    apply Subtype.ext
    exact congrArg (fun k : residual H => k.val)
      (mem_center_iff.mp hz ⟨s.val,hSK s.property⟩)
  · intro he
    change R = ⊥ at he
    have hcard : Nat.card R = 4 := by
      change Nat.card ((center (residual H)).map (residual H).subtype) = 4
      rw [card_map_of_injective (residual H).subtype_injective]
      exact d.unitaryFive_right_center_card h hH hp U hc
    rw [he,card_bot] at hcard
    contradiction

theorem Preparation.unitaryFive_represented_fixed_derived_center
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
    _root_.commutator I = center I ∧ Nat.card (center I)=16 ∧
      IsElementaryAbelian 2 (center I) ∧
      Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧ Nat.card Z ≤ 16 ∧
      Z ≤ (center I).map I.subtype ∧
      normalizer (Q : Set G) ≤ normalizer (Z : Set G) := by
  let I := sourceS L H ⊓ centralizer ({t.val} : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
  let Z := (center Q ⊓ _root_.commutator Q).map Q.subtype
  obtain ⟨e⟩ := Preparation.unitaryFive_represented_inner_sylow_equiv
    h hH U r F P hinner t ht u hf hsat
  have hde : _root_.commutator I = center I := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective,center_map_equiv]
    exact Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph.fixed_unipotent_derived
      (m := 2) U.graph_fixed_field_card (by decide)
  have hcard : Nat.card (center I)=16 := by
    rw [Nat.card_congr (centerCongr e).toEquiv,
      ←Nat.card_congr Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.centerEquiv.toEquiv,
      Nat.card_prod]
    simp only [Nat.card_congr (Multiplicative.toAdd : Multiplicative
      (FixedBy.subfield U.F U.form.conj) ≃ (FixedBy.subfield U.F U.form.conj)),U.graph_fixed_field_card]
  let : IsElementaryAbelian 2 (center I) := by
    let : IsElementaryAbelian 2 (center (Theory.SpecificGroups.SymplecticFour.unipotent
      (F := FixedBy.subfield U.F U.form.conj))) :=
        Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.center_elementary
    exact IsElementaryAbelian.of_injective (centerCongr e).toMonoidHom (centerCongr e).injective
  have hIP : I ≤ Q := inf_le_inf_right _ (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
  have hder : (_root_.commutator Q).map Q.subtype ≤ sourceS L H := by
    rw [map_subtype_commutator]
    have hh := d.unitaryFive_sylow_commutator_le_sourceS h hH hp U hc
    rw [map_subtype_commutator] at hh
    exact (commutator_mono inf_le_left inf_le_left).trans hh
  have hZI : Z ≤ I := le_inf ((map_mono inf_le_right).trans hder)
    ((map_subtype_le _).trans inf_le_right)
  have hZcenter : Z ≤ (center I).map I.subtype := by
    rintro z ⟨q,hq,rfl⟩
    refine ⟨⟨q.val,hZI ⟨q,hq,rfl⟩⟩,mem_center_iff.mpr ?_,rfl⟩
    intro i
    apply Subtype.ext
    exact congrArg (fun x : Q => x.val)
      (mem_center_iff.mp hq.1 ⟨i.val,hIP i.property⟩)
  have hneI : _root_.commutator I ≠ ⊥ := by
    intro he
    rw [hde] at he
    rw [he,card_bot] at hcard
    contradiction
  have hneQ : _root_.commutator Q ≠ ⊥ := by
    intro he
    have hm : (_root_.commutator I).map I.subtype ≤ (_root_.commutator Q).map Q.subtype := by
      rw [map_subtype_commutator,map_subtype_commutator]
      exact commutator_mono hIP hIP
    rw [he,Subgroup.map_bot] at hm
    exact hneI ((map_eq_bot_iff_of_injective (_root_.commutator I)
      I.subtype_injective).mp (eq_bot_iff.mpr hm))
  have hZne : Z ≠ ⊥ := by
    intro he
    exact center_inf_ne_bot_of_normal (T.isPGroup'.to_le (show Q ≤ (T : Subgroup G) from inf_le_left))
      (_root_.commutator Q) hneQ ((map_eq_bot_iff_of_injective
        (center Q ⊓ _root_.commutator Q) Q.subtype_injective).mp he)
  have hZel : IsElementaryAbelian 2 Z := by
    let : IsElementaryAbelian 2 ((center I).map I.subtype) := IsElementaryAbelian.map I.subtype
    exact IsElementaryAbelian.of_injective (inclusion hZcenter) (inclusion_injective hZcenter)
  have hbound := card_le_of_le hZcenter
  rw [card_map_of_injective I.subtype_injective,hcard] at hbound
  exact ⟨hde,hcard,inferInstance,hZne,hZel,hbound,hZcenter,
    normalizer_le_normalizer_characteristic_image Q (center Q ⊓ _root_.commutator Q)⟩

/-- A long-root point central in the whole T lies in the derived center of
its full fixed subgroup, including every outer actor. -/
theorem Preparation.unitaryFive_represented_fixed_derived_meets_root
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
    let Q := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
    ((center Q ⊓ _root_.commutator Q).map Q.subtype) ⊓
      (center (residual H)).map (residual H).subtype ≠ ⊥ := by
  have hfixed := d.unitaryFive_represented_fixed_derived_center h hH hp U hc
    r F P hinner t ht u hf hsat
  obtain ⟨hR,hTR,hRne⟩ := d.unitaryFive_long_root_center_sourceS h hH hp U hc
  exact fixed_derived_meets_normal_root (sourceS L H)
    ((center (residual H)).map (residual H).subtype)
    (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
    (hR.trans (map_subtype_le _)) hTR hRne t.val htT hfixed.1

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

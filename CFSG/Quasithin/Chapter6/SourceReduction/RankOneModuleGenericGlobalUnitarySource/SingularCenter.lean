module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularFixed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.SelectedCenter

/-!
# The singular part of the selected full unitary centralizer

The fixed line of T ∩ L on O₂(L) is the original center of O²(H):
containment follows from the common Sylow and the self-centralizing core,
and the actual Hermitian fixed-line order proves equality. Any noncore
element of the inner Sylow detects this line among singular core vectors.

Thus ambient nonfusion preserves Z ∩ Z(O²(H)) whenever Z ≤ O₂(L) is
centralized by such an element. Conjugators need only normalize Z.
Applied to Z = Z(C_T(f)) ∩ C_T(f)′, this proves the long-root intersection
is preserved by N_G(C_T(f)). For the maximizing degree-two outer actor,
the earlier cardinal comparison supplies the required noncore element.
The SAME escaping two-group then forces the intersection to be trivial.

The source contradiction still requires nontriviality of that intersection.
No equality with the marked graph source centralizer, full-center dimension,
or exclusion of additional field actors is assumed. Both degree-two
orientations and q=4 are included; the fixed-line identity covers both
comparison families.
Source: Aschbacher–Smith F.4.35,37, printed pp.292–293, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Representation.OrthogonalFourMinus.FiniteModel
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularFixed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

namespace UnitarySource
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
  exact (Nat.card_congr j).trans (sylow_fixed_card m R)

private theorem singular_fixed_inner_iff (P : Sylow 2 L)
    (u : P) (hu : u.val ∉ pCore 2 L) (z : L.pCoreIn 2)
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
end UnitarySource

variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include d h hH hp hm hc

/-- The fixed line of the original inner Sylow is exactly the original
right-residual center, with both ambient subgroup embeddings retained. -/
theorem Preparation.unitaryFour_inner_fixed_core_eq_right_center :
    L.pCoreIn 2 ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) =
      (center (residual H)).map (residual H).subtype := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨e,f,hf⟩ := d.unitary_core_hermitian_model h hH hp m hm hc
  let K := residual H
  let S := (T : Subgroup G) ⊓ L
  let R := (center K).map K.subtype
  have hS := d.common_sylow_of_comparison h hH.1.1.2 hp
    (hc.elim (.unitary m hm) (.unitaryExtension m hm))
  have hSK : S ≤ K := by
    dsimp only [S,K]
    rw [hS]
    exact inf_le_right
  have hQS : L.pCoreIn 2 ≤ S := by
    rw [←d.unitary_inner_thompson h hH hp m hm hc]
    exact sSup_le fun _ hF => hF.1
  have hRC : R ≤ centralizer (S : Set G) := by
    rintro _ ⟨z,hz,rfl⟩
    exact mem_centralizer_iff.mpr fun s hs =>
      congrArg Subtype.val (mem_center_iff.mp hz (⟨s,hSK hs⟩ : K))
  have hRQ : R ≤ L.pCoreIn 2 := by
    rw [←d.unitary_core_centralizer h hH hp m hm hc]
    exact hRC.trans (centralizer_le (show (L.pCoreIn 2 : Set G) ⊆ S from hQS))
  have hRJ : R ≤ L.pCoreIn 2 ⊓ centralizer (S : Set G) := le_inf hRQ hRC
  obtain ⟨P,hP⟩ := exists_sylow_component h.sylow_normalizes
  have hcardJ : Nat.card (L.pCoreIn 2 ⊓ centralizer (S : Set G) : Subgroup G)=2^m := by
    dsimp only [S]
    rw [←hP]
    exact UnitarySource.core_sylow_fixed_card m e f hf P
  have hk := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
    (h.qtke.evenCharacteristic T) (d.unitary_right_maximal h hH hp m hm hc).1
  have hZQ : center K ≤ pCore 2 K :=
    (center_le_centralizer (pCore 2 K : Set K)).trans hk
  have hstr := d.unitary_core_structure h hH.1.1.2 hp m hm hc
  have hZ : (center (pCore 2 K)).map (pCore 2 K).subtype=center K := by
    apply le_antisymm hstr.2.2.2.2.2.2.2.2.2
    intro z hz
    refine ⟨⟨z,hZQ hz⟩,?_,rfl⟩
    exact mem_center_iff.mpr fun a => Subtype.ext (mem_center_iff.mp hz a.val)
  have hcardR : Nat.card R=2^m := by
    rw [card_map_of_injective K.subtype_injective,←hZ,
      card_map_of_injective (pCore 2 K).subtype_injective]
    exact hstr.2.2.2.2.2.1
  exact (eq_of_le_of_card_ge hRJ (by rw [hcardJ,hcardR])).symm

/-- The original long-root group is the singular locus on any subgroup
of the core centralized by a noncore element of the inner Sylow. -/
theorem Preparation.unitaryFour_singular_iff_right_center
    [NeZero m]
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field m))
    (f : L.pCoreIn 2 ≃* Multiplicative (Space m))
    (hf : ∀ (l : L) (v : L.pCoreIn 2),
      (f.symm (Multiplicative.ofAdd (action m (e (QuotientGroup.mk' (pCore 2 L) l))
        (f v).toAdd)) : G) = (l : G)*(v : G)*(l : G)⁻¹)
    (u : G) (hu : u ∈ (T : Subgroup G) ⊓ L) (huQ : u ∉ L.pCoreIn 2)
    (z : L.pCoreIn 2) (hz : Commute u z.val) :
    form m (f z).toAdd=0 ↔ z.val ∈ (center (residual H)).map (residual H).subtype := by
  obtain ⟨P,hP⟩ := exists_sylow_component h.sylow_normalizes
  have huP : (⟨u,hu.2⟩ : L) ∈ (P : Subgroup L) := by
    have hum : u ∈ (P : Subgroup L).map L.subtype := hP.symm ▸ hu
    exact (mem_map_iff_mem L.subtype_injective).mp hum
  have huPcore : (⟨u,hu.2⟩ : L) ∉ pCore 2 L :=
    fun hh => huQ (mem_map_of_mem L.subtype hh)
  have hh := UnitarySource.singular_fixed_inner_iff m e f hf P
    ⟨⟨u,hu.2⟩,huP⟩ huPcore z hz
  rw [hP] at hh
  rw [←d.unitaryFour_inner_fixed_core_eq_right_center h hH hp m hm hc,mem_inf]
  exact hh.trans (and_iff_right z.property).symm


/-- Ambient conjugation preserves the intersection with the original long
root group whenever the core subgroup is fixed by a noncore inner actor.
The conjugating elements need not normalize the core or either endpoint. -/
theorem Preparation.unitaryFour_long_intersection_normalizer
    (Z : Subgroup G) (hZQ : Z ≤ L.pCoreIn 2)
    (u : G) (hu : u ∈ (T : Subgroup G) ⊓ L) (huQ : u ∉ L.pCoreIn 2)
    (huZ : u ∈ centralizer (Z : Set G)) :
    normalizer (Z : Set G) ≤
      normalizer ((Z ⊓ (center (residual H)).map (residual H).subtype : Subgroup G) : Set G) := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨e,f,hf,hfusion⟩ := d.unitary_hermitian_fusion h hH hp m hm hc
  have hroot (z : G) (hz : z ∈ Z) :
      form m (f ⟨z,hZQ hz⟩).toAdd=0 ↔
        z ∈ (center (residual H)).map (residual H).subtype :=
    d.unitaryFour_singular_iff_right_center h hH hp m hm hc e f hf u hu huQ
      ⟨z,hZQ hz⟩ (mem_centralizer_iff.mp huZ z hz).symm
  have hinv (g : G) (hg : g ∈ normalizer (Z : Set G))
      (z : G) (hz : z ∈ Z ⊓ (center (residual H)).map (residual H).subtype) :
      g*z*g⁻¹ ∈ Z ⊓ (center (residual H)).map (residual H).subtype := by
    have hz' := (mem_normalizer_iff.mp hg z).mp hz.1
    refine ⟨hz',(hroot _ hz').mp ?_⟩
    apply (hfusion ⟨z,hZQ hz.1⟩ ⟨g*z*g⁻¹,hZQ hz'⟩ ?_).mp
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

/-- For the same full outer centralizer, a noncore inner fixed element
makes its center–derived long-root intersection invariant under its full
ambient normalizer. -/
theorem Preparation.unitaryFour_outer_long_intersection_normalizer
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L)
    (hinner : ¬ ((T : Subgroup G) ⊓ L) ⊓ centralizer ({u.val} : Set G) ≤ L.pCoreIn 2) :
    let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
    let Z := (center P ⊓ _root_.commutator P).map P.subtype
    normalizer (P : Set G) ≤
      normalizer ((Z ⊓ (center (residual H)).map (residual H).subtype : Subgroup G) : Set G) := by
  let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
  let Z := (center P ⊓ _root_.commutator P).map P.subtype
  obtain ⟨a,ha,haQ⟩ := SetLike.not_le_iff_exists.mp hinner
  have haZ : a ∈ centralizer (Z : Set G) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨z,hz,rfl⟩
    exact congrArg Subtype.val
      ((mem_center_iff.mp hz.1 (⟨a,ha.1.1,ha.2⟩ : P)).symm)
  exact (normalizer_le_normalizer_characteristic_image P
    (center P ⊓ _root_.commutator P)).trans
    (d.unitaryFour_long_intersection_normalizer h hH hp m hm hc Z
      (d.unitaryFour_outer_derived_center_le_core h hH hp m hm hc u hu ho).1
      a ha.1 haQ haZ)

omit hc in
/-- The actual maximizing degree-two outer involution satisfies the
long-root invariance required in F.4.37, with its full C_T(u). -/
theorem Preparation.unitaryFour_degreeTwo_maximal_long_intersection_normalizer
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse))
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L)
    (hmax : ∀ g : T, orderOf g=2 → g.val ∉ L →
      Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({u} : Set T))) :
    let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
    let Z := (center P ⊓ _root_.commutator P).map P.subtype
    normalizer (P : Set G) ≤
      normalizer ((Z ⊓ (center (residual H)).map (residual H).subtype : Subgroup G) : Set G) :=
  d.unitaryFour_outer_long_intersection_normalizer h hH hp m hm (.inr he) u hu ho
    (d.unitaryFour_degreeTwo_maximal_outer_inner_not_le_core h hH hp m hm he u hu ho hmax)

omit hc in
/-- The same maximizing involution and escaping normalizer preserve the actual long-root intersection. The intersection must be trivial, leaving its source-geometric nontriviality as the remaining contradiction. -/
theorem Preparation.unitaryFour_degreeTwo_selected_singular_center
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    ∃ f : T,
      (∀ g : T, orderOf g=2 → g.val ∉ L →
        Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({f} : Set T))) ∧
      orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        (∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G)) ∧
        Nat.card (L.pCoreIn 2 ⊓ centralizer ({f.val} : Set G) : Subgroup G) = (2^m)^3 ∧
        (∀ B : Subgroup G, B ≤ (center (residual H)).map (residual H).subtype →
          V ≤ normalizer (B : Set G) → B=⊥) ∧
        let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧ Z ≤ L.pCoreIn 2 ∧
          V ≤ normalizer (Z : Set G) ∧
          normalizer (P : Set G) ≤
            normalizer ((Z ⊓ (center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ∧
          Z ⊓ (center (residual H)).map (residual H).subtype = ⊥ := by
  have hc : FourLocalComparison L (residual H) (sourceS L H) m hm := .inr he
  obtain ⟨_,_,g,_,hgT,hg,hgo,_⟩ := d.unitary_graph_local_sylow h hH hp m hm he
  have hex : ∃ f : T, orderOf f=2 ∧ f.val ∉ L :=
    ⟨⟨g.val,hgT⟩,(Subgroup.orderOf_coe _).symm.trans hg,hgo⟩
  obtain ⟨f,hf,ho,hor,hselected,hmax⟩ := d.unitaryFour_maximal_outer_centralizer h hH hp m hm hc hex
  let C := centralizer ({f.val} : Set G)
  let P := (T : Subgroup G) ⊓ C
  have hlocal (i : Fin 2) : Chapter1.IsSylowIn 2 P
      (normalizer (![L,residual H] i : Set G) ⊓ C) := by
    have hTM : (T : Subgroup G) ≤ normalizer (![L,residual H] i : Set G) := by
      fin_cases i
      · exact h.sylow_normalizes
      · exact hH.1.1.2.trans (le_normalizer_residual H)
    apply Chapter1.isSylowIn_iff.mpr
    exact ⟨T.isPGroup'.to_le inf_le_left,inf_le_inf_right C hTM,
      fun U hU hPU hUM => hmax i U hU hPU (hUM.trans inf_le_right) (hUM.trans inf_le_left)⟩
  obtain ⟨R,hR⟩ := (T.isPGroup'.comap_subtype (K := C)).exists_le_sylow
  let U := (R : Subgroup C).map C.subtype
  have hPU : P ≤ U := by
    intro x hx
    exact mem_map_of_mem C.subtype (hR (show (⟨x,hx.2⟩ : C) ∈
      (T : Subgroup G).subgroupOf C from hx.1))
  have hlt : P < U := lt_of_le_of_ne hPU (by
    intro heq
    have hh : Chapter1.IsSylowIn 2 P C := ⟨R,heq.symm⟩
    exact d.unitaryFour_outer_centralizer_not_sylow h hH hp m hm hc f hf ho hh)
  have hUp : IsPGroup 2 U := R.isPGroup'.map C.subtype
  let V := U ⊓ normalizer (P : Set G)
  have hVp : IsPGroup 2 V := hUp.to_le inf_le_left
  have hPV : P < V := by
    have hproper : P.subgroupOf U < ⊤ := by
      rw [lt_top_iff_ne_top,Ne,subgroupOf_eq_top]
      exact not_le_of_gt hlt
    let : Group.IsNilpotent U := hUp.isNilpotent
    obtain ⟨v,hv,hvn⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (P.subgroupOf U) hproper)
    have hvN : v.val ∈ normalizer (P : Set G) := by
      rw [←subgroupOf_normalizer_eq hPU] at hv
      exact hv
    refine lt_of_le_of_ne (le_inf hPU le_normalizer) ?_
    intro hh
    exact hvn (hh.symm ▸ (show v.val ∈ V from ⟨v.property,hvN⟩))
  have hVC : V ≤ C := inf_le_left.trans (map_subtype_le _)
  have hout (i : Fin 2) : ¬ V ≤ normalizer (![L,residual H] i : Set G) := by
    intro hh
    exact hPV.ne (hmax i V hVp hPV.le hVC hh).symm
  have hZ := d.unitaryFour_outer_derived_center_le_core h hH hp m hm hc f hf ho
  have hZN := d.unitaryFour_centralizer_derived_center h hH hp m hm hc f
  have hBN := d.unitaryFour_degreeTwo_maximal_long_intersection_normalizer
    h hH hp m hm he f hf ho hselected
  refine ⟨f,hselected,hf,ho,hor,hlocal,V,hVp,hPV,hVC,inf_le_right,hout,
    d.unitaryFour_outer_core_fixed_card_eq h hH hp m hm hc f hf ho,?_,
    d.unitaryFour_degreeTwo_maximal_derived_center_ne_bot h hH hp m hm he f hf ho hselected,
    hZ.2,hZ.1,inf_le_right.trans hZN.2,hBN,?_⟩
  · intro B hB hN
    exact d.unitaryFour_escaping_two_group_long_root h hH hp m hm hc V B hVp hB hN (hout 1)
  · exact d.unitaryFour_escaping_two_group_long_root h hH hp m hm hc V _ hVp
      inf_le_right (inf_le_right.trans hBN) (hout 1)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

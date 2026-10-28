module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.ExtensionFusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.OddField
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.FieldTransfer
public import Theory.GroupTheory.ElementaryThompsonFusion

/-!
# Ambient class predicates on the same marked unitary extension

The literal endpoint map carries O₂(L) onto the native plane core. Its
normalizer is exactly the full plane endpoint, so elementary Thompson fusion
identifies core fusion in G and in this same extension. At odd outer degree,
Sylow conjugacy and the whole-overlap squares extend this equivalence to both
full endpoints. The two ambient core classes then cover the extension as well.

The two homomorphism bodies are exposed as canonical inclusions of the exact
endpoint isomorphisms; the order proof uses their literal pointwise equations.
No identification of G with the native base is used.

Source: Aschbacher--Smith F.4.35,38,43, pp.292,294,296.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace UnitaryFourFusion
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
/-- The original left full normalizer maps to the marked plane endpoint. -/
@[expose] def markedLeftHom {L K : Subgroup G} {R : Subgroup G} {m : ℕ} {hm : 1 ≤ m}
    (r : UnitaryFourNormalizerMarking L K R m hm)
    (F : RankTwoAmalgam.Iso (normalizerDiagram L K) r.extension.amalgam.reverse) :
    normalizer (L : Set G) →* r.extension.carrier :=
  (inclusion r.extension.right_le).comp
    (show normalizer (L : Set G) ≃* r.extension.right from F.left).toMonoidHom

variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm).reverse)
    (F : RankTwoAmalgam.Iso (normalizerDiagram L (residual H)) r.extension.amalgam.reverse)
    (h0 : ∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val)
include d h hH hp hc h0

private theorem core_image :
    ((L.pCoreIn 2).subgroupOf (normalizer (L : Set G))).map
      (markedLeftHom r F) =
      (ChapterF.UnitarySource.FourPlacement.planeCore m hm).map r.extension.baseHom := by
  let N := normalizer (L : Set G)
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (.unitary m hm) (.unitaryExtension m hm)) 0
  change (solvableResidual P).map P.subtype = L at hr
  have hPN : P ≤ N := by
    change P ≤ normalizer (L : Set G)
    rw [←hr]
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (solvableResidual P).le_normalizer_map P.subtype
  have hcore : P.pCoreIn 2 = L.pCoreIn 2 := le_antisymm
    (ChapterF.UnitarySource.FourPlacement.plane_comparison_core_le_residual_core
      m hm P L a.comparison.left hr)
    (pCoreIn_mono_of_normalizes (show L ≤ P from le_sup_left.trans le_sup_left) hPN)
  have hQc : (pCore 2 P).map (inclusion r.left_le) = (L.pCoreIn 2).subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le ((pCoreIn_le 2 L).trans L.le_normalizer)]
    exact hcore
  rw [←hQc]
  change ((pCore 2 P).map (inclusion r.left_le)).map
    (markedLeftHom r F) = _
  simp only [map_map]
  have hj : (markedLeftHom r F).comp
      (inclusion r.left_le) = r.extension.baseHom.comp
      ((planeParabolic m hm).subtype.comp a.comparison.left.toMonoidHom) := by
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (h0 x)
  rw [hj,←map_map,←map_map,pCore_map_iso]
  rw [ChapterF.UnitarySource.FourPlacement.planeCore_eq_twoCore]
  rfl

private theorem marked_core_normalizer :
    let j := markedLeftHom r F
    normalizer (((L.pCoreIn 2).subgroupOf (normalizer (L : Set G))).map j : Set r.extension.carrier) =
      r.extension.right.subgroupOf r.extension.carrier := by
  let N := normalizer (L : Set G)
  let Q := (L.pCoreIn 2).subgroupOf N
  let j := markedLeftHom r F
  have hrange : j.range = r.extension.right.subgroupOf r.extension.carrier := by
    apply le_antisymm
    · rintro z ⟨x,rfl⟩
      exact (F.left x).property
    · intro z hz
      obtain ⟨x,hx⟩ := F.left.surjective ⟨z.val,hz⟩
      exact ⟨x,congrArg (inclusion r.extension.right_le) hx⟩
  have hn : N ≤ normalizer (L.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hQN : L.pCoreIn 2 ≤ N := (pCoreIn_le 2 L).trans L.le_normalizer
  have hnorm : normalizer (Q : Set N) = ⊤ := by
    rw [←subgroupOf_normalizer_eq hQN]
    exact eq_top_iff.mpr (fun x _ => hn x.property)
  have hnmap : r.extension.right.subgroupOf r.extension.carrier ≤
      normalizer (Q.map j : Set r.extension.carrier) := by
    rw [←hrange,MonoidHom.range_eq_map,←hnorm]
    exact le_normalizer_map j
  change normalizer (Q.map j : Set r.extension.carrier) = _
  rw [core_image d h hH hp m hm hc r a F h0] at hnmap ⊢
  exact ChapterF.UnitarySource.ExtensionFusion.normalizer_inner r.extension
    (four_conj_injective m hm) (ChapterF.UnitarySource.FourPlacement.planeCore m hm)
    (ChapterF.UnitarySource.FourPlacement.planeCore_normalizer m hm) hnmap

theorem marked_core_fusion :
    let j := markedLeftHom r F
    ∀ x y : normalizer (L : Set G), x.val ∈ L.pCoreIn 2 → y.val ∈ L.pCoreIn 2 →
      (IsConj x.val y.val ↔ IsConj (j x) (j y)) := by
  let N := normalizer (L : Set G)
  let Q := (L.pCoreIn 2).subgroupOf N
  let j := markedLeftHom r F
  have hj : Function.Injective j := (inclusion_injective r.extension.right_le).comp F.left.injective
  have hrange : j.range = r.extension.right.subgroupOf r.extension.carrier := by
    apply le_antisymm
    · rintro z ⟨x,rfl⟩
      exact (F.left x).property
    · intro z hz
      obtain ⟨x,hx⟩ := F.left.surjective ⟨z.val,hz⟩
      exact ⟨x,congrArg (inclusion r.extension.right_le) hx⟩
  let S := T.subtype h.sylow_normalizes
  have hSindex := ChapterF.UnitarySource.ExtensionFusion.four_right_sylow_index m hm r.extension j hj hrange S
  let P : Sylow 2 r.extension.carrier := (S.isPGroup'.map j).toSylow hSindex
  have hQN : L.pCoreIn 2 ≤ N := (pCoreIn_le 2 L).trans L.le_normalizer
  have hJ : elementaryAbelianMaxJ (S : Subgroup N) = Q := by
    apply map_injective N.subtype_injective
    rw [←elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_normalizes,
      map_subgroupOf_eq_of_le hQN]
    exact d.unitary_thompson h hH hp m hm hc
  have hJP : elementaryAbelianMaxJ (P : Subgroup r.extension.carrier) = Q.map j := by
    change elementaryAbelianMaxJ ((S : Subgroup N).map j) = _
    rw [elementaryAbelianMaxJ_map_injective j hj,hJ]
  have hnorm := marked_core_normalizer d h hH hp m hm hc r a F h0
  let : IsElementaryAbelian 2 (pCore 2 L) :=
    (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.1
  let : IsElementaryAbelian 2 (L.pCoreIn 2) := IsElementaryAbelian.map L.subtype
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.subgroupOf hQN
  let : IsElementaryAbelian 2 (Q.map j) := IsElementaryAbelian.map j
  change ∀ x y : N, x.val ∈ L.pCoreIn 2 → y.val ∈ L.pCoreIn 2 →
    (IsConj x.val y.val ↔ IsConj (j x) (j y))
  intro x y hx hy
  constructor
  · intro he
    obtain ⟨g,hg,hge⟩ := d.unitary_core_fusion h hH hp m hm hc hx hy he
    have hge' : (⟨g,hg⟩ : N)*x*(⟨g,hg⟩ : N)⁻¹ = y := Subtype.ext hge
    exact j.map_isConj (isConj_iff.mpr ⟨⟨g,hg⟩,hge'⟩)
  · intro he
    have hxC : j x ∈ centralizer (elementaryAbelianMaxJ (P : Subgroup r.extension.carrier) : Set r.extension.carrier) := by
      rw [hJP]
      exact (Q.map j).le_centralizer (mem_map_of_mem j hx)
    have hyC : j y ∈ centralizer (elementaryAbelianMaxJ (P : Subgroup r.extension.carrier) : Set r.extension.carrier) := by
      rw [hJP]
      exact (Q.map j).le_centralizer (mem_map_of_mem j hy)
    obtain ⟨g,hg,hge⟩ := maxJ_controls_centralizer_fusion P hxC hyC he
    rw [hJP,hnorm,←hrange] at hg
    obtain ⟨g,rfl⟩ := hg
    have hxy : g*x*g⁻¹ = y := hj (by simpa only [map_mul,map_inv] using hge)
    exact isConj_iff.mpr ⟨g.val,congrArg Subtype.val hxy⟩

/-- The two endpoint conjugations place an original reduced-endpoint
involution in the core in both ambient groups, using the literal marking. -/
private theorem marked_involution_placement
    (x : normalizer (L : Set G))
    (hxP : x.val ∈ ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0)
    (hx2 : x^2=1) :
    ∃ y : normalizer (L : Set G), y.val ∈ L.pCoreIn 2 ∧
      IsConj x.val y.val ∧ IsConj (markedLeftHom r F x) (markedLeftHom r F y) := by
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L)
  let xP : P 0 := ⟨x.val,hxP⟩
  have hxP2 : xP^2=1 := Subtype.ext (congrArg (fun v : normalizer (L : Set G) => (v : G)) hx2)
  obtain ⟨y,hy,hxy,hxyB⟩ := ChapterF.UnitarySource.FourReturn.synchronized_involution_placement
    m hm (P 0) (P 1) a.comparison xP hxP2
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (.unitary m hm) (.unitaryExtension m hm)) 0
  have hyQ : y.val ∈ L.pCoreIn 2 :=
    ChapterF.UnitarySource.FourPlacement.plane_comparison_core_le_residual_core
      m hm (P 0) L a.comparison.left hr (mem_map_of_mem (P 0).subtype hy)
  have hxmark : markedLeftHom r F x = r.extension.baseHom (a.comparison.left xP).val :=
    Subtype.ext (h0 xP)
  have hymark : markedLeftHom r F (inclusion r.left_le y) =
      r.extension.baseHom (a.comparison.left y).val := Subtype.ext (h0 y)
  refine ⟨inclusion r.left_le y,hyQ,hxy,?_⟩
  rw [hxmark,hymark]
  exact r.extension.baseHom.map_isConj hxyB

/-- At odd outer degree, the same extension has exactly the two ambient
involution classes on the marked core. No new extension or fusion datum is chosen. -/
theorem marked_two_classes_of_odd_outer
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier) :
    ∃ z t : normalizer (L : Set G),
      z.val ∈ L.pCoreIn 2 ∧ t.val ∈ L.pCoreIn 2 ∧
      orderOf z.val=2 ∧ orderOf t.val=2 ∧
      orderOf (markedLeftHom r F z)=2 ∧ orderOf (markedLeftHom r F t)=2 ∧
      ¬ IsConj z.val t.val ∧ ¬ IsConj (markedLeftHom r F z) (markedLeftHom r F t) ∧
      (∀ x : G, orderOf x=2 → IsConj x z.val ∨ IsConj x t.val) ∧
      (∀ x : r.extension.carrier, orderOf x=2 →
        IsConj x (markedLeftHom r F z) ∨ IsConj x (markedLeftHom r F t)) := by
  let N := normalizer (L : Set G)
  let j := markedLeftHom r F
  have hj : Function.Injective j := (inclusion_injective r.extension.right_le).comp F.left.injective
  have hrange : j.range = r.extension.right.subgroupOf r.extension.carrier := by
    apply le_antisymm
    · rintro z ⟨x,rfl⟩
      exact (F.left x).property
    · intro z hz
      obtain ⟨x,hx⟩ := F.left.surjective ⟨z.val,hz⟩
      exact ⟨x,congrArg (inclusion r.extension.right_le) hx⟩
  let S := T.subtype h.sylow_normalizes
  have hSindex := ChapterF.UnitarySource.ExtensionFusion.four_right_sylow_index m hm r.extension j hj hrange S
  let P : Sylow 2 r.extension.carrier := (S.isPGroup'.map j).toSylow hSindex
  obtain ⟨z,hz,t,ht,hz2,ht2,hzt,hcover⟩ := d.unitaryFour_ambient_two_classes h hH hp m hm hc
  let zN : N := ⟨z,L.le_normalizer (pCoreIn_le 2 L hz)⟩
  let tN : N := ⟨t,L.le_normalizer (pCoreIn_le 2 L ht)⟩
  have hztE : ¬ IsConj (j zN) (j tN) :=
    fun he => hzt ((marked_core_fusion d h hH hp m hm hc r a F h0 zN tN hz ht).mpr he)
  refine ⟨zN,tN,hz,ht,hz2,ht2,?_,?_,hzt,hztE,hcover,?_⟩
  · exact (orderOf_injective j hj zN).trans ((Subgroup.orderOf_coe zN).symm.trans hz2)
  · exact (orderOf_injective j hj tN).trans ((Subgroup.orderOf_coe tN).symm.trans ht2)
  · intro x hx
    obtain ⟨b,hxb⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
    obtain ⟨v,hv,hvb⟩ := (show b.val ∈ (S : Subgroup N).map j from b.property)
    have hv2 : v^2=1 := hj (by
      rw [map_pow,map_one,hvb]
      have hb2 : b.val^2=1 := isConj_one_right.mp ((hx ▸ pow_orderOf_eq_one x) ▸ hxb.pow 2)
      exact hb2)
    have hTL : (T : Subgroup G) ≤ L :=
      inf_eq_left.mp (d.unitaryFour_two_subgroups_of_odd_outer h hH hp m hm hc r hodd).2
    have hvP : v.val ∈ ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 :=
      (show L ≤ _ from le_sup_left.trans le_sup_left) (hTL hv)
    obtain ⟨y,hy,hvy,hvyE⟩ := marked_involution_placement d h hH hp m hm hc r a F h0 v hvP hv2
    have hy2 : orderOf y.val=2 := by
      have hvo : orderOf v.val=2 := by
        rw [Subgroup.orderOf_coe v,←orderOf_injective j hj v,hvb]
        obtain ⟨g,hg⟩ := isConj_iff.mp hxb
        rw [←hg]
        exact ((MulAut.conj g).orderOf_eq x).trans hx
      obtain ⟨g,hg⟩ := isConj_iff.mp hvy
      rw [←hg]
      exact ((MulAut.conj g).orderOf_eq v.val).trans hvo
    have hxy : IsConj x (j y) := hxb.trans (hvb ▸ hvyE)
    rcases hcover y.val hy2 with hyz | hyt
    · exact Or.inl (hxy.trans ((marked_core_fusion d h hH hp m hm hc r a F h0 y zN hy hz).mp hyz))
    · exact Or.inr (hxy.trans ((marked_core_fusion d h hH hp m hm hc r a F h0 y tN hy ht).mp hyt))

omit [Finite G] d h hH hp hc h0 in
private theorem conjugate_order {X : Type*} [Group X] {x y : X} (hxy : IsConj x y) :
    orderOf y = orderOf x := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hxy
  rw [←hg]
  exact (MulAut.conj g).orderOf_eq x

/-- Every involution of the whole original left normalizer can be placed
in the marked core simultaneously in G and the same extension. -/
private theorem marked_left_placement_of_odd_outer
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier)
    (x : normalizer (L : Set G)) (hx : orderOf x.val=2) :
    ∃ y : normalizer (L : Set G), y.val ∈ L.pCoreIn 2 ∧
      IsConj x.val y.val ∧ IsConj (markedLeftHom r F x) (markedLeftHom r F y) := by
  let N := normalizer (L : Set G)
  let j := markedLeftHom r F
  let S := T.subtype h.sylow_normalizes
  obtain ⟨v,hxv⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1)
    (by simpa only [Subgroup.orderOf_coe,pow_one] using hx)
  have hvo : orderOf v.val=2 := (conjugate_order hxv).trans
    ((Subgroup.orderOf_coe x).symm.trans hx)
  have hv2 : v.val^2=1 := by simpa only [hvo] using pow_orderOf_eq_one v.val
  have hTL : (T : Subgroup G) ≤ L :=
    inf_eq_left.mp (d.unitaryFour_two_subgroups_of_odd_outer h hH hp m hm hc r hodd).2
  have hvP : v.val.val ∈ ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 :=
    (show L ≤ _ from le_sup_left.trans le_sup_left) (hTL v.property)
  obtain ⟨y,hy,hvy,hvyE⟩ := marked_involution_placement d h hH hp m hm hc r a F h0 v.val hvP hv2
  exact ⟨y,hy,(N.subtype.map_isConj hxv).trans hvy,
    (j.map_isConj hxv).trans hvyE⟩

/-- The literal whole-left endpoint map preserves both ambient involution
class predicates, even on elements outside the reduced endpoint. -/
theorem marked_left_class_of_odd_outer
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier)
    (z : normalizer (L : Set G)) (hz : z.val ∈ L.pCoreIn 2) (hz2 : orderOf z.val=2)
    (x : normalizer (L : Set G)) :
    IsConj z.val x.val ↔ IsConj (markedLeftHom r F z) (markedLeftHom r F x) := by
  let j := markedLeftHom r F
  have hj : Function.Injective j := (inclusion_injective r.extension.right_le).comp F.left.injective
  by_cases hx : orderOf x.val=2
  · obtain ⟨y,hy,hxy,hxyE⟩ := marked_left_placement_of_odd_outer d h hH hp m hm hc r a F h0 hodd x hx
    exact ⟨fun hh => ((marked_core_fusion d h hH hp m hm hc r a F h0 z y hz hy).mp
      (hh.trans hxy)).trans hxyE.symm,
      fun hh => ((marked_core_fusion d h hH hp m hm hc r a F h0 z y hz hy).mpr
        (hh.trans hxyE)).trans hxy.symm⟩
  · constructor
    · intro hh
      exact (hx ((conjugate_order hh).trans hz2)).elim
    · intro hh
      have he := conjugate_order hh
      rw [orderOf_injective j hj,orderOf_injective j hj,
        ←Subgroup.orderOf_coe x,←Subgroup.orderOf_coe z] at he
      exact (hx (he.trans hz2)).elim


omit [Finite G] d h hH hp hc h0 in
/-- The original right full normalizer maps to the marked point endpoint. -/
@[expose] def markedRightHom {L K : Subgroup G} {R : Subgroup G} {m : ℕ} {hm : 1 ≤ m}
    (r : UnitaryFourNormalizerMarking L K R m hm)
    (F : RankTwoAmalgam.Iso (normalizerDiagram L K) r.extension.amalgam.reverse) :
    normalizer (K : Set G) →* r.extension.carrier :=
  (inclusion r.extension.left_le).comp
    (show normalizer (K : Set G) ≃* r.extension.left from F.right).toMonoidHom

omit [Finite G] d h hH hp hc h0 in
theorem marked_overlap (x : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G)) :
    markedLeftHom r F (inclusion inf_le_left x) =
      markedRightHom r F (inclusion inf_le_right x) := by
  apply Subtype.ext
  exact (congrArg Subtype.val (F.left_commutes x)).trans
    (congrArg Subtype.val (F.right_commutes x)).symm

/-- The full-right endpoint map preserves the same ambient class predicates.
Its Sylow placement uses the original T and both whole-overlap squares. -/
theorem marked_right_class_of_odd_outer
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier)
    (z : normalizer (L : Set G)) (hz : z.val ∈ L.pCoreIn 2) (hz2 : orderOf z.val=2)
    (x : normalizer (residual H : Set G)) :
    IsConj z.val x.val ↔ IsConj (markedLeftHom r F z) (markedRightHom r F x) := by
  let N := normalizer (residual H : Set G)
  let k := markedRightHom r F
  have hk : Function.Injective k := (inclusion_injective r.extension.left_le).comp F.right.injective
  by_cases hx : orderOf x.val=2
  · let S := T.subtype (hH.1.1.2.trans (le_normalizer_residual H))
    obtain ⟨v,hxv⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1)
      (by simpa only [Subgroup.orderOf_coe,pow_one] using hx)
    let vD : (normalizer (L : Set G) ⊓ N : Subgroup G) :=
      ⟨v.val.val,h.sylow_normalizes v.property,v.val.property⟩
    let vL := inclusion inf_le_left vD
    have hvo : orderOf vL.val=2 :=
      (Subgroup.orderOf_coe v.val).trans ((conjugate_order hxv).trans
        ((Subgroup.orderOf_coe x).symm.trans hx))
    have hxy : IsConj x.val vL.val := N.subtype.map_isConj hxv
    have hxyE : IsConj (k x) (markedLeftHom r F vL) := by
      rw [marked_overlap m hm r F vD]
      exact k.map_isConj hxv
    have he := marked_left_class_of_odd_outer d h hH hp m hm hc r a F h0 hodd z hz hz2 vL
    exact ⟨fun hh => (he.mp (hh.trans hxy)).trans hxyE.symm,
      fun hh => (he.mpr (hh.trans hxyE)).trans hxy.symm⟩
  · have hj : Function.Injective (markedLeftHom r F) :=
      (inclusion_injective r.extension.right_le).comp F.left.injective
    constructor
    · intro hh
      exact (hx ((conjugate_order hh).trans hz2)).elim
    · intro hh
      have he := conjugate_order hh
      rw [orderOf_injective k hk,orderOf_injective (markedLeftHom r F) hj,
        ←Subgroup.orderOf_coe x,←Subgroup.orderOf_coe z] at he
      exact (hx (he.trans hz2)).elim

end UnitaryFourFusion
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

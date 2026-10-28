module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCoreSizes
public import Theory.SpecificGroups.BinaryLinear.PerfectRadicalAction
-- Internal implementation reuse preserves the frozen image-of-core calculation.
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCoreSizes

/-!
# The literal original core image has one doubled row type

For an actual binary-five point carrier, the original q(Q) is the radical
rectangle of an adjacent flag. Its conjugation action is doubled natural
or doubled dual under any prescribed marking of the original L/O2(L).
The same point centralizer, quotient map, full Sylow, and carrier are kept.
No orientation relative to the original source marking is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions

private theorem adjacent_parabolic (v : Basis 4) (last : Bool) :
    cutStabilizer v (if last then {2,3} else {0,1}) ≤
      parabolic (cutSpace v (if last then 2 else 1)) := by
  intro g hg
  exact (mem_cutStabilizer v (if last then {2,3} else {0,1}) g).mp hg
    (if last then 2 else 1) (by cases last <;> simp)

private theorem moving_rectangle_transport {X : Type*} [Group X] [Finite X]
    (a : X ≃* LinearGroup 5) (D : Subgroup X) (T : Sylow 2 X)
    (hres : (pResidual 2 (D ⊔ (T : Subgroup X) : Subgroup X)).map (D ⊔ (T : Subgroup X)).subtype=D)
    (v : Basis 4) (last : Bool)
    (hflag : D.map a.toMonoidHom ⊔
      (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup _) =
        cutStabilizer v (if last then {2,3} else {0,1})) :
    (LinearThree.commutatorCore D).map a.toMonoidHom=
      radical (cutSpace v (if last then 2 else 1)) := by
  let J := D ⊔ (T : Subgroup X)
  have hJ : J.map a.toMonoidHom=cutStabilizer v (if last then {2,3} else {0,1}) := by
    rw [Subgroup.map_sup]
    exact hflag
  have hr : (pResidual 2 (cutStabilizer v (if last then {2,3} else {0,1}))).map
      (cutStabilizer v (if last then {2,3} else {0,1})).subtype=D.map a.toMonoidHom := by
    have hh := congrArg (Subgroup.map a.toMonoidHom) hres
    rw [map_embedded_pResidual,hJ] at hh
    exact hh
  have hh := (BinaryLinear.SevenFlagCore.adjacent_residual_moving_rectangle v last).1
  rw [hr,←map_pCoreIn_of_injective 2 D a.toMonoidHom a.injective,←map_commutator] at hh
  exact hh

private theorem transport_radical_model {X E F : Type*}
    [Group X] [Group E] [AddCommGroup F] [Module (ZMod 2) F]
    (K A : Subgroup X) (hAK : A ≤ K) (a : K ≃* LinearGroup 5)
    (f : E →* K) (U : Submodule (ZMod 2) (Space 5))
    (hrect : (A.subgroupOf K).map a.toMonoidHom=radical U)
    (π : E →* BinaryLinearThree.Group)
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group F)
    (ff : E →* parabolic U) (hff : ∀ g, (ff g).val=a (f g))
    (e : radical U ≃* Multiplicative F)
    (he : ∀ (g : E) (x y : radical U), y.val=(ff g).val*x.val*(ff g).val⁻¹ →
      (e y).toAdd=ρ (π g) (e x).toAdd) :
    ∃ e : A ≃* Multiplicative F,
      ∀ (g : E) (x y : A), y.val=(f g).val*x.val*(f g).val⁻¹ →
        (e y).toAdd=ρ (π g) (e x).toAdd := by
  let r := ((subgroupOfEquivOfLe hAK).symm.trans
    ((A.subgroupOf K).equivMapOfInjective a.toMonoidHom a.injective)).trans
      (MulEquiv.subgroupCongr hrect)
  refine ⟨r.trans e,?_⟩
  intro g x y hy
  apply he g (r x) (r y)
  rw [hff]
  change a ⟨y.val,hAK y.property⟩ =
    a (f g) * a ⟨x.val,hAK x.property⟩ * (a (f g))⁻¹
  rw [←map_inv,←map_mul,←map_mul]
  exact congrArg a (Subtype.ext hy)

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual original q(Q), with the actual original L action, is doubled
natural or doubled dual for any specified original quotient marking. -/
theorem binary_three_source_five_core_image_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 5 2)
    (em : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let Qbar := ((LinearThree.commutatorCore c.L).subgroupOf C).map q
    let actor := q.comp (inclusion (show c.L ≤ C from le_sup_left.trans hLS))
    let π := linearThreeActor em
    (∃ j : Qbar ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector),
      ∀ (l : c.L) (x y : Qbar), y.val=actor l*x.val*(actor l)⁻¹ →
        (j y).toAdd=(BinaryLinearThree.W.prod BinaryLinearThree.W) (π l) (j x).toAdd) ∨
    (∃ j : Qbar ≃* Multiplicative
        (Module.Dual (ZMod 2) BinaryLinearThree.Vector × Module.Dual (ZMod 2) BinaryLinearThree.Vector),
      ∀ (l : c.L) (x y : Qbar), y.val=actor l*x.val*(actor l)⁻¹ →
        (j y).toAdd=(BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual) (π l) (j x).toAdd) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let Q := LinearThree.commutatorCore c.L
  let A := c.L.subgroupOf C
  let B := A.map q
  let D := B.subgroupOf K
  let Qbar := (Q.subgroupOf C).map q
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hQL : Q ≤ c.L := (LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)
  have hQB : Qbar ≤ B := map_mono (subgroupOf_mono C hQL)
  have hQK : Qbar ≤ K := hQB.trans hBK
  have hQeq : Qbar=LinearThree.commutatorCore B := image_core_eq c.L C hLC
  have hDmap : D.map K.subtype=B := map_subgroupOf_eq_of_le hBK
  have hcoreD : LinearThree.commutatorCore D=Qbar.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_subgroupOf_eq_of_le hQK,hQeq]
    simp only [LinearThree.commutatorCore,map_commutator,
      map_pCoreIn_of_injective 2 D _ K.subtype_injective,hDmap]
  obtain ⟨T,hT,a,v,hv,hflag⟩ := binary_three_source_five_adjacent_flags
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
  obtain ⟨_,T₁,hT₁,hres⟩ := binary_three_point_join_residual d c.L b z hLS P hP K hBK
  have hTT : T₁=T := Sylow.ext (hT₁.trans hT.symm)
  subst T₁
  have hlast : ∃ last : Bool, D.map a.toMonoidHom ⊔
      (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup _)=
        cutStabilizer v (if last then {2,3} else {0,1}) := by
    rcases hflag with hflag | hflag
    · exact ⟨false,hflag⟩
    · exact ⟨true,hflag⟩
  obtain ⟨last,hflag⟩ := hlast
  let U := cutSpace v (if last then 2 else 1)
  have hrect : (Qbar.subgroupOf K).map a.toMonoidHom=radical U := by
    rw [←hcoreD]
    exact moving_rectangle_transport a D T hres v last hflag
  have hDP : D.map a.toMonoidHom ≤ parabolic U :=
    le_sup_left.trans (hflag.le.trans (adjacent_parabolic v last))
  let : Group.IsPerfect (c.L.subgroupOf (c.L ⊔ d.S)) := b.component.perfect
  let i := subgroupOfEquivOfLe (show c.L ≤ c.L ⊔ d.S from le_sup_left)
  let : Group.IsPerfect c.L := Group.IsPerfect.ofSurjective (f := i.toMonoidHom) i.surjective
  let lB : c.L →* B := (q.subgroupMap A).comp (subgroupOfEquivOfLe hLC).symm.toMonoidHom
  have hlB : Function.Surjective lB := (q.subgroupMap_surjective A).comp (subgroupOfEquivOfLe hLC).symm.surjective
  let f : c.L →* K := (inclusion hBK).comp lB
  have hfr : f.range=D := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top_of_surjective lB hlB,
      ←MonoidHom.range_eq_map,inclusion_range]
  have hDb : D≠⊥ := by
    intro hD
    have hB : B=⊥ := by rw [←hDmap,hD,Subgroup.map_bot]
    have hQ : Qbar=⊥ := bot_unique (hQB.trans hB.le)
    have hcard := binary_three_source_five_core_image_card
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
    change Nat.card Qbar=64 at hcard
    rw [hQ,card_bot] at hcard
    contradiction
  let ff : c.L →* parabolic U := (a.toMonoidHom.comp f).codRestrict _ (fun g =>
    hDP (mem_map.mpr ⟨f g,hfr ▸ (show f g ∈ f.range from ⟨g,rfl⟩),rfl⟩))
  have hff : ff≠1 := by
    intro he
    apply hDb
    rw [←hfr,MonoidHom.range_eq_bot_iff]
    ext g : 1
    apply a.injective
    have hh := congrArg Subtype.val (DFunLike.congr_fun he g)
    change a (f g)=1 at hh
    simpa only [map_one,MonoidHom.one_apply] using hh
  let π := linearThreeActor em
  have hπ : Function.Surjective π := em.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 π.ker := by
    have heq : π.ker=pCore 2 c.L := by
      ext g
      change em (QuotientGroup.mk' _ g)=1 ↔ g ∈ pCore 2 c.L
      rw [map_eq_one_iff _ em.injective]
      exact QuotientGroup.eq_one_iff g
    rw [heq]
    exact pCore_isPGroup
  have hdim : (Module.finrank (ZMod 2) U=2 ∧ Module.finrank (ZMod 2) (Space 5 ⧸ U)=3) ∨
      (Module.finrank (ZMod 2) U=3 ∧ Module.finrank (ZMod 2) (Space 5 ⧸ U)=2) := by
    have hd := U.finrank_quotient_add_finrank
    have hd' : Module.finrank (ZMod 2) (Space 5 ⧸ U)+Module.finrank (ZMod 2) U=5 := by
      simpa only [Module.finrank_fin_fun] using hd
    have hU : Module.finrank (ZMod 2) U=(if last then 3 else 2) := by
      cases last
      · exact cutSpace_finrank v 1
      · exact cutSpace_finrank v 2
    cases last
    · have hU' : Module.finrank (ZMod 2) U=2 := hU
      rw [hU'] at hd'
      exact Or.inl ⟨hU',by omega⟩
    · have hU' : Module.finrank (ZMod 2) U=3 := hU
      rw [hU'] at hd'
      exact Or.inr ⟨hU',by omega⟩
  rcases perfect_radical_original_actor_dichotomy π hπ hk U ff hff hdim with ⟨j,hj⟩ | ⟨j,hj⟩
  · exact Or.inl (transport_radical_model K Qbar hQK a f U hrect π _ ff (fun _ => rfl) j hj)
  · exact Or.inr (transport_radical_model K Qbar hQK a f U hrect π _ ff (fun _ => rfl) j hj)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryWhole
public import Theory.Representation.SL3.NaturalNormalizerFixed
public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterRank.Intrinsic

/-!
# The original left core inside the natural unitary overcomponent

Write R = O₂(J) and U = O₂(L). A nonidentity element of J/R fixes at
most q² elements of the natural or dual q³ core. The literal image of U
has elementary order at most q² in SL₃(q). Since |U| = q⁴, these two
bounds are sharp: |R ∩ U| = q², C_R(U) = R ∩ U, and the image of U
is a maximal elementary subgroup of J/R of order q².

The source application uses the original left-core inclusion, quotient map
and whole-core intertwiner in both unitary orientations, including the
degree-two extension. It supplies the missing left-core position for the
second-parabolic argument; it does not assume or assert that the normalizer
of this quotient image lifts to the normalizer of U.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryLeftCore
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

private theorem linear_fixed_card {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    (a : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) (ha : a ≠ LinearEquiv.refl F _) :
    Nat.card {v : Fin 3 → F // a v = v} ≤ Nat.card F ^ 2 := by
  apply SL3NaturalFixed.fixed_card_le_of_semilinear a.toAddEquiv
    (fun hh => ha (LinearEquiv.ext (fun v => congrArg (fun f : (Fin 3 → F) ≃+ (Fin 3 → F) => f v) hh)))
    (RingEquiv.refl F)
  exact fun c v => a.map_smul c v

private theorem action_fixed_card {F V : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(3,F) V)
    (hm : Nonempty (ρ.Equiv (naturalBinary F)) ∨ Nonempty (ρ.Equiv (dualBinary F)))
    (g : SL(3,F)) (hg : ρ g ≠ 1) :
    Nat.card {v : V // ρ g v = v} ≤ Nat.card F ^ 2 := by
  have core (a : SL(3,F)) (E : V ≃ₗ[ZMod 2] (Fin 3 → F))
      (he : ∀ v, E (ρ g v) = a.val.mulVec (E v)) :
      Nat.card {v : V // ρ g v = v} ≤ Nat.card F ^ 2 := by
    let b := LinearEquiv.ofBijective (specialLinearNatural (k := F) 3 a)
      ((specialLinearNatural (k := F) 3).apply_bijective a)
    have hb : b ≠ LinearEquiv.refl F _ := by
      intro hh
      apply hg
      ext v
      apply E.injective
      have hx := he v
      change E (ρ g v) = b (E v) at hx
      rw [hh] at hx
      exact hx
    let f : {v : V // ρ g v = v} → {v : Fin 3 → F // b v = v} :=
      fun v => ⟨E v,(he v).symm.trans (congrArg E v.property)⟩
    exact (Nat.card_le_card_of_injective f (fun x y hxy =>
      Subtype.ext (E.injective (congrArg Subtype.val hxy)))).trans (linear_fixed_card b hb)
  rcases hm with hE | hE
  all_goals obtain ⟨E⟩ := hE
  · exact core g E.toLinearEquiv (fun v => IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g v)
  · exact core (Matrix.SpecialLinearGroup.inverseTranspose g) E.toLinearEquiv
      (fun v => IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g v)

variable {G : Type*} [Group G] [Finite G]

/-- Every element acting nontrivially on the whole natural core fixes at
most q² of its elements; this also holds for the dual action. -/
theorem fixed_core_card_le {h : HasCharacteristicTwo G} {m : ℕ}
    (d : UnitaryCover.NaturalCoreAction h m)
    (hphi : frattini (pCore 2 G) = ⊥) (g : G) (hg : g ∉ pCore 2 G) :
    Nat.card (pCore 2 G ⊓ centralizer ({g} : Set G) : Subgroup G) ≤ (2^m)^2 := by
  obtain ⟨F,_,_,_,hF,e,hmodel⟩ := d.exists_coordinates
  let := ZMod.algebra F 2
  let R := pCore 2 G
  let q := QuotientGroup.mk' (frattini R)
  let a := QuotientGroup.mk' R
  let ρ := (UnitaryCover.frattiniAction h).comp e.symm.toMonoidHom
  have hqi : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rw [QuotientGroup.ker_mk',hphi]
  have hne : ρ (e (a g)) ≠ 1 := by
    intro hh
    have hh' : UnitaryCover.frattiniAction h (a g) = UnitaryCover.frattiniAction h 1 := by
      simpa only [ρ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply,map_one] using hh
    have hz := UnitaryCover.frattiniAction_injective h hh'
    exact hg ((QuotientGroup.eq_one_iff g).mp hz)
  have hfixed (x : R) (hx : (x : G) ∈ centralizer ({g} : Set G)) :
      ρ (e (a g)) (Additive.ofMul (q x)) = Additive.ofMul (q x) := by
    have hc : MulAut.conjNormal g x = x := by
      apply Subtype.ext
      change g * (x : G) * g⁻¹ = (x : G)
      exact mul_inv_eq_iff_eq_mul.mpr (hx g (Set.mem_singleton g))
    change UnitaryCover.frattiniAction h (e.symm (e (a g))) _ = _
    rw [e.symm_apply_apply,UnitaryCover.frattiniAction_apply,quotientAut_apply_mk,hc]
  let f : (R ⊓ centralizer ({g} : Set G) : Subgroup G) →
      {v : UnitaryCover.CoreSpace G // ρ (e (a g)) v = v} :=
    fun x => ⟨Additive.ofMul (q ⟨x,x.property.1⟩),hfixed ⟨x,x.property.1⟩ x.property.2⟩
  have hi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : R => (z : G)) (hqi (congrArg (fun v => v.val.toMul) hxy))
  exact (Nat.card_le_card_of_injective f hi).trans
    (hF ▸ action_fixed_card ρ hmodel (e (a g)) hne)

/-- The original elementary q⁴ subgroup meets the natural q³ core in
exactly its fixed plane. Its literal quotient image is elementary of order q². -/
theorem left_core_geometry {h : HasCharacteristicTwo G} {m : ℕ}
    (d : UnitaryCover.NaturalCoreAction h m)
    (hphi : frattini (pCore 2 G) = ⊥) (hm : 0 < m)
    (hR : Nat.card (pCore 2 G) = (2^m)^3)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hU : Nat.card U = (2^m)^4) :
    Nat.card (pCore 2 G ⊓ U : Subgroup G) = (2^m)^2 ∧
      pCore 2 G ⊓ centralizer (U : Set G) = pCore 2 G ⊓ U ∧
      IsElementaryAbelian 2 (U.map (QuotientGroup.mk' (pCore 2 G))) ∧
      Nat.card (U.map (QuotientGroup.mk' (pCore 2 G))) = (2^m)^2 ∧
      ∀ E : Subgroup (G ⧸ pCore 2 G), IsElementaryAbelian 2 E →
        U.map (QuotientGroup.mk' (pCore 2 G)) ≤ E → E = U.map (QuotientGroup.mk' (pCore 2 G)) := by
  let R := pCore 2 G
  let q := QuotientGroup.mk' R
  let C := R ⊓ centralizer (U : Set G)
  have hq : 1 < 2^m := by
    simpa using Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) hm
  have hnot : ¬ U ≤ R := by
    intro hle
    have hh := card_le_of_le hle
    rw [hU,hR] at hh
    exact (not_lt_of_ge hh) (Nat.pow_lt_pow_right hq (by decide : 3 < 4))
  obtain ⟨g,hg,hgR⟩ := SetLike.not_le_iff_exists.mp hnot
  have hC : Nat.card C ≤ (2^m)^2 :=
    (card_le_of_le (inf_le_inf_left R (centralizer_le (Set.singleton_subset_iff.mpr hg)))).trans
      (fixed_core_card_le d hphi g hgR)
  have hIC : R ⊓ U ≤ C := inf_le_inf_left R U.le_centralizer
  have hI : Nat.card (R ⊓ U : Subgroup G) ≤ (2^m)^2 := (card_le_of_le hIC).trans hC
  let : IsElementaryAbelian 2 (U.map q) := IsElementaryAbelian.map q
  have hbound (A : Subgroup (G ⧸ R)) (hAe : IsElementaryAbelian 2 A) :
      Nat.card A ≤ (2^m)^2 := by
    let := hAe
    obtain ⟨F,_,_,_,hF,e,_⟩ := d.exists_coordinates
    let E := A.map e.toMonoidHom
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.map e.toMonoidHom
    have hr := Representation.HermitianTensorThree.ImageOuter.OuterRank.specialLinearThree_twoRank F hm hF
    have hc := (primeRank_le_iff_elementary_card_le SL(3,F)).mp hr.le E inferInstance
    rw [card_map_of_injective e.injective] at hc
    simpa only [←pow_mul,Nat.mul_comm m 2] using hc
  have hA := hbound (U.map q) inferInstance
  have hcount : Nat.card (R ⊓ U : Subgroup G) * Nat.card (U.map q) = (2^m)^4 := by
    have hc := (R.subgroupOf U).card_mul_index
    have he : Nat.card (R.subgroupOf U) = Nat.card (R ⊓ U : Subgroup G) := by
      rw [←inf_subgroupOf_right R U]
      exact Nat.card_congr (subgroupOfEquivOfLe (show R ⊓ U ≤ U from inf_le_right)).toEquiv
    rw [he,hU] at hc
    have hi : (R.subgroupOf U).index = Nat.card (U.map q) := by
      change R.relIndex U = _
      simpa only [q,QuotientGroup.ker_mk'] using (relIndex_ker U q)
    rwa [hi] at hc
  have hIc : Nat.card (R ⊓ U : Subgroup G) = (2^m)^2 := by
    have hh := Nat.mul_le_mul_left (Nat.card (R ⊓ U : Subgroup G)) hA
    rw [hcount,show (2^m)^4 = (2^m)^2*(2^m)^2 by ring] at hh
    exact le_antisymm hI ((Nat.le_of_mul_le_mul_right hh (by positivity)))
  have hAc : Nat.card (U.map q) = (2^m)^2 := by
    rw [hIc,show (2^m)^4 = (2^m)^2*(2^m)^2 by ring] at hcount
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hcount
  refine ⟨hIc,(eq_of_le_of_card_ge hIC (hIc ▸ hC)).symm,inferInstance,hAc,?_⟩
  intro E hE hle
  exact (eq_of_le_of_card_ge hle (hAc ▸ hbound E hE)).symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryLeftCore
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- The original left core has a full elementary q² image in J/O₂(J),
and its q² intersection with O₂(J) is exactly the fixed subgroup there.
All subgroups and quotient maps are the original marked ones. -/
theorem Preparation.unitary_overcomponent_left_core_geometry
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    Nat.card (J.pCoreIn 2 ⊓ L.pCoreIn 2 : Subgroup G) = (2^m)^2 ∧
      J.pCoreIn 2 ⊓ centralizer (L.pCoreIn 2 : Set G) = J.pCoreIn 2 ⊓ L.pCoreIn 2 ∧
      (let π := QuotientGroup.mk' (pCore 2 J)
       let U := (L.pCoreIn 2).subgroupOf J
       IsElementaryAbelian 2 (U.map π) ∧ Nat.card (U.map π) = (2^m)^2 ∧
         ∀ E : Subgroup (J ⧸ pCore 2 J), IsElementaryAbelian 2 E →
           U.map π ≤ E → E = U.map π) := by
  have hUJ := (d.unitary_overcomponent_left_core_normalizer h hH hp m hm he hJ hKJ hQR).1
  obtain ⟨_,hRc,hc,hact⟩ :=
    d.unitary_overcomponent_whole_natural_core h hH hp m hm he hJ hKJ hQR
  have hphi := (d.unitary_overcomponent_elementary_core h hH hp m hm he hJ hKJ hQR).2
  obtain ⟨hm',_,hUe,hUc,_⟩ := d.unitary_core_structure h hH.1.1.2 hp m hm he
  let U := (L.pCoreIn 2).subgroupOf J
  let : IsElementaryAbelian 2 (pCore 2 L) := hUe
  let : IsElementaryAbelian 2 (L.pCoreIn 2) := IsElementaryAbelian.map L.subtype
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUJ
  have hUcard : Nat.card U = (2^m)^4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUJ).toEquiv]
    exact (Nat.card_congr ((pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective).symm.toEquiv).trans hUc
  have hRcard : Nat.card (pCore 2 J) = (2^m)^3 :=
    (Nat.card_congr ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).toEquiv).trans hRc
  obtain ⟨hI,hC,helem,himage,hmax⟩ := UnitaryLeftCore.left_core_geometry hact hphi (by omega) hRcard U hUcard
  have hUm : U.map J.subtype = L.pCoreIn 2 := by
    rw [subgroupOf_map_subtype,inf_eq_left.mpr hUJ]
  have hIm : (pCore 2 J ⊓ U).map J.subtype = J.pCoreIn 2 ⊓ L.pCoreIn 2 := by
    rw [Subgroup.map_inf _ _ _ J.subtype_injective,hUm]
    rfl
  have hCm : (pCore 2 J ⊓ centralizer (U : Set J)).map J.subtype =
      J.pCoreIn 2 ⊓ centralizer (L.pCoreIn 2 : Set G) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨mem_map_of_mem J.subtype hy.1,?_⟩
      intro u hu
      exact congrArg Subtype.val (hy.2 ⟨u,hUJ hu⟩ hu)
    · intro hx
      obtain ⟨y,hy,rfl⟩ := hx.1
      refine ⟨y,⟨hy,?_⟩,rfl⟩
      intro u hu
      exact Subtype.ext (hx.2 u hu)
  have hIcard : Nat.card (J.pCoreIn 2 ⊓ L.pCoreIn 2 : Subgroup G) = (2^m)^2 := by
    rw [←hIm,card_map_of_injective J.subtype_injective]
    exact hI
  have hCeq := congrArg (Subgroup.map J.subtype) hC
  rw [hCm,hIm] at hCeq
  exact ⟨hIcard,hCeq,helem,himage,hmax⟩
end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

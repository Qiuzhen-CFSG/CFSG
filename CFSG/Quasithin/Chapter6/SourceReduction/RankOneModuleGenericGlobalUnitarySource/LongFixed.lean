module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.NormalizerGrowth
public import Theory.GroupAction.SubgroupCentralizerCongruence

/-!
# Fixed long roots exclude the ambient normalizer enlargement

A two-group normalizing a nontrivial subgroup of the original right
residual center fixes an involution there. The established full ambient
long-root centralizer bound then places that entire two-group in the
right normalizer. Applied to the actual escaping two-normalizer from
F.4.37, every normalized subgroup of the original long-root group is
therefore trivial.

In particular the long-root intersection of the characteristic
center–derived subgroup cannot be both nontrivial and preserved by this
normalizer. This isolates the exact fixed-root geometry still needed for
the selected outer involution, without identifying it with a graph actor.

Source: Aschbacher–Smith F.4.37(4), printed p.293 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open UnitaryCompletion ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include d h hH hp hm hc

/-- Normalizing any nontrivial subgroup of the original long-root group
forces a two-group into the full right endpoint. The fixed involution is
constructed in that same subgroup. -/
theorem Preparation.unitaryFour_two_group_long_root_normalizer
    (V B : Subgroup G) (hV : IsPGroup 2 V)
    (hB : B ≤ (center (residual H)).map (residual H).subtype) (hne : B ≠ ⊥)
    (hnorm : V ≤ normalizer (B : Set G)) :
    ∃ z ∈ B, orderOf z=2 ∧ V ≤ centralizer ({z} : Set G) ∧
      V ≤ normalizer (residual H : Set G) := by
  obtain ⟨b,hb1⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hb1' : b.val ≠ 1 := fun he => hb1 (Subtype.ext he)
  have hb2 := d.unitary_right_center_involutions h hH hp m hm hc b.val (hB b.property) hb1'
  have hdiv : 2 ∣ Nat.card B := by
    have hbsub : orderOf b=2 := (Subgroup.orderOf_coe b).symm.trans hb2
    rw [←hbsub]
    exact orderOf_dvd_natCard b
  have hfix : 2 ∣ Nat.card (B ⊓ centralizer (V : Set G) : Subgroup G) :=
    Nat.modEq_zero_iff_dvd.mp
      ((card_modEq_card_inf_centralizer V B hV hnorm).symm.trans hdiv.modEq_zero_nat)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' 2 hfix
  have hz2 : orderOf z.val=2 := (Subgroup.orderOf_coe z).trans hz
  have hVC : V ≤ centralizer ({z.val} : Set G) := by
    intro v hv
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp z.property.2 v hv)
  exact ⟨z.val,z.property.1,hz2,hVC,hVC.trans
    (d.unitary_central_involution_centralizers h hH hp m hm hc 1 z.val
      (hB z.property.1) hz2)⟩

/-- A two-group escaping the right endpoint cannot preserve any nontrivial
subgroup of the original long-root group. -/
theorem Preparation.unitaryFour_escaping_two_group_long_root
    (V B : Subgroup G) (hV : IsPGroup 2 V)
    (hB : B ≤ (center (residual H)).map (residual H).subtype)
    (hnorm : V ≤ normalizer (B : Set G))
    (hout : ¬ V ≤ normalizer (residual H : Set G)) : B=⊥ := by
  by_contra hne
  obtain ⟨_,_,_,_,hle⟩ := d.unitaryFour_two_group_long_root_normalizer
    h hH hp m hm hc V B hV hB hne hnorm
  exact hout hle

/-- The larger ambient normalizer supplied by an outer involution cannot
preserve a nonzero long-root intersection of its characteristic plane.
The normalizer and involution are the same witnesses throughout. -/
theorem Preparation.unitaryFour_outer_long_root_obstruction
    (hex : ∃ f : T, orderOf f=2 ∧ f.val ∉ L) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        (∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G)) ∧
        (∀ B : Subgroup G, B ≤ (center (residual H)).map (residual H).subtype →
          V ≤ normalizer (B : Set G) → B=⊥) ∧
        let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        let B := Z ⊓ (center (residual H)).map (residual H).subtype
        Z ≤ ((T : Subgroup G) ⊓ L) ⊓ centralizer ({f.val} : Set G) ∧
          V ≤ normalizer (Z : Set G) ∧
          (V ≤ normalizer (B : Set G) → B=⊥) := by
  obtain ⟨f,hf,ho,hor,hs,V,hV,hPV,hVC,hVN,hout⟩ :=
    d.unitaryFour_outer_centralizer_normalizer_growth h hH hp m hm hc hex
  have hB (B : Subgroup G) (hle : B ≤ (center (residual H)).map (residual H).subtype)
      (hN : V ≤ normalizer (B : Set G)) : B=⊥ :=
    d.unitaryFour_escaping_two_group_long_root h hH hp m hm hc V B hV hle hN (hout 1)
  have hZ := d.unitaryFour_centralizer_derived_center h hH hp m hm hc f
  exact ⟨f,hf,ho,hor,hs,V,hV,hPV,hVC,hVN,hout,hB,hZ.1,hVN.trans hZ.2,
    fun hN => hB _ inf_le_right hN⟩

omit hc in
/-- The degree-two comparison supplies this obstruction with no separate
outer-existence premise. Both orientations and q=4 are retained. -/
theorem Preparation.unitaryFour_degreeTwo_long_root_obstruction
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        (∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G)) ∧
        (∀ B : Subgroup G, B ≤ (center (residual H)).map (residual H).subtype →
          V ≤ normalizer (B : Set G) → B=⊥) ∧
        let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        let B := Z ⊓ (center (residual H)).map (residual H).subtype
        Z ≤ ((T : Subgroup G) ⊓ L) ⊓ centralizer ({f.val} : Set G) ∧
          V ≤ normalizer (Z : Set G) ∧
          (V ≤ normalizer (B : Set G) → B=⊥) := by
  obtain ⟨_,_,f,_,hfT,hf,ho,_⟩ := d.unitary_graph_local_sylow h hH hp m hm he
  exact d.unitaryFour_outer_long_root_obstruction h hH hp m hm (.inr he)
    ⟨⟨f.val,hfT⟩,(Subgroup.orderOf_coe _).symm.trans hf,ho⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

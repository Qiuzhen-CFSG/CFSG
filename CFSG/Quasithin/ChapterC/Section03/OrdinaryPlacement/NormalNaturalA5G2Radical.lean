module

public import Theory.SpecificGroups.G2Even.RadicalNormalizers
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.ShortCore
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.LongCore
public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter

/-!
# Centers of the actual two-radicals in even G₂

The exact radical normalizer classification reduces to the two five-root
cores and the positive Sylow group. The short core and Sylow centers are
the highest root group. In the long core, commuting with roots C and D
kills all coordinates except A and B. Thus every radical center has order
at most the square of the coefficient-field order.

Source: Aschbacher--Smith C.2.2, F.1.11--12 and the ordinary inspection
in 12.7.5, printed pp.144,262--264,840.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.OrdinaryPlacement.NormalNaturalA5G2
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem long_central_parameters (t : Fin 6 → F) (ht4 : t 4 = 0)
    (ht : ∀ j : Fin 6, j ≠ 4 →
      unipotentProductParameters (Pi.single j 1) t =
        unipotentProductParameters t (Pi.single j 1)) :
    t = ![t 0,t 1,0,0,0,0] := by
  have he5 := congrFun (ht 2 (by decide)) 1
  have h5 : t 5 = 0 := by
    simpa [unipotentProductParameters,Pi.single_apply,ht4,CharTwo.neg_eq,
      CharTwo.ofNat_eq_mod,add_comm] using he5.symm
  have he3 := congrFun (ht 2 (by decide)) 0
  have h3 : t 3 = 0 := by
    simpa [unipotentProductParameters,Pi.single_apply,ht4,h5,CharTwo.neg_eq,
      CharTwo.ofNat_eq_mod,add_comm] using he3.symm
  have he2 := congrFun (ht 3 (by decide)) 0
  have h2 : t 2 = 0 := by
    simpa [unipotentProductParameters,Pi.single_apply,ht4,h5,CharTwo.neg_eq,
      CharTwo.ofNat_eq_mod,add_comm] using he2
  ext i
  fin_cases i <;> simp [ht4,h5,h3,h2]

omit [Finite F] in
private theorem long_center_form (z : center (radical₂ (F := F))) :
    z.val.val = unipotentProduct ![unipotentParameters z.val.val 0,
      unipotentParameters z.val.val 1,0,0,0,0] := by
  obtain ⟨t,ht,he⟩ := z.val.property
  have hp : t = ![t 0,t 1,0,0,0,0] := by
    apply long_central_parameters t ht
    intro j hj
    apply unipotentProduct_injective
    rw [←unipotentProduct_mul,←unipotentProduct_mul,he]
    exact congrArg Subtype.val (mem_center_iff.mp z.property
      ⟨unipotentProduct (Pi.single j 1),⟨Pi.single j 1,by simp [Ne.symm hj],rfl⟩⟩)
  rw [←he,unipotentParameters_product]
  exact congrArg unipotentProduct hp

/-- The two remaining coordinates inject the long radical's center into F². -/
theorem long_radical_center_card_le :
    Nat.card (center (radical₂ (F := F))) ≤ Nat.card F ^ 2 := by
  let f : center (radical₂ (F := F)) → F × F :=
    fun z => (unipotentParameters z.val.val 0,unipotentParameters z.val.val 1)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    rw [long_center_form x,long_center_form y]
    have h0 := congrArg Prod.fst h
    have h1 := congrArg Prod.snd h
    change unipotentParameters x.val.val 0 = unipotentParameters y.val.val 0 at h0
    change unipotentParameters x.val.val 1 = unipotentParameters y.val.val 1 at h1
    rw [h0,h1]
  simpa only [Nat.card_prod,pow_two] using Nat.card_le_card_of_injective f hf

/-- Every actual two-radical has center of order at most q². -/
theorem radical_center_card_le (R : Subgroup (Model F)) (hR : R.IsPRadical 2) :
    Nat.card (center R) ≤ Nat.card F ^ 2 := by
  have hq : Nat.card F ≤ Nat.card F ^ 2 := by
    have hp : 0 < Nat.card F := Nat.card_pos
    nlinarith
  rcases Atlas.G2.radical_normalizer_parabolic_or_sylow R hR with ⟨g,hg⟩ | ⟨S,hS⟩
  · let a := MulAut.conj g
    let P := R.map a.toMonoidHom
    have hp : P.IsPRadical 2 := hR.map_equiv a
    have hc : Nat.card (center R) = Nat.card (center P) :=
      Nat.card_congr (centerCongr (R.equivMapOfInjective a.toMonoidHom a.injective)).toEquiv
    have hn : (normalizer (R : Set (Model F))).map a.toMonoidHom =
        normalizer (P : Set (Model F)) := map_equiv_normalizer_eq R a
    change (normalizer (R : Set (Model F))).map a.toMonoidHom = parabolic₁ ∨
      (normalizer (R : Set (Model F))).map a.toMonoidHom = parabolic₂ at hg
    rw [hn] at hg
    have he : (normalizer (P : Set (Model F))).pCoreIn 2 = P := hp.2
    rw [hc]
    rcases hg with hg | hg
    · rw [hg,EvenLocal.parabolic₁_pCoreIn] at he
      rw [←he,card_center_radical₁]
      exact hq
    · rw [hg,EvenLocal.parabolic₂_pCoreIn] at he
      rw [←he]
      exact long_radical_center_card_le
  · have hc : Nat.card (center R) = Nat.card F := by
      rw [←hS]
      calc
        _ = Nat.card (center (sylow (F := F))) :=
          Nat.card_congr (centerCongr (S.equiv sylow)).toEquiv
        _ = Nat.card F := Nat.card_congr
          (centerEquivHighestRoot unipotent (fiveRootSubgroup_le_unipotent _ _) le_rfl).toEquiv
    rw [hc]
    exact hq

end CFSG.Quasithin.ChapterC.OrdinaryPlacement.NormalNaturalA5G2

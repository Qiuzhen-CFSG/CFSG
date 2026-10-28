module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Definitions
public import CFSG.Quasithin.Chapter1.Section03.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.ResidualAction
public import Theory.GroupTheory.WreathTwoSylowMaximal
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Xi recognition of the actual wreath residual

A Sylow two-subgroup is maximal in the actual S₃-wreath quotient. Its
preimage is the original Sylow subgroup. An invariant subgroup of the
residual Frattini quotient therefore lifts either inside that Sylow
subgroup, hence inside the two-core, or to a normal subgroup generating
the whole group with the Sylow subgroup, hence containing O².
This proves the irreducibility required by the genuine Xi definition.

The quotient is identified with the actual elementary cubic base using
the two-core quotient map and the embedded residual subtype.
Source: Aschbacher--Smith 15.2.12(1), printed p.1111, from 15.2.8;
Definition 1.3.1, printed p.508.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Chapter1
open Chapter13.Section08.Components.Swapped.LinearThree
variable {G : Type*} [Group G] [Finite G]

/-- The exact source wreath quotient. -/
abbrev Wreath := RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))

/-- Change each S₃ factor to its actual SL₂(2) model. -/
noncomputable def matrixWreathEquiv : Wreath ≃* WreathModel.W :=
  RegularWreathProduct.congr SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
    (MulEquiv.refl _)

private theorem maximal_sylow (H : Subgroup G) (S : Sylow 2 H)
    (e : (H ⧸ pCore 2 H) ≃* Wreath) : IsCoatom (S : Subgroup H) := by
  let f : H →* WreathModel.W :=
    (e.trans matrixWreathEquiv).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := (e.trans matrixWreathEquiv).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    ext x
    change (e.trans matrixWreathEquiv) (QuotientGroup.mk' (pCore 2 H) x) = 1 ↔ _
    rw [← (e.trans matrixWreathEquiv).map_one, (e.trans matrixWreathEquiv).injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hm := isCoatom_comap_of_surjective hf
    (wreath_two_sylow_isCoatom (S.mapSurjective hf))
  change IsCoatom (((S : Subgroup H).map f).comap f) at hm
  rwa [comap_map_eq_self (hk ▸ pCore_isPGroup.le_sylow_of_normal S)] at hm

/-- Original 15.2.12(1), with no additional action or irreducibility input. -/
theorem residual_mem_Xi_of_wreath {T : Sylow 2 G} {H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hH : H ∈ Chapter1.H G)
    (e : (H ⧸ pCore 2 H) ≃* Wreath) : residual H ∈ Xi G (T : Subgroup G) := by
  let S := T.subtype hTH
  let r := ResidualAction.residualQuotientEquiv (e.trans matrixWreathEquiv)
  let : IsElementaryAbelian 3 (XiQuotient (pResidual 2 H)) :=
    IsElementaryAbelian.of_injective r.toMonoidHom r.injective
  have hc : Nat.card (XiQuotient (pResidual 2 H)) = 3 ^ 2 :=
    (Nat.card_congr r.toEquiv).trans WreathModel.cubicBase_card
  have htop : (⊤ : Subgroup H) ∈ Chapter1.H H := by
    intro hb
    apply hH
    have hm := congrArg (Subgroup.map H.subtype) hb
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective] at hm
    simpa only [←MonoidHom.range_eq_map,range_subtype,Subgroup.map_bot] using hm
  have hxi : pResidual 2 H ∈ Xi H (S : Subgroup H) := by
    let X := pResidual 2 H
    have hn : (S : Subgroup H) ≤ normalizer (X : Set H) := le_normalizer_of_normal
    refine ⟨isPPerfect_pResidual 2, hn, ?_, ⟨3, by decide, by decide,
      Or.inl ⟨inferInstance, hc⟩⟩, ?_⟩
    · simpa only [pResidual_sup_sylow_eq_top] using htop
    · intro A hA
      let f : X →* XiFrattiniQuotient X :=
        (QuotientGroup.mk' (frattini (XiQuotient X))).comp
          (QuotientGroup.mk' (pCore 2 X))
      have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
        (QuotientGroup.mk'_surjective _)
      let B := A.comap f
      let N := B.map X.subtype
      have hBN : B.Normal := inferInstance
      have hXN : X ≤ normalizer (N : Set H) := by
        have hh := B.le_normalizer_map X.subtype
        simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
      have hSN : (S : Subgroup H) ≤ normalizer (N : Set H) := by
        apply le_normalizer_iff.mpr
        rintro s hs x ⟨y,hy,rfl⟩
        let z : X := ⟨s * (y : H) * s⁻¹,
          (mem_normalizer_iff.mp (hn hs) (y : H)).mp y.property⟩
        refine ⟨z,?_,rfl⟩
        change f z ∈ A
        have hh := hA (⟨s,hs⟩ : (S : Subgroup H)) (f y) hy
        change xiFrattiniAction (S : Subgroup H) X hn ⟨s,hs⟩
          (QuotientGroup.mk' _ (QuotientGroup.mk' _ y)) ∈ A at hh
        simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk] at hh
        exact hh
      have hN : N.Normal := normalizer_eq_top_iff.mp (top_unique (by
        rw [← pResidual_sup_sylow_eq_top S]
        exact sup_le hXN hSN))
      let _ := hN
      by_cases hNS : N ≤ (S : Subgroup H)
      · left
        have hNQ : N ≤ pCore 2 H := le_sSup ⟨hN,S.isPGroup'.to_le hNS⟩
        have hBQ : B ≤ pCore 2 X := by
          apply le_sSup
          refine ⟨hBN,?_⟩
          have hb : B ≤ (pCore 2 H).subgroupOf X := by
            intro x hx
            exact hNQ (mem_map_of_mem X.subtype hx)
          exact (pCore_isPGroup (p := 2) (G := H)).comap_subtype.to_le hb
        apply bot_unique
        intro a ha
        obtain ⟨x,rfl⟩ := hf a
        have hx : x ∈ pCore 2 X := hBQ ha
        change f x = 1
        dsimp only [f,MonoidHom.comp_apply]
        have hxq : QuotientGroup.mk' (pCore 2 X) x = 1 :=
          (QuotientGroup.eq_one_iff x).mpr hx
        rw [hxq,map_one]
      · right
        have hs : N ⊔ (S : Subgroup H) = ⊤ := by
          rcases (maximal_sylow H S e).le_iff.mp
            (show (S : Subgroup H) ≤ N ⊔ (S : Subgroup H) from le_sup_right) with h | h
          · exact h
          · exact (hNS (h ▸ le_sup_left)).elim
        have hXN' : X ≤ N := sInf_le ⟨hN,
          isPGroup_quotient_of_sup_eq_top N (S : Subgroup H) S.isPGroup' hs⟩
        apply top_unique
        intro a _
        obtain ⟨x,rfl⟩ := hf a
        obtain ⟨y,hy,hyx⟩ := hXN' x.property
        have hyx' : y = x := X.subtype_injective hyx
        exact hyx' ▸ hy
  have hx := (mem_Xi_map_iff H.subtype H.subtype_injective).mpr hxi
  change residual H ∈ Xi G (((T : Subgroup G).subgroupOf H).map H.subtype) at hx
  rwa [map_subgroupOf_eq_of_le hTH] at hx

/-- The elementary quotient of the literal embedded residual, through
its original subtype and two-core quotient maps. -/
noncomputable def residualQuotientEquiv (H : Subgroup G)
    (e : (H ⧸ pCore 2 H) ≃* Wreath) :
    XiQuotient (residual H) ≃* WreathModel.cubicBase := by
  let a := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let q := QuotientGroup.congr (pCore 2 (pResidual 2 H))
    (pCore 2 (residual H)) a (pCore_map_iso 2 a)
  exact q.symm.trans (ResidualAction.residualQuotientEquiv (e.trans matrixWreathEquiv))

/-- The prime is three, rather than an unspecified odd prime in Xi. -/
theorem residual_odd_quotient_of_wreath (H : Subgroup G)
    (e : (H ⧸ pCore 2 H) ≃* Wreath) : XiOddQuotient 3 (XiQuotient (residual H)) := by
  let r := residualQuotientEquiv H e
  exact Or.inl ⟨IsElementaryAbelian.of_injective r.toMonoidHom r.injective,
    (Nat.card_congr r.toEquiv).trans WreathModel.cubicBase_card⟩

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry

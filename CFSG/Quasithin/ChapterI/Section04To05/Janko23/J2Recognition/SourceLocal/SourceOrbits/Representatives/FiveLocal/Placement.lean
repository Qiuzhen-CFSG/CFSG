module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Contracts

/-!
# Placing the fixed cubic subgroup in a five-local component

Choose an actual order-five subgroup of the selected 47.1 component.
The fixed X centralizes that component, hence normalizes the chosen F.
The generation clause of 47.2 therefore puts X in E(C_G(F)). This uses
the exact published `RootFiveWitness` and keeps its ambient embeddings,
inverting involution, and extraspecial complement.

The 47.1 geometry and 47.2 root-five family remain explicit earlier-source
inputs, owned by their respective source producers. No pair, root-fixer,
or suborbit conclusion is an input here.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1–47.2 and the opening
line of the proof of 47.5, printed pp.259–263.
-/

@[expose] public section

open scoped Pointwise
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal
namespace EarlierFive
open PrimeNormalizers.FiveLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- A five-subgroup of the selected component, together with its genuine
47.2 component and the proved placement of X. -/
structure PlacedComponent (D : Seed G) (t : G) where
  F : Subgroup G
  five : FiveCentralizing t F
  witness : RootFiveWitness D F
  X_le : D.X ≤ fiveComponent F

noncomputable def componentEquiv {F : Subgroup G} (W : RootFiveWitness D F) :
    fiveComponent F ≃* alternatingGroup (Fin 5) := by
  let N := normalizer (F : Set G)
  let B := (⊥ : Subgroup (DihedralGroup 5)).prod (⊤ : Subgroup (alternatingGroup (Fin 5)))
  let f := N.subtype.comp W.equiv.symm.toMonoidHom
  have hf : Function.Injective f := N.subtype_injective.comp W.equiv.symm.injective
  exact (MulEquiv.subgroupCongr W.component_factor.symm).trans
    ((B.equivMapOfInjective f hf).symm.trans
      ((Subgroup.prodEquiv _ _).trans ((MulEquiv.uniqueProd).trans Subgroup.topEquiv)))

/-- The source generation clause of 47.2 places X in the actual component:
choose a five-subgroup of the 47.1 component centralized by X. -/
theorem placedComponent_nonempty (S : InvolutionGeometry.SelectedGeometry D)
    (hA : RootFiveFamily D S.t) : Nonempty (PlacedComponent D S.t) := by
  let K := InvolutionGeometry.rootComponent S.t
  have hK : Nat.card K = 60 := by
    rw [show K = S.model.fiveFactor from S.component_eq,
      InvolutionGeometry.SecondCentralizer.fiveFactor,
      card_map_of_injective S.model.embedding_injective,
      Nat.card_congr (prodEquiv (⊥ : Subgroup InvolutionGeometry.E4)
        (⊤ : Subgroup InvolutionGeometry.A5)).toEquiv, Nat.card_prod]
    rw [card_bot, card_top, one_mul, InvolutionGeometry.card_A5]
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 (by rw [hK]; norm_num)
  let F := (zpowers f).map K.subtype
  have hF : Nat.card F = 5 := by
    rw [card_map_of_injective K.subtype_injective, Nat.card_zpowers, hf]
  have hFK : F ≤ K := map_subtype_le _
  have hKt : K ≤ involutionCentralizer S.t := map_subtype_le _
  have hFt : FiveCentralizing S.t F := ⟨hF, S.t, IsConj.refl _, hFK.trans hKt⟩
  obtain ⟨W⟩ := hA F hFt
  have hXF : D.X ≤ normalizer (F : Set G) := by
    apply le_trans _ (centralizer_le_normalizer _)
    intro x hx
    apply mem_centralizer_iff.mpr
    intro f hf
    exact mem_centralizer_iff.mp (S.X_centralizes_component hx) f (hFK hf)
  refine ⟨⟨F, hFt, W, ?_⟩⟩
  rw [W.generation, orbitGenerated]
  exact le_sSup ⟨MulAction.mem_orbit_self _, hXF⟩

end EarlierFive
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal

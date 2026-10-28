module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Layers
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Residual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Residual
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Projection
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility
public import Theory.Representation.GeneralLinearNatural

/-!
# The actual natural center in the third C.1.34 case

The marking on Z(Q) identifies every invariant subgroup with a subrepresentation
of the faithful irreducible binary natural module. Hence the L-conjugates of
any nonidentity fixed subgroup generate Z(Q). Applied to U = [V,Y_L], this
proves fixation of Z(Q) by Y_C from the genuine earlier local inputs.

Conversely Y_L cannot fix Z(Q): faithfulness would put Y_L in O₂(L), and its
two-perfectness would make it trivial, contradicting [V,Y_L] ≠ 1. The argument
uses the actual residuals, with no odd-order assumption on Y_C.

Source: Aschbacher–Smith, C.1.34(3), printed pp.136–137, and the proof of
15.3.23, printed p.1129 (combined manuscript of 1 March 2004).
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer
variable {G : Type*} [Group G]
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
local notation "W" => Fin 3 → ZMod 2

/-- Coordinates on the genuine natural center, with its redundant single-copy index removed. -/
noncomputable def naturalCoordinates {L Z : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1)) : Z ≃* Multiplicative W :=
  m.upperIso.trans
    { toFun v := Multiplicative.ofAdd (v.toAdd 0)
      invFun v := Multiplicative.ofAdd (fun _ => v.toAdd)
      left_inv v := by change (fun _ : Fin 1 => v.toAdd 0) = v.toAdd; funext i; exact congrArg v.toAdd (Subsingleton.elim _ _)
      right_inv v := rfl
      map_mul' _ _ := rfl }

/-- The coordinates retain the exact conjugation action and the supplied marking. -/
theorem naturalCoordinates_intertwining {L Z : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1)) (l : L) (z : Z) :
    (naturalCoordinates m (layerConjugate L Z m.normalized l z)).toAdd =
      BinaryLinearThree.W (e (QuotientGroup.mk' _ l)) (naturalCoordinates m z).toAdd := by
  exact congrFun (m.upperIso_intertwining l z) 0

/-- Every L-invariant subgroup of the natural layer is trivial or the whole layer. -/
theorem natural_invariant_eq_bot_or_eq {L Z A : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1))
    (hAZ : A ≤ Z) (hn : L ≤ normalizer (A : Set G)) : A = ⊥ ∨ A = Z := by
  let f := naturalCoordinates m
  let V : Submodule (ZMod 2) W :=
    AddSubgroup.toZModSubmodule 2 ((A.subgroupOf Z).map f.toMonoidHom).toAddSubgroup
  have hv (g : SL) (v : W) (h : v ∈ V) : BinaryLinearThree.W g v ∈ V := by
    obtain ⟨a, ha⟩ := e.surjective g
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) a
    obtain ⟨z, hz, rfl⟩ := h
    refine ⟨layerConjugate L Z m.normalized l z, (hn l.property z).mp hz, ?_⟩
    have hh := naturalCoordinates_intertwining m l z
    rw [hl, ha] at hh
    exact congrArg Multiplicative.ofAdd hh
  let V' : Subrepresentation BinaryLinearThree.W := ⟨V, fun g v h => hv g v h⟩
  let _ : IsIrreducible BinaryLinearThree.W := BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  rcases eq_bot_or_eq_top V' with hb | ht
  · left
    apply le_bot_iff.mp
    intro a ha
    have hh : (f ⟨a, hAZ ha⟩).toAdd ∈ V' := ⟨⟨a, hAZ ha⟩, ha, rfl⟩
    rw [hb] at hh
    change (f ⟨a, hAZ ha⟩).toAdd = 0 at hh
    have hz : f ⟨a, hAZ ha⟩ = f 1 := by rw [map_one]; exact congrArg Multiplicative.ofAdd hh
    exact congrArg Subtype.val (f.injective hz)
  · right
    apply le_antisymm hAZ
    intro z hz
    have hh : (f ⟨z, hz⟩).toAdd ∈ V' := by rw [ht]; trivial
    obtain ⟨a, ha, he⟩ := hh
    have he' : (a : G) = z := congrArg Subtype.val (f.injective he)
    exact he' ▸ ha

/-- Any nontrivial subgroup generates the natural layer under L-conjugation. -/
theorem natural_generated {L Z U : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1))
    (hUZ : U ≤ Z) (hU : U ≠ ⊥) : conjugateSpanBy U L = Z := by
  rcases natural_invariant_eq_bot_or_eq m (conjugateSpanBy_le hUZ m.normalized)
    (le_normalizer_conjugateSpanBy U L) with hb | hz
  · exact (hU (eq_bot_iff.mpr ((le_conjugateSpanBy U L).trans hb.le))).elim
  · exact hz

variable [Finite G]
/-- A nontrivial fixed subgroup of the natural center generates a wholly fixed center. -/
theorem YC_fixes_center (d : LocalData G) (L : Subgroup G)
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L (coreCenter L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (hcore : L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSC : d.S ≤ normalizer (YC d L : Set G))
    {U : Subgroup G} (hUZ : U ≤ coreCenter L) (hU : U ≠ ⊥)
    (hfix : YC d L ≤ centralizer (U : Set G)) :
    YC d L ≤ centralizer (coreCenter L : Set G) := by
  have hLC := component_normalizes_YC d L hcore hR hSC
  apply le_centralizer_iff.mpr
  rw [← natural_generated m hUZ hU]
  exact conjugateSpanBy_le (le_centralizer_iff.mp hfix)
    (hLC.trans (normalizer_le_normalizer_centralizer _))
omit [Finite G] in
/-- Faithfulness of the actual natural action detects the component two-core. -/
theorem natural_centralizer_le_core {L Z : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1)) :
    L ⊓ centralizer (Z : Set G) ≤ L.pCoreIn 2 := by
  intro x hx
  let l : L := ⟨x, hx.1⟩
  have hi : BinaryLinearThree.W (e (QuotientGroup.mk' _ l)) = 1 := by
    apply LinearMap.ext
    intro v
    obtain ⟨z, hz⟩ := (naturalCoordinates m).surjective (Multiplicative.ofAdd v)
    have he : layerConjugate L Z m.normalized l z = z := by
      apply Subtype.ext
      change x * (z : G) * x⁻¹ = z
      rw [← hx.2 z z.property, mul_inv_cancel_right]
    have hh := naturalCoordinates_intertwining m l z
    rw [he, hz] at hh
    exact hh.symm
  have hi' : e (QuotientGroup.mk' _ l) = e 1 := by
    rw [e.map_one]
    apply specialLinearNatural_injective 3
    exact hi.trans (map_one _).symm
  have hl : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp (e.injective hi')
  exact mem_map.mpr ⟨l, hl, rfl⟩

/-- Two-perfectness prevents the moving residual from fixing the natural center. -/
theorem YL_not_fixes_center (d : LocalData G) (L : Subgroup G)
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L (coreCenter L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (hU : ⁅d.V, YL d L⁆ ≠ ⊥) :
    ¬ YL d L ≤ centralizer (coreCenter L : Set G) := by
  intro hfix
  have hYL : YL d L ≤ L := (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have htwo : IsPGroup 2 (YL d L) :=
    (L.isPGroup_pCoreIn 2).to_le ((le_inf hYL hfix).trans (natural_centralizer_le_core m))
  have hi := (ComponentIntersection.intersectionResidual_isPPerfect d.Yplus L).hom_eq_one_of_isPGroup
    htwo (MonoidHom.id (YL d L))
  have hb : YL d L = ⊥ := by
    apply le_bot_iff.mp
    intro y hy
    exact congrArg (fun f : YL d L →* YL d L => (f ⟨y, hy⟩ : G)) hi
  exact hU (by rw [hb, commutator_bot_right])

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer
end

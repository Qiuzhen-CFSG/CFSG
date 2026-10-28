module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Layers
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Frattini
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer

/-!
# Conjugate-core reductions for the surviving L₃(2) cases

The layer transport retains the actual C.1.34 quotient actions. The residual
and Frattini arguments construct the source conjugate-core bounds once their
model-action inputs are supplied. In the three-layer case those inputs are
full Y_L displacement and fixation of Q by Y_C. In the natural-layer cases
they are fixation of Q by Y_C and the trivial action of C_S(P) on L/O₂(L).

The natural-module and three-layer action calculations are supplied by the
child modules and assembled here with the Frattini adjustment. The result keeps
the model and local geometric inputs explicit; the 15.3.23 contradiction is
assembled by the parent after choosing the source case.

Source: Aschbacher–Smith, proof of 15.3.23, printed p.1129 (PDF p.1146).
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions
universe u
variable {G : Type u} [Group G] [Finite G]

/--
The one- and two-natural-layer source cases supply the two action premises of
the Frattini reduction.  The representative outside `S` is then adjusted to
normalize the chosen actual Sylow three-subgroup, while retaining residual
exchange and the bound by the two-core of `LS`.

All model data (the quotient marking, the parabolic image and its conjugating
element) remain explicit.  Thus this theorem transports the source action
calculation without replacing the actual component by an abstract family.
-/
theorem exists_natural_conjugate_core_le
    (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) {κ : GroupClass.{u}}
    (s : NaturalActions.SourceData κ c.L d.R)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (hYplus : d.Y = d.Yplus)
    (hY : d.Y = YL d c.L ⊔ YC d c.L)
    (hTY : (d.T : Subgroup G) ≤ normalizer (d.Y : Set G))
    (hquot : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y))
    (hU : Nat.card (⁅d.V, YL d c.L⁆ : Subgroup G) = 4)
    (hUQ : ⁅d.V, YL d c.L⁆ ≤ commutatorCore c.L)
    (hfixU : YC d c.L ≤
      centralizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G))
    (e : (c.L ⧸ pCore 2 c.L) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (M : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hstd : M = Matrix.PSL3Two.pointParabolicSL ∨
      M = Matrix.PSL3Two.lineParabolicSL)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hM : ((YL d c.L ⊔ (d.S ⊓ c.L)).subgroupOf c.L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) = M.conjBy g)
    (P : Sylow 3 d.Y)
    (t₀ : G) (ht₀ : t₀ ∈ (d.T : Subgroup G)) (ht₀S : t₀ ∉ d.S)
    (hexchange : (YL d c.L).conjBy t₀ = YC d c.L) :
    ∃ t : G, t ∈ (d.T : Subgroup G) ∧ t ∉ d.S ∧
      (YL d c.L).conjBy t = YC d c.L ∧
      t ∈ normalizer (sylowThree d P : Set G) ∧
      (commutatorCore c.L).conjBy t ≤ (c.L ⊔ d.S).pCoreIn 2 := by
  obtain ⟨hfix, hCP⟩ := NaturalActions.source_actions d c s hU hUQ hfixU
    hSL hY e M hstd g hM
  exact exists_conjugate_core_le_of_actions d c hindex hcore hR hSL hYplus hY
    hTY hquot hfix P (hCP P) t₀ ht₀ ht₀S hexchange

/--
The compatible third C.1.34 case yields full `Y_L` displacement and fixes the
actual commutator core by `Y_C`.  The transported center and dual layers are
kept in one quotient marking, and the supplied outside element is returned
with the resulting conjugate-core centralizer bound.
-/
theorem three_layer_conjugate_core_centralizes
    (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (m : LayerModel c.L (coreCenter c.L) ⊥ e
      (NaturalCopies (ZMod 2) 1))
    (n : LayerModel c.L (commutatorCore c.L) (coreCenter c.L) e
      (DualCopies (ZMod 2) 2))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hU : Nat.card (⁅d.V, YL d c.L⁆ : Subgroup G) = 4)
    (hUZ : ⁅d.V, YL d c.L⁆ ≤ coreCenter c.L)
    (hfixU : YC d c.L ≤
      centralizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G))
    (hpar : YL d c.L ⊔ (d.S ⊓ c.L) =
      c.L ⊓ normalizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G))
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hexchange : (YL d c.L).conjBy t = YC d c.L) :
    ⁅commutatorCore c.L, YL d c.L⁆ = commutatorCore c.L ∧
      YC d c.L ≤ centralizer (commutatorCore c.L : Set G) ∧
      (commutatorCore c.L).conjBy t ≤ centralizer (c.L : Set G) := by
  obtain ⟨hfull, hfix⟩ := ThreeLayer.core_actions d c m n hindex hcore hR hSYL
    hU hUZ hfixU hpar t ht hexchange
  exact ⟨hfull, hfix,
    conjugate_core_centralizes_of_full_action d c
      (commutatorCore_le_S d c.L hcore hR) hSYL hfull hfix t hexchange⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions
end

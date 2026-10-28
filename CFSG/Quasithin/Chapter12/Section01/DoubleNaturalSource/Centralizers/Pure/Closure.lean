module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Contracts
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Fusion
public import Theory.GroupTheory.CentralizerInjectiveImage
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Abelian pure-point closure from the original local core

Let Q = O₂(C_G(w)). Once W lies in Q and [W₁,Q] lies in the point
line, normality of Q transports the dual summand to every C_G(w)-conjugate.
The intersection of that dual summand with the fixed point line is trivial,
so W₁ centralizes it. Faithfulness of each summand inside the W-normalizer
then makes W commute with every conjugate. Normalizer invariance propagates
this to commutativity of the entire closure.

The ambient Sylow assertion and the local core conclusions remain explicit
inputs. Source: Aschbacher--Smith 12.1.6, printed pp.791--792.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
public section
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

private theorem closure_commutative_of_core
    {G : Type*} [Group G] (W A D H Q Z : Subgroup G)
    (hAW : A ≤ W) (hDW : D ≤ W) (hZD : Z ⊓ D = ⊥)
    (hWQ : W ≤ Q) (hHQ : H ≤ normalizer (Q : Set G))
    (hQW : Q ≤ normalizer (W : Set G)) (hQD : Q ≤ normalizer (D : Set G))
    (hHZ : H ≤ centralizer (Z : Set G)) (hAQ : ⁅A, Q⁆ ≤ Z)
    (hA : normalizer (W : Set G) ⊓ centralizer (A : Set G) ≤ centralizer (W : Set G))
    (hD : normalizer (W : Set G) ⊓ centralizer (D : Set G) ≤ centralizer (W : Set G)) :
    IsMulCommutative (componentOrbit W H) := by
  have hpair (g : H) : W.map (MulAut.conj (g : G)).toMonoidHom ≤ centralizer (W : Set G) := by
    let f := (MulAut.conj (g : G)).toMonoidHom
    have hQ : Q.map f = Q := mem_normalizer_iff_map_conj_eq.mp (hHQ g.property)
    have hZ : Z.map f = Z := mem_normalizer_iff_map_conj_eq.mp
      (centralizer_le_normalizer (Z : Set G) (hHZ g.property))
    have hWgQ : W.map f ≤ Q := (map_mono hWQ).trans_eq hQ
    have hDgQ : D.map f ≤ Q := (map_mono hDW).trans hWgQ
    have hQWg : Q ≤ normalizer (W.map f : Set G) := by
      rw [← hQ]
      exact (map_mono hQW).trans (W.le_normalizer_map f)
    have hQDg : Q ≤ normalizer (D.map f : Set G) := by
      rw [← hQ]
      exact (map_mono hQD).trans (D.le_normalizer_map f)
    have hZDg : Z ⊓ D.map f = ⊥ := by
      rw [← hZ, ← map_inf _ _ _ (MulAut.conj (g : G)).injective, hZD, Subgroup.map_bot]
    have hADg : A ≤ centralizer (D.map f : Set G) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      apply bot_unique
      rw [← hZDg]
      exact le_inf ((commutator_mono le_rfl hDgQ).trans hAQ)
        (le_normalizer_iff_commutator_le_right.mp (hAW.trans (hWQ.trans hQDg)))
    have hAg : A ≤ centralizer (W.map f : Set G) := by
      have hd := map_mono (f := f) hD
      rw [← map_inf_centralizer_of_injective f (MulAut.conj (g : G)).injective,
        map_equiv_normalizer_eq W (MulAut.conj (g : G))] at hd
      have hcle : (centralizer (W : Set G)).map f ≤ centralizer (W.map f : Set G) :=
        map_centralizer_le_centralizer_image (W : Set G) f
      exact (le_inf (hAW.trans (hWQ.trans hQWg)) hADg).trans (hd.trans hcle)
    exact (le_inf (hWgQ.trans hQW) (le_centralizer_iff.mp hAg)).trans hA
  have hCW : componentOrbit W H ≤ centralizer (W : Set G) := iSup_le hpair
  have hWC : W ≤ centralizer (componentOrbit W H : Set G) := le_centralizer_iff.mp hCW
  apply le_centralizer_iff_isMulCommutative.mp
  apply iSup_le
  intro g
  have hn := (normalizer_le_normalizer_centralizer (componentOrbit W H))
    (le_normalizer_componentOrbit W H g.property)
  exact (map_mono hWC).trans_eq (mem_normalizer_iff_map_conj_eq.mp hn)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- The 12.1.6(1) conclusion from the literal Sylow and two-core inputs. -/
theorem pureCentralizerClosureAbelian_of_core
    (hs : B.PurePointSylows) (hd : B.SummandCentralizers) (hc : B.PureCoreControl) :
    B.PureCentralizerClosureAbelian := by
  intro w hw hp
  let H := centralizer ({(w : G)} : Set G)
  have hHQ : H ≤ normalizer (B.purePointCore w : Set G) := by
    have hmap := (pCore 2 H).le_normalizer_map H.subtype
    have hn : normalizer (pCore 2 H : Set H) = ⊤ := normalizer_eq_top _
    rw [hn, ← MonoidHom.range_eq_map, H.range_subtype] at hmap
    exact hmap
  have hHZ : H ≤ centralizer (zpowers (w : G) : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hQN := B.purePointCore_le_normalizers hs w hw hp
  exact closure_commutative_of_core
    (componentOrbit V (T : Subgroup G)) B.naturalSummand B.dualSummand H
    (B.purePointCore w) (zpowers (w : G))
    B.naturalSummand_le B.dualSummand_le (B.point_inf_dualSummand w hp)
    (hc.orbit_le w hw hp) hHQ (hQN.trans inf_le_left) (hQN.trans inf_le_right)
    hHZ (hc.commutator_le w hw hp) hd.natural hd.dual

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

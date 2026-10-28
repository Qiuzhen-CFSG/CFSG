module

public import Theory.SpecificGroups.Frobenius21.Recognition
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.SimpleOrder168Sylow
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.LinearAlgebra.Dimension.Free


/-!
# Binary subnormal overgroups of the Frobenius group of order 21

A subgroup F of order 21 in GL₃(2) has a characteristic Sylow seven-subgroup Q.
The Sylow count in the simple group GL₃(2), of order 168, gives |N(Q)| = 21.
Thus N(F) ≤ N(Q) = F. A self-normalizing subgroup cannot be properly subnormal
in an overgroup: the first strict step in a subnormal series would normalize it.

A basis identifies the general linear group of any three-dimensional binary
space with the existing matrix model, so all subgroups and actions here are
actual linear groups. No choice of a new representation is required.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), E.6.25, printed p.255 (PDF p.266). The Sylow-normalizer
argument is also in Gorenstein–Lyons–Solomon, *The Classification of the Finite
Simple Groups*, Number 2, Chapter C, Proposition 14.2, Step 3
(`refs/KGroup/GLS2/ChapterC.tex`). The order and simplicity results are reused
from the existing PSL₃(2) and attributed ATLAS comparison modules.
-/

public section

open Subgroup
namespace Frobenius21
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem normalizer_eq_of_card_twenty_one {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hG : Nat.card G = 168) (F : Subgroup G) (hF : Nat.card F = 21) :
    normalizer (F : Set G) = F := by
  let P : Sylow 7 F := Classical.choice inferInstance
  have hP : Nat.card P = 7 := by rw [P.card_eq_multiplicity, hF]; decide +kernel
  have : P.Characteristic := P.characteristic_of_normal (normal_sylow_seven hF P)
  let Q : Sylow 7 G := Sylow.ofCard (P.toSubgroup.map F.subtype) (by
    rw [card_map_of_injective F.subtype_injective, hP, hG]
    decide +kernel)
  have hQ : Nat.card (normalizer (Q : Set G)) = 21 :=
    Atlas.GroupTheory.simple_order_168_sylow_seven_normalizer_card hG Q
  have hn : normalizer (F : Set G) ≤ normalizer (Q : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    let a := F.normalizerMonoidHom ⟨g, hg⟩
    have hfixed : P.toSubgroup.comap a.toMonoidHom = P.toSubgroup :=
      (inferInstance : P.Characteristic).fixed a
    have hay : a y ∈ P := by
      change y ∈ P.toSubgroup.comap a.toMonoidHom
      rw [hfixed]
      exact hy
    exact mem_map.mpr ⟨a y, hay, rfl⟩
  have he : F = normalizer (Q : Set G) :=
    eq_of_le_of_card_ge (F.le_normalizer.trans hn) (by omega)
  exact le_antisymm (hn.trans_eq he.symm) F.le_normalizer

private theorem eq_of_subnormal_of_normalizer_eq {G : Type*} [Group G]
    (F H : Subgroup G) (hFH : F ≤ H) (hs : (F.subgroupOf H).IsSubnormal)
    (hn : normalizer (F : Set G) = F) : H = F := by
  have hn' : normalizer (F.subgroupOf H : Set H) = F.subgroupOf H := by
    rw [← subgroupOf_normalizer_eq hFH, hn]
  obtain ht | ⟨K, hK, _, hk⟩ := Subgroup.IsSubnormal.iff_eq_top_or_exists.mp hs
  · exact le_antisymm (subgroupOf_eq_top.mp ht) hFH
  · have hh := (normal_subgroupOf_iff_le_normalizer hK.le).mp hk
    rw [hn'] at hh
    exact False.elim (hK.not_ge hh)


variable (W : Type*) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]

/-- Every subgroup of order 21 in GL(W) is self-normalizing when W has binary dimension three. -/
theorem binary_normalizer_of_card (hdim : Module.finrank (ZMod 2) W = 3)
    (F : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)) (hF : Nat.card F = 21) :
    normalizer (F : Set (LinearMap.GeneralLinearGroup (ZMod 2) W)) = F := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hdim
  let e : Matrix.PSL3Two.SL ≃* (LinearMap.GeneralLinearGroup (ZMod 2) W) :=
    Matrix.PSL3Two.equivGL.trans (Matrix.GeneralLinearGroup.toLin' b)
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) W) := Finite.of_equiv _ e.toEquiv
  have : IsSimpleGroup Matrix.PSL3Two.SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  have : IsSimpleGroup (LinearMap.GeneralLinearGroup (ZMod 2) W) := e.symm.isSimpleGroup
  exact normalizer_eq_of_card_twenty_one
    ((Nat.card_congr e.toEquiv.symm).trans Matrix.PSL3Two.card_SL) F hF

/-- A copy of the concrete Frobenius model is self-normalizing in GL₃(2). -/
theorem binary_normalizer (hdim : Module.finrank (ZMod 2) W = 3)
    (F : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)) (e : F ≃* Model) :
    normalizer (F : Set (LinearMap.GeneralLinearGroup (ZMod 2) W)) = F :=
  binary_normalizer_of_card W hdim F ((Nat.card_congr e.toEquiv).trans card_model)

/-- A copy of the Frobenius model has no proper overgroup in which it is subnormal.
The subnormality is relative to H, using the given inclusion F ≤ H. -/
theorem binary_subnormal_overgroup (hdim : Module.finrank (ZMod 2) W = 3)
    (F H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)) (hFH : F ≤ H) (e : F ≃* Model)
    (hs : (F.subgroupOf H).IsSubnormal) : H = F :=
  eq_of_subnormal_of_normalizer_eq F H hFH hs (binary_normalizer W hdim F e)

end Frobenius21

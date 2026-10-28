module
public import Theory.GroupTheory.UniqueFixedCosetCounting
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Classes
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Extension
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityLongCentralizer
import Mathlib.Tactic.Ring

/-!
# Commuting-class incidence for the original triality comparison

The local short centralizer and the entire long centralizer are identified
with the corresponding centralizers in the same marked extension. The
published paired class catalogue identifies their commuting-class fibers.
Double counting those fibers yields the exact fixed-coset incidence count
needed in F.4.42, without assuming an order bound on the ambient group.

Source: Aschbacher--Smith F.4.42, printed p.295 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.TrialityNonbinary TrialityCompletionFusion

private theorem local_equiv {G E : Type*} [Group G] [Group E]
    (C N : Subgroup G) (D : Subgroup E) (f : N →* E)
    (hf : Function.Injective f) (hD : (C.subgroupOf N).map f = D) :
    ∃ k : N.subgroupOf C ≃* D,
      ∀ x, (k x).val = f ⟨x.val.val,x.property⟩ := by
  let s : N.subgroupOf C ≃* C.subgroupOf N := {
    toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let k := s.trans (((C.subgroupOf N).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr hD))
  exact ⟨k,fun _ => rfl⟩

variable {G : Type*} [Group G] [Finite G]
/-- The ambient long-class incidence has exactly one fixed coset on average. -/
theorem Preparation.triality_short_long_class_count
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse) :
    let P := binaryParameters m hm
    let t := (e.right.symm (shortElement P rfl)).val
    let z := (e.right.symm (longElement P rfl)).val
    let C := centralizer ({t} : Set G)
    let X := (normalizer (L : Set G)).subgroupOf C
    Nat.card {x : C // IsConj z x.val} * Nat.card X =
      Nat.card C * Nat.card {x : X // IsConj z x.val.val} := by
  let P := binaryParameters m hm
  let a := d.trialityNormalizerMarking h hH hp m hm e
  let t := (e.right.symm (shortElement P rfl)).val
  let z := (e.right.symm (longElement P rfl)).val
  let t' := a.extension.baseHom (shortElement P rfl).val
  let z' := a.extension.baseHom (longElement P rfl).val
  let C := centralizer ({t} : Set G)
  let X := (normalizer (L : Set G)).subgroupOf C
  let C' := centralizer ({t'} : Set a.extension.carrier)
  let f := (inclusion a.extension.right_le).comp a.comparison.left.toMonoidHom
  obtain ⟨kt,hkt⟩ := local_equiv C (normalizer (L : Set G)) C' f
    ((inclusion_injective a.extension.right_le).comp a.comparison.left.injective)
    (d.triality_short_extension_centralizer_image h hH hp m hm e)
  obtain ⟨hz,kz,hkz,_⟩ := d.triality_long_centralizer_full_marked h hH hp m hm e a
  obtain ⟨hl,hr⟩ := d.triality_short_centralizer_class_fidelity h hH hp m hm e a
  have hAX : Nat.card {x : X // IsConj z x.val.val} =
      Nat.card (CommutingClassIncidence.Fiber t' z') := by
    apply Nat.card_congr (kt.toEquiv.subtypeEquiv ?_)
    intro x
    change IsConj z x.val.val ↔ IsConj z' (kt x).val
    rw [hkt]
    exact hl ⟨x.val.val,x.property⟩
  have hB : Nat.card (CommutingClassIncidence.Fiber z t) =
      Nat.card (CommutingClassIncidence.Fiber z' t') := by
    apply Nat.card_congr (kz.toEquiv.subtypeEquiv ?_)
    intro x
    change IsConj t x.val ↔ IsConj t' (kz x).val
    rw [hkz]
    exact hr (inclusion hz x)
  have hC : Nat.card X = Nat.card C' := Nat.card_congr kt.toEquiv
  have hZ := Nat.card_congr kz.toEquiv
  have hb := CommutingClassIncidence.balance z t
  have hb' := CommutingClassIncidence.balance z' t'
  change Nat.card {x : C // IsConj z x.val} * Nat.card X =
    Nat.card C * Nat.card {x : X // IsConj z x.val.val}
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := centralizer ({z} : Set G)))
  change Nat.card (centralizer ({z} : Set G)) *
    (Nat.card (CommutingClassIncidence.Fiber t z) * Nat.card X) = _
  calc
    _ = (Nat.card C * Nat.card (CommutingClassIncidence.Fiber z t)) * Nat.card X := by
      rw [←mul_assoc,hb]
    _ = Nat.card C * (Nat.card (centralizer ({z'} : Set a.extension.carrier)) *
        Nat.card (CommutingClassIncidence.Fiber t' z')) := by
      rw [hC,hB]
      change (Nat.card C * _) * Nat.card (centralizer ({t'} : Set a.extension.carrier)) = _
      rw [mul_assoc,mul_comm (Nat.card (CommutingClassIncidence.Fiber z' t')),←hb']
    _ = _ := by rw [←hAX,←hZ]; ring

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

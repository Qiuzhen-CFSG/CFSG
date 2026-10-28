module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Descent
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.AutomorphismCentralizers
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent

/-!
# The sharp group rank bound for outer tensor actors

The source generalized Fitting subgroup has trivial ambient centralizer because
its matrix model is centerless. Thus conjugation embeds the ambient group in
the actual automorphism group and detects membership in the component by
innerness. The proved symplectic field-cocycle descent and automorphism-centralizer
rank theorem give the bound 3s+1 for every elementary actor containing an outer
involution. Diagram preservation is an explicit input, supplied by `Diagram`.
Only group geometry is reused from the natural-plus-graph development.

Source: Aschbacher–Smith, K.3.4.2, printed p.457.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [Field F] [CharP F 2]

theorem component_centralizer_eq_bot {K : GroupClass} (hS : SourceHypothesis K ρ L)
    (e : Sp F ≃* L) : centralizer (L : Set G) = ⊥ := by
  have hcenter : center L = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hm : e.symm x ∈ center (Sp F) := MulEquivClass.apply_mem_center e.symm hx
    rw [EvenProjective.center_eq_bot, mem_bot] at hm
    exact e.symm.injective (hm.trans e.symm.map_one.symm)
  apply le_bot_iff.mp
  intro x hx
  have hle : centralizer (L : Set G) ≤ L := by
    rw [← hS.fitting]
    exact centralizer_generalizedFitting_le G
  have hz : (⟨x, hle hx⟩ : L) ∈ center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) y y.property)
  rw [hcenter, mem_bot] at hz
  exact congrArg Subtype.val hz

variable [L.Normal]

omit [Finite G] [CharP F 2] in
theorem extensionAction_mem_inner_iff (e : Sp F ≃* L)
    (hC : centralizer (L : Set G) = ⊥) (g : G) :
    extensionAction L e g ∈ MulAut.innerSubgroup (Sp F) ↔ g ∈ L := by
  have hi (x : Sp F) : extensionAction L e (e x).val = MulAut.conj x := by
    apply MulEquiv.ext
    intro y
    apply e.injective
    apply Subtype.ext
    rw [extensionAction_apply]
    simp
  constructor
  · rintro ⟨x, hx⟩
    have he : g = (e x).val := extensionAction_injective L e hC
      (hx.symm.trans (hi x).symm)
    exact he ▸ (e x).property
  · intro hg
    exact ⟨e.symm ⟨g, hg⟩, by simpa only [e.apply_symm_apply] using
      (hi (e.symm ⟨g, hg⟩)).symm⟩

variable [Finite F]

theorem outer_centralizer_rank_le {s : ℕ} (hs : 0 < s)
    (hF : Nat.card F = 2 ^ (2 * s)) (e : Sp F ≃* L)
    (hC : centralizer (L : Set G) = ⊥)
    (hdiagram : ∀ g : G, PreservesDiagram (extensionAction L e g))
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) :
    primeRank 2 (centralizer ({t} : Set G)) ≤ 3 * s + 1 := by
  let α := extensionAction L e
  have hα := extensionAction_injective L e hC
  have ho : orderOf (α t) = 2 := (orderOf_injective α hα t).trans ht
  have hn : α t ∉ MulAut.innerSubgroup (Sp F) :=
    fun hh => hout ((extensionAction_mem_inner_iff L e hC t).mp hh)
  have hb := (SymplecticConjugatePair.Ambient.AutomorphismCentralizers.preserving_outer_centralizer_rank_le_of_descent hF (by omega)
      (half_frobenius_cocycle_coboundary hF (by omega)) (α t) ho (hdiagram t) hn).2
  let f : centralizer ({t} : Set G) →* centralizer ({α t} : Set (MulAut (Sp F))) :=
    (α.comp (centralizer ({t} : Set G)).subtype).codRestrict _ (fun x => by
      rw [mem_centralizer_singleton_iff]
      change α x.val * α t = α t * α x.val
      rw [← map_mul, ← map_mul]
      exact congrArg α (mem_centralizer_singleton_iff.mp x.property))
  have hf : Function.Injective f := fun _ _ hh => Subtype.ext (hα (congrArg Subtype.val hh))
  have hh := (Theory.GroupTheory.primeRank_le_of_injective 2 f hf).trans hb
  simpa using hh

theorem outer_elementary_rank_le {s : ℕ} (hs : 0 < s)
    (hF : Nat.card F = 2 ^ (2 * s)) (e : Sp F ≃* L)
    (hC : centralizer (L : Set G) = ⊥)
    (hdiagram : ∀ g : G, PreservesDiagram (extensionAction L e g))
    (A : Subgroup G) (hA : IsElementaryTwo A) (t : G) (htA : t ∈ A) (hout : t ∉ L) :
    rank A ≤ 3 * s + 1 := by
  let : IsElementaryAbelian 2 A := hA.2
  have ht : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t htA) (fun he => hout (he ▸ L.one_mem))
  have hle : A ≤ centralizer ({t} : Set G) := by
    intro a ha
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm
      (⟨a, ha⟩ : A) ⟨t, htA⟩)
  let f := (inclusion hle)
  have hf := inclusion_injective hle
  let B : Subgroup (centralizer ({t} : Set G)) := f.range
  have hB : IsElementaryAbelian 2 B :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le (centralizer ({t} : Set G))).mp
    (outer_centralizer_rank_le L hs hF e hC hdiagram t ht hout) B hB
  have he : Nat.card B = Nat.card A := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm
  rw [he] at hc
  simpa only [BinaryOffender.rank, Nat.log_pow (by decide : 1 < 2)] using Nat.log_mono_right (b := 2) hc

end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer

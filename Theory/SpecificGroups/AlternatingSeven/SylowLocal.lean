module
public import Theory.SpecificGroups.SymmetricFourSylow
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.ModelAction
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Theory.GroupAction.LargeOrbitNormalizer
public import Theory.Alternating.Aut
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# A canonical characteristic-two local overgroup of an A7 Sylow

The marked dihedral Sylow has point orbits of sizes four, two and one.
Every normalizing permutation preserves the four-point orbit and the unique
fixed point, hence preserves the signed S4 on the four points and the pair.
The full automorphism theorem for A7 gives invariance under every abstract
Sylow-preserving automorphism. Sylow conjugacy transports the construction.

The signed S4 cannot centralize a triple transposition: commuting with its
three adjacent generators fixes two specified points, whereas a triple
transposition on seven points has only one fixed point. The finite checks
are confined to eight Sylow entries and twenty-four S4 elements.

Source application: Aschbacher--Smith 2.5.2, printed p.551, excluding the
A7 and triple A7 component alternatives under the empty Gamma-even hypothesis.
-/

public section
namespace AlternatingSevenSylowLocal
open Equiv Subgroup
open scoped Pointwise
abbrev S7 := Perm (Fin 7)
abbrev A7 := alternatingGroup (Fin 7)
private def signedPerm (g : Perm (Fin 4)) : S7 :=
  (finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7).permCongr (Equiv.sumCongr g (Equiv.refl (Fin 3))) * if Perm.sign g = 1 then 1 else swap 4 5
set_option maxRecDepth 10000 in
private theorem signed_even : ∀ g : Perm (Fin 4), Perm.sign (signedPerm g) = 1 := by decide +kernel

private def signed : Perm (Fin 4) →* A7 where
  toFun g := ⟨signedPerm g,signed_even g⟩
  map_one' := by decide
  map_mul' := by decide +kernel

set_option maxRecDepth 10000 in
private theorem signed_injective : Function.Injective signed := by decide +kernel
private noncomputable def localGroup : Subgroup A7 := signed.range
private noncomputable def localEquiv : localGroup ≃* Perm (Fin 4) :=
  (MonoidHom.ofInjective signed_injective).symm

private theorem local_characteristicTwo :
    centralizer (pCore 2 localGroup : Set localGroup) ≤ pCore 2 localGroup :=
  Matrix.PSL3Two.ParabolicCoreModel.core_selfCentralizing localEquiv

private def a : A7 := ⟨swap 0 1 * swap 2 3, by change Perm.sign _ = 1; decide⟩
private def b : A7 := ⟨swap 0 1 * swap 4 5, by change Perm.sign _ = 1; decide⟩
private def r : A7 := ⟨swap 0 2 * swap 1 3, by change Perm.sign _ = 1; decide⟩
private def entry : Fin 8 → A7 := ![1,a,b,a*b,r,a*r,b*r,a*b*r]
private def sylowGroup : Subgroup A7 where
  carrier := Set.range entry
  one_mem' := ⟨0,rfl⟩
  mul_mem' := by
    rintro x y ⟨i,rfl⟩ ⟨j,rfl⟩
    change ∃ k,entry k = entry i * entry j
    fin_cases i <;> fin_cases j <;> decide
  inv_mem' := by
    rintro x ⟨i,rfl⟩
    change ∃ j,entry j = (entry i)⁻¹
    fin_cases i <;> decide

private theorem sylowGroup_le_local : sylowGroup ≤ localGroup := by
  rintro x ⟨i,rfl⟩
  have h : ∀ i : Fin 8,∃ g : Perm (Fin 4), signed g = entry i := by decide +kernel
  exact h i

private theorem sylowGroup_card : Nat.card sylowGroup = 8 := by
  let f : Fin 8 → sylowGroup := fun i => ⟨entry i,⟨i,rfl⟩⟩
  have hi : Function.Injective f := by
    intro i j he
    have hc : Function.Injective entry := by decide
    exact hc (congrArg Subtype.val he)
  have hs : Function.Surjective f := by rintro ⟨_,i,rfl⟩;exact ⟨i,rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm.trans (by simp)

private noncomputable def sylow : Sylow 2 A7 := Sylow.ofCard sylowGroup (by
  rw [sylowGroup_card, nat_card_alternatingGroup, Nat.card_fin]
  decide +kernel)

set_option maxRecDepth 10000 in
private theorem all_fix6 : ∀ i, (entry i : S7) 6 = 6 := by decide
set_option maxRecDepth 10000 in
private theorem only_fix6 : ∀ j : Fin 7, (∀ i, (entry i : S7) j = j) → j = 6 := by decide

private def fourSet : Finset (Fin 7) := {0,1,2,3}


set_option maxRecDepth 10000 in
private theorem local_generators_shape : ∀ k : Perm (Fin 4),
    signedPerm k 6 = 6 ∧ ∀ i ∈ fourSet, signedPerm k i ∈ fourSet := by decide +kernel

set_option maxRecDepth 10000 in
private theorem signed_on_four : ∀ (k : Perm (Fin 4)) (i : Fin 4),
    signedPerm k ⟨i.val,by omega⟩ = ⟨(k i).val,by omega⟩ := by decide +kernel

private theorem mem_fourSet (i : Fin 7) : i ∈ fourSet ↔ i.val < 4 := by
  fin_cases i <;> decide

private theorem even_eq_one_of_fix_four_and_six (g : S7) (he : Perm.sign g = 1)
    (hf : ∀ i : Fin 4, g ⟨i.val,by omega⟩ = ⟨i.val,by omega⟩)
    (h6 : g 6 = 6) : g = 1 := by
  have hs : g.support ⊆ {4,5} := by
    intro i hi
    have hn := Perm.mem_support.mp hi
    fin_cases i
    · exact (hn (hf 0)).elim
    · exact (hn (hf 1)).elim
    · exact (hn (hf 2)).elim
    · exact (hn (hf 3)).elim
    · simp
    · simp
    · exact (hn h6).elim
  by_contra hn
  have hb := Finset.card_le_card hs
  have hl := Perm.two_le_card_support_of_ne_one hn
  have hc : g.support.card = 2 := by simpa using Nat.le_antisymm hb hl
  have hg := (Perm.card_support_eq_two.mp hc).sign_eq
  rw [he] at hg
  contradiction

private theorem local_shape (g : S7) (he : Perm.sign g = 1)
    (h6 : g 6 = 6) (hF : ∀ i ∈ fourSet, g i ∈ fourSet) :
    ∃ k : Perm (Fin 4), signedPerm k = g := by
  let f : Fin 4 → Fin 4 := fun i => ⟨(g ⟨i.val,by omega⟩).val,
    (mem_fourSet _).mp (hF _ ((mem_fourSet _).mpr i.isLt))⟩
  have hfi : Function.Injective f := by
    intro i j heq
    have hval := congrArg Fin.val heq
    have hh := g.injective (Fin.ext hval)
    exact Fin.ext (congrArg (fun x : Fin 7 => x.val) hh)
  let e : Perm (Fin 4) := Equiv.ofBijective f (⟨hfi,Finite.surjective_of_injective hfi⟩)
  have hge (i : Fin 4) : g ⟨i.val,by omega⟩ = signedPerm e ⟨i.val,by omega⟩ := by
    rw [signed_on_four]
    rfl
  have hz := even_eq_one_of_fix_four_and_six ((signedPerm e)⁻¹ * g)
    (by simp [signed_even,he])
    (by intro i; change (signedPerm e)⁻¹ (g ⟨i.val,by omega⟩) = _; rw [hge]; simp)
    (by change (signedPerm e)⁻¹ (g 6) = 6; rw [h6];
        exact (signedPerm e).symm_apply_eq.mpr (local_generators_shape e).1.symm)
  exact ⟨e,inv_mul_eq_one.mp hz⟩

private abbrev sylowPermGroup : Subgroup S7 := sylowGroup.map (alternatingGroup (Fin 7)).subtype

private theorem orbit_four : MulAction.orbit sylowPermGroup (0 : Fin 7) = (fourSet : Set (Fin 7)) := by
  ext j
  have he : j ∈ MulAction.orbit sylowPermGroup (0 : Fin 7) ↔
      ∃ i : Fin 8, (entry i : S7) 0 = j := by
    constructor
    · rintro ⟨g,rfl⟩
      obtain ⟨x,⟨i,rfl⟩,hh⟩ := g.property
      exact ⟨i,congrArg (fun p : S7 => p 0) hh⟩
    · rintro ⟨i,hi⟩
      exact ⟨⟨(entry i : S7),mem_map_of_mem _ (show entry i ∈ sylowGroup from ⟨i,rfl⟩)⟩,hi⟩
  rw [he]
  fin_cases j <;> decide

private theorem normalizer_shape (g : S7)
    (hg : g ∈ normalizer (sylowPermGroup : Set S7)) :
    g 6 = 6 ∧ ∀ i ∈ fourSet, g i ∈ fourSet := by
  constructor
  · apply only_fix6
    intro i
    have hm := (((normalizer (sylowPermGroup : Set S7)).inv_mem hg) (entry i : S7)).mp
      (mem_map_of_mem _ (show entry i ∈ sylowGroup from ⟨i,rfl⟩))
    obtain ⟨x,⟨j,rfl⟩,he⟩ := hm
    have hh : (g⁻¹ * (entry i : S7) * g) 6 = 6 := by
      simpa only [inv_inv] using (congrArg (fun p : S7 => p 6) he).symm.trans (all_fix6 j)
    have hv := congrArg g hh
    simpa only [Perm.mul_apply,Perm.inv_def,Equiv.apply_symm_apply] using hv
  · have hn := normalizer_le_stabilizer_of_large_orbit sylowPermGroup (0 : Fin 7) (by
      rw [orbit_four,Set.ncard_coe_finset,Nat.card_fin]
      decide)
    have he : g • (fourSet : Set (Fin 7)) = (fourSet : Set (Fin 7)) := by
      simpa only [orbit_four] using MulAction.mem_stabilizer_iff.mp (hn hg)
    intro i hi
    have hx : g • i ∈ g • (fourSet : Set (Fin 7)) := ⟨i,hi,rfl⟩
    rw [he] at hx
    exact hx

private theorem triple_not_centralizes (σ : S7) (hσ : σ.cycleType = {2,2,2}) :
    ¬ ∀ k : Perm (Fin 4), signedPerm k * σ = σ * signedPerm k := by
  intro h
  have h2 := congrArg (fun g : S7 => g 0) (h (swap 1 2))
  have h3 := congrArg (fun g : S7 => g 0) (h (swap 2 3))
  have ha : signedPerm (swap 1 2) (σ 0) = σ 0 := by
    simpa only [Perm.mul_apply,
      show signedPerm (swap 1 2) 0 = 0 from by decide] using h2
  have hb : signedPerm (swap 2 3) (σ 0) = σ 0 := by
    simpa only [Perm.mul_apply,
      show signedPerm (swap 2 3) 0 = 0 from by decide] using h3
  have hc : ∀ j : Fin 7, signedPerm (swap 1 2) j = j →
      signedPerm (swap 2 3) j = j → j = 0 ∨ j = 6 := by decide
  have h01 := congrArg (fun g : S7 => g 0) (h (swap 0 1))
  change signedPerm (swap 0 1) (σ 0) = σ (signedPerm (swap 0 1) 0) at h01
  rw [show signedPerm (swap 0 1) 0 = 1 from by decide] at h01
  have h0 : σ 0 = 0 := by
    rcases hc (σ 0) ha hb with hx | hx
    · exact hx
    · rw [hx,show signedPerm (swap 0 1) 6 = 6 from by decide] at h01
      exact (show (0 : Fin 7) ≠ 1 from by decide) (σ.injective (hx.trans h01)) |>.elim
  have h1 : σ 1 = 1 := by
    rw [h0,show signedPerm (swap 0 1) 0 = 1 from by decide] at h01
    exact h01.symm
  have hsup : σ.support ⊆ Finset.univ \ {0,1} := by
    intro i hi
    simp only [Finset.mem_sdiff,Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_and,not_or]
    exact ⟨fun he => Perm.mem_support.mp hi (he.symm ▸ h0),
      fun he => Perm.mem_support.mp hi (he.symm ▸ h1)⟩
  have hcard := Finset.card_le_card hsup
  have hcycle := Perm.sum_cycleType σ
  rw [hσ] at hcycle
  have hs : σ.support.card = 6 := by simpa using hcycle.symm
  rw [hs] at hcard
  have hfive : (Finset.univ \ ({0,1} : Finset (Fin 7))).card = 5 := by decide
  rw [hfive] at hcard
  omega

private theorem normalizer_maps_local (g : S7)
    (hg : g ∈ normalizer (sylowPermGroup : Set S7)) :
    localGroup.map (MulAut.conjNormal (H := alternatingGroup (Fin 7)) g).toMonoidHom ≤ localGroup := by
  have hshape := normalizer_shape g hg
  have hishape := normalizer_shape g⁻¹ ((normalizer _).inv_mem hg)
  rintro x ⟨k,⟨a,rfl⟩,rfl⟩
  obtain ⟨b,hb⟩ := local_shape (g * signedPerm a * g⁻¹)
    (by simp [signed_even])
    (by simp only [Perm.mul_apply,hishape.1,(local_generators_shape a).1,hshape.1])
    (by intro i hi; exact hshape.2 _ ((local_generators_shape a).2 _ (hishape.2 _ hi)))
  exact ⟨b,Subtype.ext hb⟩

private theorem local_invariant_of_sylow_invariant (α : MulAut A7)
    (hP : sylowGroup.map α.toMonoidHom = sylowGroup) :
    localGroup.map α.toMonoidHom = localGroup := by
  obtain ⟨g,rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    7 (by decide) (by decide)).2 α
  have hg : g ∈ normalizer (sylowPermGroup : Set S7) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [show sylowPermGroup = sylowGroup.map (alternatingGroup (Fin 7)).subtype from rfl,map_map]
    change sylowGroup.map ((alternatingGroup (Fin 7)).subtype.comp
      (MulAut.conjNormal (H := alternatingGroup (Fin 7)) g).toMonoidHom) = _
    rw [← map_map,hP]
  exact Subgroup.eq_of_le_of_card_ge (normalizer_maps_local g hg)
    (card_map_of_injective (MulAut.conjNormal (H := alternatingGroup (Fin 7)) g).injective).ge

private theorem local_not_centralizes_triple (σ : S7) (hσ : σ.cycleType = {2,2,2}) :
    ¬ ∀ k ∈ localGroup, (k : S7) * σ = σ * k := by
  intro h
  exact triple_not_centralizes σ hσ (fun k => h (signed k) ⟨_,rfl⟩)

/-- Every actual A7 Sylow has a canonical S4 overgroup, invariant under
all Sylow-preserving automorphisms, which is not centralized by any triple
transposition. The construction uses the original seven-point action. -/
theorem exists_invariant_local (P : Sylow 2 A7) :
    ∃ K : Subgroup A7, (P : Subgroup A7) ≤ K ∧
      Nonempty (K ≃* Perm (Fin 4)) ∧
      (∀ α : MulAut A7, (P : Subgroup A7).map α.toMonoidHom = P →
        K.map α.toMonoidHom = K) ∧
      ∀ σ : S7, σ.cycleType = {2,2,2} → ¬ ∀ k ∈ K, (k : S7) * σ = σ * k := by
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq A7 sylow P
  let e := MulAut.conj c
  have hP : (P : Subgroup A7) = sylowGroup.map e.toMonoidHom :=
    (congrArg Sylow.toSubgroup hc).symm
  let K := localGroup.map e.toMonoidHom
  refine ⟨K,?_,⟨(localGroup.equivMapOfInjective e.toMonoidHom e.injective).symm.trans localEquiv⟩,?_,?_⟩
  · rw [hP]
    exact map_mono sylowGroup_le_local
  · intro α hα
    let β := e⁻¹ * α * e
    have hβ : sylowGroup.map β.toMonoidHom = sylowGroup := by
      change sylowGroup.map (e.symm.toMonoidHom.comp (α.toMonoidHom.comp e.toMonoidHom)) = _
      rw [← map_map,← map_map,← hP,hα,hP,map_map]
      simp
    have hh := local_invariant_of_sylow_invariant β hβ
    have hx := congrArg (Subgroup.map e.toMonoidHom) hh
    have hecomp : e.toMonoidHom.comp β.toMonoidHom = α.toMonoidHom.comp e.toMonoidHom := by
      ext x
      dsimp [β]
      simp
    rw [map_map] at hx
    rw [hecomp,← map_map] at hx
    exact hx
  · intro σ hσ hfix
    apply local_not_centralizes_triple ((c : S7)⁻¹ * σ * (c : S7))
      (by simpa only [inv_inv] using (Perm.cycleType_conj (σ := σ) (τ := (c : S7)⁻¹)).trans hσ)
    intro k hk
    have hx := hfix (e k) (mem_map_of_mem e.toMonoidHom hk)
    change ((c : S7) * (k : S7) * (c : S7)⁻¹) * σ =
      σ * ((c : S7) * (k : S7) * (c : S7)⁻¹) at hx
    have hh := congrArg (fun x : S7 => (c : S7)⁻¹ * x * (c : S7)) hx
    convert hh using 1 <;> group


end AlternatingSevenSylowLocal

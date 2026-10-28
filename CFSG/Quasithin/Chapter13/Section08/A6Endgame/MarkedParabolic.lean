module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Models
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.GroupTheory.SylowKernelCore
import Mathlib.Tactic

/-!
# Normal subgroups of the marked point parabolic

In the concrete duad stabilizers `S₄` and `C₂ × S₄`, conjugating one
nonidentity four-letter permutation produces a nonidentity double
transposition. Its conjugates generate the Klein four subgroup. Consequently
a normal subgroup of `C₂ × S₄` of order greater than two contains this
particular four-group. It is the two-core of the embedded `A₄`, not the
whole eight-group two-core of the point stabilizer.

The transport lemmas require the image of the marked subgroup under an
actual multiplicative equivalence. Normality is relative to the parabolic.
The last conjugation is explicit, so a bound on `Vα*` cannot silently be
applied to `Vγ*`. We also prove the stronger order obstruction: a proper
normal extension of a normal subgroup of order two has order at least eight.

These are intrinsic calculations for the last paragraph of Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
printed pp. 968–969. Identifying the source's point stabilizer and its marked
`L₁` remains an explicit application premise; no such identification follows
from the order or dimension of an unrelated model.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame

open Subgroup Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.DuadCalculation

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem commutator_witness : ∀ b : Four, b ≠ 1 → ∃ g : Four,
    b * (g * b⁻¹ * g⁻¹) ∈ core ∧ b * (g * b⁻¹ * g⁻¹) ≠ 1 := by
  decide +kernel

private theorem core_le_normal (N : Subgroup Four) [N.Normal] (hne : N ≠ ⊥) :
    core ≤ N := by
  have hex : ∃ b ∈ N, b ≠ (1 : Four) := by
    by_contra! h
    apply hne
    exact le_antisymm (fun b hb => h b hb) bot_le
  obtain ⟨b, hb, hbone⟩ := hex
  obtain ⟨g, hc, hcne⟩ := commutator_witness b hbone
  have hcN := N.mul_mem hb ((inferInstance : N.Normal).conj_mem _ (N.inv_mem hb) g)
  intro y hy
  by_cases hyone : y = 1
  · subst y; exact N.one_mem
  obtain ⟨k, hk⟩ := core_conjugate _ hc hcne y hy hyone
  rw [← hk]
  exact (inferInstance : N.Normal).conj_mem _ hcN k

def markedFour : Subgroup DuadProduct := (⊥ : Subgroup Two).prod core

def markedA4 : Subgroup DuadProduct :=
  (⊥ : Subgroup Two).prod (alternatingGroup (Fin 4))

instance : markedFour.Normal := inferInstanceAs (((⊥ : Subgroup Two).prod core).Normal)
instance : markedA4.Normal :=
  inferInstanceAs (((⊥ : Subgroup Two).prod (alternatingGroup (Fin 4))).Normal)

theorem markedFour_le_of_normal_of_two_lt_card (N : Subgroup DuadProduct) [N.Normal]
    (hlarge : 2 < Nat.card N) : markedFour ≤ N := by
  have hn : ¬N ≤ centralFactor := by
    intro hn
    have hc := Subgroup.card_le_of_le hn
    rw [centralFactor_card] at hc
    omega
  obtain ⟨x, hx, hxnot⟩ := SetLike.not_le_iff_exists.mp hn
  have hxsnd : x.2 ≠ 1 := by
    intro he
    apply hxnot
    exact ⟨mem_top _, he⟩
  obtain ⟨g, hc, hcne⟩ := commutator_witness x.2 hxsnd
  have hcomm : (1, x.2 * (g * x.2⁻¹ * g⁻¹)) ∈ N := by
    have hh := N.mul_mem hx
      ((inferInstance : N.Normal).conj_mem _ (N.inv_mem hx) (1, g))
    change (x.1 * (1 * x.1⁻¹ * 1⁻¹), x.2 * (g * x.2⁻¹ * g⁻¹)) ∈ N at hh
    simpa only [one_mul, inv_one, mul_one, mul_inv_cancel] using hh
  intro y hy
  have hyfst : y.1 = 1 := hy.1
  by_cases hyone : y.2 = 1
  · have : y = 1 := Prod.ext hyfst hyone
    rw [this]; exact N.one_mem
  obtain ⟨k, hk⟩ := core_conjugate _ hc hcne y.2 hy.2 hyone
  have hh := (inferInstance : N.Normal).conj_mem _ hcomm (1, k)
  change (1 * 1 * 1⁻¹, k * (x.2 * (g * x.2⁻¹ * g⁻¹)) * k⁻¹) ∈ N at hh
  have he : (1, y.2) = y := Prod.ext hyfst.symm rfl
  simpa only [one_mul, inv_one, hk, he] using hh

theorem four_normal_card_ne_two (N : Subgroup Four) [N.Normal] : Nat.card N ≠ 2 := by
  intro hc
  have hne : N ≠ ⊥ := by
    intro he
    simp [he] at hc
  have h := Subgroup.card_le_of_le (core_le_normal N hne)
  rw [core_card, hc] at h
  omega

theorem markedA4_twoCore : markedA4.pCoreIn 2 = markedFour := by
  have hfour : markedFour ≤ productCore := prod_mono bot_le le_rfl
  have hsmall : markedFour ≤ markedA4 := by
    intro x hx
    exact ⟨hx.1, (core_mem_iff x.2).mp hx.2 |>.1⟩
  have hn : (markedA4.pCoreIn 2).Normal :=
    inferInstanceAs (((pCore 2 markedA4).map markedA4.subtype).Normal)
  have hpc : markedA4.pCoreIn 2 ≤ productCore := by
    rw [productCore_eq]
    exact le_sSup ⟨hn, isPGroup_pCoreIn 2 markedA4⟩
  apply le_antisymm
  · intro x hx
    exact ⟨(pCoreIn_le 2 markedA4 hx).1, (hpc hx).2⟩
  · exact le_pCoreIn_of_normalizes
      ((IsElementaryAbelian.isPGroup 2 productCore).to_le hfour) hsmall
      le_normalizer_of_normal

private theorem two_normal_le_central (U : Subgroup DuadProduct) [U.Normal]
    (hU : Nat.card U = 2) : U ≤ centralFactor := by
  by_contra hn
  obtain ⟨x, hx, hxnot⟩ := SetLike.not_le_iff_exists.mp hn
  have hxsnd : x.2 ≠ 1 := fun he => hxnot ⟨mem_top _, he⟩
  obtain ⟨g, hc, hcne⟩ := commutator_witness x.2 hxsnd
  have hcomm : (1, x.2 * (g * x.2⁻¹ * g⁻¹)) ∈ U := by
    have hh := U.mul_mem hx
      ((inferInstance : U.Normal).conj_mem _ (U.inv_mem hx) (1, g))
    change (x.1 * (1 * x.1⁻¹ * 1⁻¹), x.2 * (g * x.2⁻¹ * g⁻¹)) ∈ U at hh
    simpa only [one_mul, inv_one, mul_one, mul_inv_cancel] using hh
  have hfour : markedFour ≤ U := by
    intro y hy
    have hyfst : y.1 = 1 := hy.1
    by_cases hyone : y.2 = 1
    · have : y = 1 := Prod.ext hyfst hyone
      rw [this]; exact U.one_mem
    obtain ⟨k, hk⟩ := core_conjugate _ hc hcne y.2 hy.2 hyone
    have hh := (inferInstance : U.Normal).conj_mem _ hcomm (1, k)
    change (1 * 1 * 1⁻¹, k * (x.2 * (g * x.2⁻¹ * g⁻¹)) * k⁻¹) ∈ U at hh
    have he : (1, y.2) = y := Prod.ext hyfst.symm rfl
    simpa only [one_mul, inv_one, hk, he] using hh
  have hcard : Nat.card markedFour = 4 := by
    change Nat.card ((⊥ : Subgroup Two).prod core) = 4
    rw [Nat.card_congr ((⊥ : Subgroup Two).prodEquiv core).toEquiv,
      Nat.card_prod, Subgroup.card_bot, core_card, one_mul]
  have := Subgroup.card_le_of_le hfour
  omega

/-- A strict normal extension of the invariant line contains the entire
two-core of the point parabolic, hence every relatively normal marked core. -/
theorem twoCore_le_of_strict_normal_pair (U V : Subgroup DuadProduct)
    [U.Normal] [V.Normal] (hU : Nat.card U = 2) (hlt : U < V) :
    pCore 2 DuadProduct ≤ V := by
  have hUc : U = centralFactor := Subgroup.eq_of_le_of_card_ge
    (two_normal_le_central U hU) (by rw [hU, centralFactor_card])
  have hlarge : 2 < Nat.card V := by
    by_contra! h
    have he := Subgroup.eq_of_le_of_card_ge hlt.le (by rw [hU]; exact h)
    exact hlt.ne he
  have hfour := markedFour_le_of_normal_of_two_lt_card V hlarge
  have hcore : productCore ≤ V := by
    intro x hx
    have ha : (x.1, 1) ∈ V := hlt.le (by rw [hUc]; exact ⟨mem_top _, rfl⟩)
    have hb : (1, x.2) ∈ V := hfour ⟨rfl, hx.2⟩
    simpa using V.mul_mem ha hb
  rwa [productCore_eq] at hcore

theorem eight_le_card_of_strict_normal_pair (U V : Subgroup DuadProduct) [U.Normal] [V.Normal]
    (hU : Nat.card U = 2) (hlt : U < V) : 8 ≤ Nat.card V := by
  have hcore := twoCore_le_of_strict_normal_pair U V hU hlt
  rw [← productCore_eq] at hcore
  have := Subgroup.card_le_of_le hcore
  rwa [productCore_card] at this

theorem marked_core_le_of_model {P : Type*} [Group P] (e : P ≃* DuadProduct)
    (J U V : Subgroup P) [V.Normal] (hmark : J.map e.toMonoidHom = markedA4)
    (hU : Nat.card U = 2) (hlt : U < V) : J.pCoreIn 2 ≤ V := by
  let : Finite P := Finite.of_equiv DuadProduct e.symm.toEquiv
  have hlarge : 2 < Nat.card V := by
    by_contra! h
    have he := Subgroup.eq_of_le_of_card_ge hlt.le (by rw [hU]; exact h)
    exact hlt.ne he
  let N := V.map e.toMonoidHom
  have : N.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  have hn : 2 < Nat.card N := by
    simpa only [N, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] using hlarge
  have hc := markedFour_le_of_normal_of_two_lt_card N hn
  have hmap : (J.pCoreIn 2).map e.toMonoidHom ≤ V.map e.toMonoidHom := by
    rw [map_pCoreIn_of_injective 2 J _ e.injective, hmark, markedA4_twoCore]
    exact hc
  intro x hx
  obtain ⟨y, hy, he⟩ := hmap (mem_map.mpr ⟨x, hx, rfl⟩)
  exact e.injective he ▸ hy

theorem eight_le_card_of_normal_pair_model {P : Type*} [Group P]
    (model : Nonempty (P ≃* Four) ∨ Nonempty (P ≃* DuadProduct))
    (U V : Subgroup P) [U.Normal] [V.Normal]
    (hU : Nat.card U = 2) (hlt : U < V) : 8 ≤ Nat.card V := by
  rcases model with h | h
  · obtain ⟨e⟩ := h
    have : (U.map e.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ e.surjective
    exact (four_normal_card_ne_two (U.map e.toMonoidHom)
      ((Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).trans hU)).elim
  · obtain ⟨e⟩ := h
    have : (U.map e.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ e.surjective
    have : (V.map e.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ e.surjective
    have hh := eight_le_card_of_strict_normal_pair (U.map e.toMonoidHom) (V.map e.toMonoidHom)
      ((Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).trans hU)
      (e.mapSubgroup.strictMono hlt)
    simpa only [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] using hh

theorem marked_core_le_of_relative_normality {G : Type*} [Group G] (P J U V : Subgroup G)
    (e : P ≃* DuadProduct) (hJP : J ≤ P) (hVP : V ≤ P)
    (hmark : (J.subgroupOf P).map e.toMonoidHom = markedA4)
    (hnorm : P ≤ normalizer (V : Set G))
    (hU : Nat.card U = 2) (hlt : U < V) : J.pCoreIn 2 ≤ V := by
  have : (V.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVP).mpr hnorm
  have hUP : U ≤ P := hlt.le.trans hVP
  have hU' : Nat.card (U.subgroupOf P) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv).trans hU
  have hlt' : U.subgroupOf P < V.subgroupOf P := by
    apply lt_of_le_of_ne
    · intro x hx
      exact hlt.le hx
    · intro he
      have := congrArg (Subgroup.map P.subtype) he
      rw [map_subgroupOf_eq_of_le hUP, map_subgroupOf_eq_of_le hVP] at this
      exact hlt.ne this
  have hh := marked_core_le_of_model e (J.subgroupOf P) (U.subgroupOf P) (V.subgroupOf P)
    hmark hU' hlt'
  have hm := Subgroup.map_mono (f := P.subtype) hh
  rwa [map_pCoreIn_of_injective 2 _ _ P.subtype_injective,
    map_subgroupOf_eq_of_le hJP, map_subgroupOf_eq_of_le hVP] at hm

theorem marked_conjugate_contradiction {G : Type*} [Group G]
    (P J Ug Vg Va : Subgroup G) (c : G) (e : P ≃* DuadProduct)
    (hJP : J ≤ P) (hVP : Vg ≤ P)
    (hmark : (J.subgroupOf P).map e.toMonoidHom = markedA4)
    (hnorm : P ≤ normalizer (Vg : Set G))
    (hU : Nat.card Ug = 2) (hlt : Ug < Vg)
    (hVa : Vg.map (MulAut.conj c).toMonoidHom = Va)
    (hnot : ¬(J.map (MulAut.conj c).toMonoidHom).pCoreIn 2 ≤ Va) : False := by
  apply hnot
  have hm := Subgroup.map_mono (f := (MulAut.conj c).toMonoidHom)
    (marked_core_le_of_relative_normality P J Ug Vg e hJP hVP hmark hnorm hU hlt)
  rwa [map_pCoreIn_of_injective 2 J _ (MulAut.conj c).injective, hVa] at hm

theorem eight_le_card_of_duad_models {P : Type*} [Group P]
    (model : Nonempty (P ≃* a6DuadStabilizer) ∨ Nonempty (P ≃* duadStabilizer))
    (U V : Subgroup P) [U.Normal] [V.Normal]
    (hU : Nat.card U = 2) (hlt : U < V) : 8 ≤ Nat.card V := by
  apply eight_le_card_of_normal_pair_model _ U V hU hlt
  rcases model with h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨e.trans a6DuadModelEquiv.symm⟩
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨e.trans duadProductEquiv.symm⟩

theorem eight_le_card_of_relative_normal_pair {G : Type*} [Group G] (P U V : Subgroup G)
    (model : Nonempty (P ≃* a6DuadStabilizer) ∨ Nonempty (P ≃* duadStabilizer))
    (hVP : V ≤ P) (hUn : P ≤ normalizer (U : Set G))
    (hVn : P ≤ normalizer (V : Set G))
    (hU : Nat.card U = 2) (hlt : U < V) : 8 ≤ Nat.card V := by
  have hUP : U ≤ P := hlt.le.trans hVP
  have : (U.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUP).mpr hUn
  have : (V.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVP).mpr hVn
  have hU' : Nat.card (U.subgroupOf P) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv).trans hU
  have hlt' : U.subgroupOf P < V.subgroupOf P := by
    apply lt_of_le_of_ne
    · intro x hx
      exact hlt.le hx
    · intro he
      have := congrArg (Subgroup.map P.subtype) he
      rw [map_subgroupOf_eq_of_le hUP, map_subgroupOf_eq_of_le hVP] at this
      exact hlt.ne this
  have hh := eight_le_card_of_duad_models model (U.subgroupOf P) (V.subgroupOf P) hU' hlt'
  rwa [Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv] at hh

theorem no_small_relative_normal_pair {G : Type*} [Group G] (P U V : Subgroup G)
    (model : Nonempty (P ≃* a6DuadStabilizer) ∨ Nonempty (P ≃* duadStabilizer))
    (hVP : V ≤ P) (hUn : P ≤ normalizer (U : Set G))
    (hVn : P ≤ normalizer (V : Set G))
    (hU : Nat.card U = 2) (hlt : U < V) (hV : Nat.card V ≤ 4) : False := by
  have := eight_le_card_of_relative_normal_pair P U V model hVP hUn hVn hU hlt
  omega

end CFSG.Quasithin.Chapter13.Section08.A6Endgame

module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# Intrinsic reductions for the swapped-component case

The complement is already identified with X/O₂(X) by `Embeddings.Reduction`.
If it is abelian, the extraspecial alternative is impossible and finite vector
space coordinates identify it with the actual plane E_(p²). The normality of
C-components inside their layer and the Frattini factorization of T produce an
element of N_T(P) that moves L. Finally the image of Φ(N_T(P)) cannot act
trivially, so Φ(Aut_T(P)) is nontrivial.

These deductions use no Sylow hypothesis on T in H. `SwappedInput` records
the task's given local hypotheses, not an embedding or classification result.
The conjugate product and model restrictions of 1.3.4(1) are not proved here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed pp.509–510.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G]

/-- The intrinsic local and component witnesses supplied to the swapped case. -/
structure SwappedInput (𝒦 : GroupClass.{u}) (p : ℕ) (T X P H L : Subgroup G)
    extends LocalInput p T X P H where
  sqtk : IsSQTK 𝒦 H
  component : L ∈ cComponentsIn H
  quasisimple : IsQuasisimple (XiQuotient L)
  orbit_normal : ((componentOrbit L T).subgroupOf H).Normal
  complement_le_orbit : P ≤ componentOrbit L T
  orbit_commutator : ⁅componentOrbit L T, P⁆ = componentOrbit L T
  noncentral : ¬ ⁅L, P⁆ ≤ L.pCoreIn 2
  not_invariant : ¬ T ≤ normalizer L

variable {p : ℕ} {T X P H L : Subgroup G}

/-- The chosen complement lies in X. -/
theorem LocalInput.complement_le (h : LocalInput p T X P H) : P ≤ X :=
  le_sup_right.trans_eq h.complement

/-- The normalizer factorization places O₂(X) inside T. -/
theorem LocalInput.core_le_two_group (h : LocalInput p T X P H) : X.pCoreIn 2 ≤ T :=
  le_sup_left.trans_eq h.normalizer_factor.symm

/-- An abelian complement has the elementary, rather than extraspecial, quotient type. -/
theorem LocalInput.complement_elementary_of_commutative
    (h : LocalInput p T X P H) (hc : IsMulCommutative P) :
    IsElementaryAbelian p P ∧ Nat.card P = p ^ 2 := by
  rcases h.odd_complement with he | ⟨he, _, _⟩
  · exact he
  · let _ := hc
    exact ((QuotientGroup.nontrivial_iff.mp he.quotient_nontrivial)
      (center_eq_top (G := P))).elim

/-- Finite vector space coordinates supply the actual plane isomorphism. -/
theorem LocalInput.complement_plane_of_commutative [Finite G]
    (h : LocalInput p T X P H) (hc : IsMulCommutative P) : Nonempty (P ≃* Plane p) := by
  classical
  let _ : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨he, hcard⟩ := h.complement_elementary_of_commutative hc
  let _ := he
  have hpow : p ^ Module.finrank (ZMod p) (Additive P) = p ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive P)
    change Nat.card P = _ at hsize
    simpa only [Nat.card_zmod, hcard] using hsize.symm
  have hdim : Module.finrank (ZMod p) (Additive P) = 2 :=
    Nat.pow_right_injective h.prime.one_lt hpow
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive P) hdim
  exact ⟨b.equivFun.toAddEquiv.toMultiplicativeRight⟩

/-- All T-conjugates of a relative C-component normalize it inside H. -/
theorem cComponentOrbit_le_normalizer [Finite G] (hL : L ∈ cComponentsIn H)
    (hT : T ≤ H) : componentOrbit L T ≤ normalizer L := by
  let D := (cComponentLayer H).map H.subtype
  have hDN : D ≤ normalizer L := by
    have hh := map_mono (f := H.subtype) (cComponentLayer_le_normalizer hL.2)
    have hn := (L.subgroupOf H).le_normalizer_map H.subtype
    rw [map_subgroupOf_eq_of_le hL.1] at hn
    exact hh.trans hn
  apply le_trans ?_ hDN
  apply iSup_le
  intro t
  rintro x ⟨l, hl, rfl⟩
  exact mem_map_of_mem H.subtype
    (le_cComponentLayer (hL.2.map_equiv (MulAut.conj (⟨t, hT t.property⟩ : H)))
      (mem_map_of_mem (MulAut.conj (⟨t, hT t.property⟩ : H)).toMonoidHom
        (show (⟨l, hL.1 hl⟩ : H) ∈ L.subgroupOf H from hl)))

/-- A moving element can be chosen in the actual normalizer N_T(P). -/
theorem SwappedInput.exists_swap [Finite G] {𝒦 : GroupClass.{u}}
    (h : SwappedInput 𝒦 p T X P H L) :
    ∃ t : G, t ∈ T ⊓ normalizer P ∧ t ∉ normalizer L := by
  have hTH : T ≤ H := le_sup_right.trans h.overgroup
  have hKH : componentOrbit L T ≤ H :=
    (componentOrbit_le_sup L T).trans (sup_le h.component.1 hTH)
  have hHN : H ≤ normalizer (componentOrbit L T) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp h.orbit_normal
  have hXK := h.toLocalInput.le_of_complement_le h.complement_le_orbit hHN
  have hcoreN : X.pCoreIn 2 ≤ normalizer L :=
    (pCoreIn_le 2 X).trans (hXK.trans (cComponentOrbit_le_normalizer h.component hTH))
  by_contra! hn
  exact h.not_invariant (h.normalizer_factor ▸ sup_le hcoreN hn)

/-- The actual automizer induced by T is a two-group. -/
theorem LocalInput.automizer_isPGroup (h : LocalInput p T X P H) :
    IsPGroup 2 (automizer T P) := by
  let f := P.normalizerMonoidHom.comp (inclusion (show T ⊓ normalizer P ≤ normalizer P from
    inf_le_right))
  exact h.two_group.to_inf_left.of_surjective f.rangeRestrict f.rangeRestrict_surjective

/-- The source Frattini commutator identity survives passage to the action image. -/
theorem LocalInput.frattini_automizer_ne_bot [Finite G] (h : LocalInput p T X P H) :
    frattini (automizer T P) ≠ ⊥ := by
  let S := T ⊓ normalizer P
  let f : S →* MulAut P := P.normalizerMonoidHom.comp (inclusion inf_le_right)
  intro hbot
  have hcentral : (frattini S).map S.subtype ≤ centralizer (P : Set G) := by
    rintro x ⟨s, hs, rfl⟩
    have him := frattini_le_comap_frattini_of_surjective f.rangeRestrict_surjective hs
    have he : f.rangeRestrict s = 1 := by
      change f.rangeRestrict s ∈ (⊥ : Subgroup (automizer T P))
      rw [← hbot]
      exact him
    have hker : (inclusion (show S ≤ normalizer P from inf_le_right)) s ∈
        P.normalizerMonoidHom.ker := congrArg Subtype.val he
    rw [normalizerMonoidHom_ker] at hker
    exact hker
  have hcomm : ⁅P, (frattini S).map S.subtype⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hcentral
  have hPbot : P = ⊥ := h.frattini_commutator.trans hcomm
  apply h.complement_not_cyclic
  rw [hPbot]
  infer_instance

/-- In particular, the induced two-group is not elementary abelian. -/
theorem LocalInput.automizer_not_elementary [Finite G] (h : LocalInput p T X P H) :
    ¬ IsElementaryAbelian 2 (automizer T P) := by
  intro he
  let _ := he
  let _ : Fact (IsPGroup 2 (automizer T P)) := ⟨h.automizer_isPGroup⟩
  exact h.frattini_automizer_ne_bot (frattini_eq_bot_of_isElementaryAbelian (p := 2))

end CFSG.Quasithin.Chapter1.XiEmbedding

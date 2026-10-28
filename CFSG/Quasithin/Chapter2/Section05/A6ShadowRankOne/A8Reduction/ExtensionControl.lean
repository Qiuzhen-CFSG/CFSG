module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.A8Reduction.Local

/-!
# Comparing the centralizer with the marked symmetric extension

An element of C_S(i) normalizes Ki by the quasithin A₆ obstruction and
commutes with t. Its automorphism of A₈ therefore commutes with the marked
transposition. Given a lift of this automorphism to a permutation commuting
with the transposition, the marked H₀ model supplies an element y of H₀∩H
with the same action on Ki. The discrepancy y⁻¹s centralizes K. The genuine
conjugation kernel in H places it in SC, and C_SC(i)=⟨i,t⟩ places it in H₀.

The only remaining model premises are the marked H₀ carrier and the
explicit automorphism-lifting theorem for A₈. They are independent tasks;
this conditional comparison does not claim either is constructed.

Source: Aschbacher–Smith, Lemma 2.5.26, printed pp.568–569 of the combined
1 March 2004 manuscript, the assertion Ki C_S(i) ≃ C₂ × S₈.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne.A8Reduction
variable {G : Type*} [Group G]

private theorem centralizes_K_mem_core (d : LocalData G) {a : G}
    (ha : a ∈ d.H) (hc : a ∈ centralizer (d.K : Set G)) : a ∈ d.SC := by
  have he : d.action ⟨a, ha⟩ = 1 := by
    apply MulEquiv.ext
    intro k
    apply d.modelK.symm.injective
    apply Subtype.ext
    have hh := d.action_compatible ⟨a, ha⟩ (d.modelK.symm k)
    simpa only [MulEquiv.apply_symm_apply, MulAut.one_apply, ← hc _ (d.modelK.symm k).property,
      mul_inv_cancel_right] using hh
  have hk : (⟨a, ha⟩ : d.H) ∈ d.action.ker := he
  rw [d.action_kernel] at hk
  exact hk

private theorem core_centralizer_mem_small (d : LocalData G) {a : G}
    (ha : a ∈ d.SC) (hc : a ∈ centralizer ({d.i} : Set G)) : a ∈ d.smallExtension := by
  have hci : (⟨a, ha⟩ : d.SC) ∈ centralizer ({(⟨d.i, d.i_mem⟩ : d.SC)} : Set d.SC) := by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hc)
  rw [d.centralizer_i] at hci
  have hmap : (zpowers (⟨d.i, d.i_mem⟩ : d.SC) ⊔ zpowers (⟨d.t, d.t_mem⟩ : d.SC)).map
      d.SC.subtype ≤ d.smallExtension := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  exact hmap (mem_map_of_mem _ hci)

variable [Finite G]
private theorem normalized_action (d : LocalData G) (hG : IsQuasithin G)
    {s : G} (hs : s ∈ d.S ⊓ centralizer {d.i}) :
    ∃ f : MulAut (alternatingGroup (Fin 8)),
      (∀ k, (d.modelKi.symm (f k) : G) = s * (d.modelKi.symm k : G) * s⁻¹) ∧
      Commute f (MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1)) := by
  let f := (d.modelKi.symm.trans
    (d.Ki.normalizerMonoidHom ⟨s, d.Ki_normalizer hG hs.2⟩)).trans d.modelKi
  have hf (k : alternatingGroup (Fin 8)) :
      (d.modelKi.symm (f k) : G) = s * (d.modelKi.symm k : G) * s⁻¹ := by
    simp only [f, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  refine ⟨f, hf, ?_⟩
  have ht (k : alternatingGroup (Fin 8)) :
      (d.modelKi.symm (MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1) k) : G) =
        d.t * (d.modelKi.symm k : G) * d.t⁻¹ := by
    simpa only [MulEquiv.apply_symm_apply] using d.t_action (d.modelKi.symm k)
  have hst : s * d.t = d.t * s := d.t_central s hs.1
  show f * MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1) =
    MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1) * f
  apply MulEquiv.ext
  intro k
  apply d.modelKi.symm.injective
  apply Subtype.ext
  change (d.modelKi.symm (f (MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1) k)) : G) =
    (d.modelKi.symm (MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1) (f k)) : G)
  rw [hf, ht, ht, hf]
  calc
    s * (d.t * (d.modelKi.symm k : G) * d.t⁻¹) * s⁻¹ =
        (s * d.t) * (d.modelKi.symm k : G) * (s * d.t)⁻¹ := by group
    _ = (d.t * s) * (d.modelKi.symm k : G) * (d.t * s)⁻¹ := by rw [hst]
    _ = d.t * (s * (d.modelKi.symm k : G) * s⁻¹) * d.t⁻¹ := by group


omit [Finite G] in
private theorem marked_lift (d : LocalData G) (m : SmallExtensionModel d)
    (q : Equiv.Perm (Fin 8)) (hq : Commute q (Equiv.swap (0 : Fin 8) 1)) :
    ∃ y : d.smallExtension, (y : G) ∈ d.H ∧ (y : G) ∈ centralizer ({d.i} : Set G) ∧
      ∀ k : d.Ki, (y : G) * k * (y : G)⁻¹ =
        (d.modelKi.symm (MulAut.conjNormal q (d.modelKi k)) : G) := by
  let y := m.equiv.symm (1, q)
  let iJ : d.smallExtension := ⟨d.i, mem_sup_left (mem_sup_right (mem_zpowers d.i))⟩
  let tJ : d.smallExtension := ⟨d.t, mem_sup_right (mem_zpowers d.t)⟩
  let kJ (k : d.Ki) : d.smallExtension := ⟨k, mem_sup_left (mem_sup_left k.property)⟩
  have hy : m.equiv y = (1, q) := m.equiv.apply_symm_apply _
  have hi : m.equiv iJ = (Multiplicative.ofAdd 1, 1) := m.map_i iJ rfl
  have ht : m.equiv tJ = (1, Equiv.swap (0 : Fin 8) 1) := m.map_t tJ rfl
  have hyt : Commute y tJ := by
    apply m.equiv.injective
    simp only [map_mul, hy, ht]
    exact Prod.ext (by simp) hq.eq
  have hyi : Commute y iJ := by
    apply m.equiv.injective
    simp only [map_mul, hy, hi, Prod.mk_mul_mk, one_mul, mul_one]
  refine ⟨y, ?_, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hyi.eq), ?_⟩
  · rw [d.centralizer_t, mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hyt.eq
  · intro k
    let w := d.modelKi.symm (MulAut.conjNormal q (d.modelKi k))
    have hj : y * kJ k * y⁻¹ = kJ w := by
      apply m.equiv.injective
      simp only [map_mul, map_inv, hy, m.map_Ki k (kJ k) rfl, m.map_Ki w (kJ w) rfl]
      dsimp only [w]
      rw [MulEquiv.apply_symm_apply]
      apply Prod.ext
      · simp
      · rfl
    exact congrArg Subtype.val hj

/-- Only the concrete automorphism lifting remains in the centralizer comparison. -/
theorem centralizer_le_smallExtension_of_lifting (d : LocalData G) (hG : IsQuasithin G)
    (m : SmallExtensionModel d)
    (hlift : ∀ f : MulAut (alternatingGroup (Fin 8)),
      Commute f (MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1)) →
      ∃ q : Equiv.Perm (Fin 8), Commute q (Equiv.swap (0 : Fin 8) 1) ∧
        MulAut.conjNormal q = f) :
    d.S ⊓ centralizer {d.i} ≤ d.smallExtension := by
  intro s hs
  obtain ⟨f, hf, hft⟩ := normalized_action d hG hs
  obtain ⟨q, hq, hqf⟩ := hlift f hft
  obtain ⟨y, hyH, hyi, hyK⟩ := marked_lift d m q hq
  let c : G := (y : G)⁻¹ * s
  have hcH : c ∈ d.H := d.H.mul_mem (d.H.inv_mem hyH) (d.s_le_h hs.1)
  have hci : c ∈ centralizer ({d.i} : Set G) :=
    (centralizer _).mul_mem ((centralizer _).inv_mem hyi) hs.2
  have hconj (k : d.Ki) : s * k * s⁻¹ = (y : G) * k * (y : G)⁻¹ := by
    have h := hyK k
    rw [hqf] at h
    have hh := hf (d.modelKi k)
    rw [MulEquiv.symm_apply_apply] at hh
    exact hh.symm.trans h.symm
  have hcK : c ∈ centralizer (d.K : Set G) := by
    intro k hk
    have he : c * k * c⁻¹ = k := by
      calc
        c * k * c⁻¹ = (y : G)⁻¹ * (s * k * s⁻¹) * y := by dsimp [c]; group
        _ = (y : G)⁻¹ * ((y : G) * k * (y : G)⁻¹) * y := by
          rw [hconj ⟨k, d.K_le_Ki hk⟩]
        _ = k := by group
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hcSC := centralizes_K_mem_core d hcH hcK
  have hcSmall := core_centralizer_mem_small d hcSC hci
  have hm := d.smallExtension.mul_mem y.property hcSmall
  simpa only [c, mul_inv_cancel_left] using hm

end CFSG.Quasithin.Chapter2.A6ShadowRankOne.A8Reduction

module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FixedGeometry
public import Theory.GroupTheory.DisjointCommutingProduct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-!
# Quotient coordinates from the factor modules

The direct-product decomposition of the moved module induces a decomposition
of its fixed subgroup when each factor is invariant under the actor. The
fixed-free moved summand identifies the printed `E_Y` with `C_E(Y)`.
For a single fixed line, multiplication and cardinality give index two.
For two fixed lines, multiplication gives an actual surjective homomorphism
from `E` onto two binary coordinates. Its kernel is exactly `C_E(Y)`.
Conjugation interchanging the factors interchanges these coordinates because
a group of order two has only one nonidentity element.

The omega-subgroup adapter proves the fixed-subgroup splitting, centralizer
identity, and quotient construction. The absence of `Y`-fixed vectors in the
moved module follows from its disjointness from the printed fixed summand.
Its inputs about fixed-line orders and conjugation permuting the module
factors remain to be realized from the full preceding source witnesses.
There is no assumed hyperplane in `Z`, and no replacement definition of the
source families `Ξ` or `𝒴`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, 15.4.12(5–6) and the first sentence of the proof of
15.4.14, printed pp.1160–1161.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors
variable {G : Type*} [Group G]

private theorem binary_eq_of_one_iff (a b : Multiplicative (ZMod 2))
    (h : a = 1 ↔ b = 1) : a = b := by
  revert a b
  decide

/-- Identify the fixed summand using its complement's fixed-point-free action. -/
theorem fixed_summand_eq_centralizer {E C F Y : Subgroup G}
    (hE : C ⊔ F = E) (hcomm : C ≤ centralizer (F : Set G))
    (hC : C ≤ centralizer (Y : Set G))
    (hF : F ⊓ centralizer (Y : Set G) = ⊥) :
    E ⊓ centralizer (Y : Set G) = C := by
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (C : Set G) * (F : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right C F
        (hcomm.trans (Subgroup.centralizer_le_normalizer _))]
      exact hE.symm ▸ hx.1
    obtain ⟨c, hc, f, hf, rfl⟩ := hxprod
    have hfC : f ∈ centralizer (Y : Set G) := by
      simpa only [inv_mul_cancel_left] using
        (centralizer (Y : Set G)).mul_mem ((centralizer (Y : Set G)).inv_mem (hC hc)) hx.2
    have hf1 : f = 1 := mem_bot.mp (hF ▸ (show f ∈ F ⊓ centralizer (Y : Set G) from ⟨hf, hfC⟩))
    change c * f ∈ C
    rw [hf1, mul_one]
    exact hc
  · exact le_inf (hE ▸ le_sup_left) hC

/-- A fixed complement of order two gives the single-factor coordinate
alternative, with the index computed in `E` rather than in the ambient group. -/
theorem centralizer_index_two_of_fixed_complement [Finite G]
    {E C F Y : Subgroup G}
    (hE : C ⊔ F = E) (hcomm : C ≤ centralizer (F : Set G))
    (hC : C ≤ centralizer (Y : Set G))
    (hF : F ⊓ centralizer (Y : Set G) = ⊥) (hcard : Nat.card F = 2) :
    (E ⊓ centralizer (Y : Set G)).relIndex E = 2 := by
  have hfix := fixed_summand_eq_centralizer hE hcomm hC hF
  have hd : Disjoint C F := disjoint_iff.mpr (le_bot_iff.mp (by
    intro x hx
    exact hF.le ⟨hx.2, hC hx.1⟩))
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C F hd hcomm
  have hc : Nat.card E = Nat.card C * 2 := by
    rw [← hE, ← Nat.card_congr e.toEquiv, Nat.card_prod, hcard]
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) C E bot_le (hE ▸ le_sup_left)
  rw [relIndex_bot_left, relIndex_bot_left, hc] at hi
  rw [hfix]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hi

/-- Construct quotient coordinates from three actual internal factors. -/
theorem swappedBinaryQuotient_of_internal_factors
    {E T Y C F₁ F₂ : Subgroup G}
    (hE : C ⊔ (F₁ ⊔ F₂) = E)
    (hd₀ : Disjoint C (F₁ ⊔ F₂)) (hd₁₂ : Disjoint F₁ F₂)
    (hc₀ : C ≤ centralizer ((F₁ ⊔ F₂ : Subgroup G) : Set G))
    (hc₁₂ : F₁ ≤ centralizer (F₂ : Set G))
    (hC : E ⊓ centralizer (Y : Set G) = C)
    (hcard₁ : Nat.card F₁ = 2) (hcard₂ : Nat.card F₂ = 2)
    (t : G) (ht : t ∈ T) (hnE : t ∈ normalizer (E : Set G))
    (hnC : t ∈ normalizer (C : Set G))
    (hs₁ : F₁.map (MulAut.conj t).toMonoidHom = F₂)
    (hs₂ : F₂.map (MulAut.conj t).toMonoidHom = F₁) :
    Nonempty (SwappedBinaryQuotient E T Y) := by
  classical
  obtain ⟨e₁₂, he₁₂⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting F₁ F₂ hd₁₂ hc₁₂
  obtain ⟨e₀, he₀⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C (F₁ ⊔ F₂) hd₀ hc₀
  let e : C × (F₁ × F₂) ≃* E :=
    (MulEquiv.prodCongr (MulEquiv.refl C) e₁₂).trans
      (e₀.trans (MulEquiv.subgroupCongr hE))
  have he (c : C) (a : F₁) (b : F₂) : (e (c, (a, b)) : G) = c * ((a : G) * b) := by
    change (e₀ (c, e₁₂ (a, b)) : G) = _
    rw [he₀, he₁₂]
  let f₁ : F₁ ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hcard₁ (by simp)
  let f₂ : F₂ ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hcard₂ (by simp)
  let q : E →* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    (f₁.prodCongr f₂).toMonoidHom.comp ((MonoidHom.snd C (F₁ × F₂)).comp e.symm.toMonoidHom)
  have hq (c : C) (a : F₁) (b : F₂) : q (e (c, (a, b))) = (f₁ a, f₂ b) := by
    change (f₁ (e.symm (e (c, (a, b)))).2.1, f₂ (e.symm (e (c, (a, b)))).2.2) = _
    rw [e.symm_apply_apply]
  have hsurj : Function.Surjective q := by
    intro x
    exact ⟨e (1, (f₁.symm x.1, f₂.symm x.2)), by simp only [hq, f₁.apply_symm_apply, f₂.apply_symm_apply]⟩
  have hkerC (x : E) : q x = 1 ↔ (x : G) ∈ C := by
    obtain ⟨⟨c, a, b⟩, rfl⟩ := e.surjective x
    rw [hq]
    constructor
    · intro hx
      have ha : a = 1 := f₁.map_eq_one_iff.mp (congrArg Prod.fst hx)
      have hb : b = 1 := f₂.map_eq_one_iff.mp (congrArg Prod.snd hx)
      rw [he, ha, hb]
      simp only [OneMemClass.coe_one, mul_one]
      exact c.property
    · intro hx
      have hh : e (c, (a, b)) = e (⟨_, hx⟩, (1, 1)) := by
        apply Subtype.ext
        rw [he (⟨_, hx⟩ : C) 1 1]
        simp
      have hprod := e.injective hh
      have ha : a = 1 := congrArg (fun x => x.2.1) hprod
      have hb : b = 1 := congrArg (fun x => x.2.2) hprod
      simp [ha, hb]
  have hk : q.ker = (centralizer (Y : Set G)).subgroupOf E := by
    ext x
    change q x = 1 ↔ (x : G) ∈ centralizer (Y : Set G)
    rw [hkerC, ← hC]
    exact and_iff_right x.property
  refine ⟨⟨q, hsurj, hk, t, ht, hnE, ?_⟩⟩
  intro x
  obtain ⟨⟨c, a, b⟩, rfl⟩ := e.surjective x
  let c' : C := ⟨t * (c : G) * t⁻¹, (mem_normalizer_iff.mp hnC c).mp c.property⟩
  let a' : F₂ := ⟨(MulAut.conj t) a, hs₁ ▸ mem_map.mpr ⟨a, a.property, rfl⟩⟩
  let b' : F₁ := ⟨(MulAut.conj t) b, hs₂ ▸ mem_map.mpr ⟨b, b.property, rfl⟩⟩
  have hc : (⟨t * (e (c, (a, b)) : G) * t⁻¹,
      (mem_normalizer_iff.mp hnE _).mp (e (c, (a, b))).property⟩ : E) =
      e (c', (b', a')) := by
    apply Subtype.ext
    change t * (e (c, (a, b)) : G) * t⁻¹ = (e (c', (b', a')) : G)
    rw [he, he]
    change (MulAut.conj t) ((c : G) * ((a : G) * b)) =
      (MulAut.conj t) c * ((MulAut.conj t) b * (MulAut.conj t) a)
    rw [map_mul, map_mul]
    congr 1
    simpa only [map_mul] using congrArg (MulAut.conj t) ((hc₁₂ a.property b b.property).symm)
  have hab : f₂ a' = f₁ a := binary_eq_of_one_iff _ _ (by
    rw [f₂.map_eq_one_iff, f₁.map_eq_one_iff]
    change (⟨(MulAut.conj t) a, _⟩ : F₂) = 1 ↔ a = 1
    simp only [Subtype.ext_iff, OneMemClass.coe_one]
    exact (MulAut.conj t).map_eq_one_iff)
  have hba : f₁ b' = f₂ b := binary_eq_of_one_iff _ _ (by
    rw [f₁.map_eq_one_iff, f₂.map_eq_one_iff]
    change (⟨(MulAut.conj t) b, _⟩ : F₁) = 1 ↔ b = 1
    simp only [Subtype.ext_iff, OneMemClass.coe_one]
    exact (MulAut.conj t).map_eq_one_iff)
  rw [hc, hq, hq, hab, hba]

/-- The fixed subgroup of an invariant internal direct product splits in the
same factors. Normality is relative to the actor subgroup. -/
theorem fixed_subgroup_split_of_internal_factors {A B S : Subgroup G}
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G))
    (hnA : S ≤ normalizer (A : Set G)) (hnB : S ≤ normalizer (B : Set G)) :
    (A ⊔ B) ⊓ centralizer (S : Set G) =
      (A ⊓ centralizer (S : Set G)) ⊔ (B ⊓ centralizer (S : Set G)) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨a, b⟩, heq⟩ := e.surjective ⟨x, hx.1⟩
    have hab : (a : G) * b = x := (he a b).symm.trans (congrArg Subtype.val heq)
    have hfix (s : G) (hs : s ∈ S) :
        s * (a : G) * s⁻¹ = a ∧ s * (b : G) * s⁻¹ = b := by
      let a' : A := ⟨s * (a : G) * s⁻¹, (mem_normalizer_iff.mp (hnA hs) a).mp a.property⟩
      let b' : B := ⟨s * (b : G) * s⁻¹, (mem_normalizer_iff.mp (hnB hs) b).mp b.property⟩
      have he' : e (a', b') = e (a, b) := by
        apply Subtype.ext
        rw [he, he]
        change (MulAut.conj s) a * (MulAut.conj s) b = (a : G) * b
        rw [← map_mul, hab, MulAut.conj_apply,
          (mem_centralizer_iff.mp hx.2 s hs), mul_inv_cancel_right]
      have hp := e.injective he'
      exact ⟨congrArg (fun p => (p.1 : G)) hp, congrArg (fun p => (p.2 : G)) hp⟩
    have ha : (a : G) ∈ centralizer (S : Set G) := by
      apply mem_centralizer_iff.mpr
      intro s hs
      exact (mul_inv_eq_iff_eq_mul.mp (hfix s hs).1)
    have hb : (b : G) ∈ centralizer (S : Set G) := by
      apply mem_centralizer_iff.mpr
      intro s hs
      exact (mul_inv_eq_iff_eq_mul.mp (hfix s hs).2)
    exact hab ▸ mul_mem_sup ⟨a.property, ha⟩ ⟨b.property, hb⟩
  · exact sup_le (inf_le_inf le_sup_left le_rfl) (inf_le_inf le_sup_right le_rfl)

/-- Conjugating a module factor also conjugates its fixed subgroup when the
actor subgroup is normalized. -/
theorem map_fixed_subgroup_of_normalizes {V W S : Subgroup G} {t : G}
    (hs : t ∈ normalizer (S : Set G))
    (hV : V.map (MulAut.conj t).toMonoidHom = W) :
    (V ⊓ centralizer (S : Set G)).map (MulAut.conj t).toMonoidHom =
      W ⊓ centralizer (S : Set G) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hV]
  have hc := mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_centralizer S hs)
  exact congrArg (fun U => W ⊓ U) hc

/-- The module decomposition in 15.4.12 gives swapped quotient coordinates
once the natural factors' fixed lines and the factor permutation are realized.
Here `C` is the printed `E_Y`; its equality to `C_E(Y)` is derived. -/
theorem swappedBinaryQuotient_of_module_factors
    {E T Y C V₁ V₂ S : Subgroup G}
    (hE : C ⊔ ((V₁ ⊔ V₂) ⊓ centralizer (S : Set G)) = E)
    (hd₀ : Disjoint C (V₁ ⊔ V₂)) (hd₁₂ : Disjoint V₁ V₂)
    (hc₀ : C ≤ centralizer ((V₁ ⊔ V₂ : Subgroup G) : Set G))
    (hc₁₂ : V₁ ≤ centralizer (V₂ : Set G))
    (hCY : C ≤ centralizer (Y : Set G))
    (hVY : (V₁ ⊔ V₂) ⊓ centralizer (Y : Set G) = ⊥)
    (hn₁ : S ≤ normalizer (V₁ : Set G)) (hn₂ : S ≤ normalizer (V₂ : Set G))
    (hcard₁ : Nat.card (V₁ ⊓ centralizer (S : Set G) : Subgroup G) = 2)
    (hcard₂ : Nat.card (V₂ ⊓ centralizer (S : Set G) : Subgroup G) = 2)
    (t : G) (ht : t ∈ T) (hnE : t ∈ normalizer (E : Set G))
    (hnC : t ∈ normalizer (C : Set G)) (hnS : t ∈ normalizer (S : Set G))
    (hs₁ : V₁.map (MulAut.conj t).toMonoidHom = V₂)
    (hs₂ : V₂.map (MulAut.conj t).toMonoidHom = V₁) :
    E ⊓ centralizer (Y : Set G) = C ∧ Nonempty (SwappedBinaryQuotient E T Y) := by
  have hfix := fixed_subgroup_split_of_internal_factors hd₁₂ hc₁₂ hn₁ hn₂
  have hC : E ⊓ centralizer (Y : Set G) = C :=
    fixed_summand_eq_centralizer hE (hc₀.trans (centralizer_le inf_le_left)) hCY
      (le_bot_iff.mp ((inf_le_inf_right _ inf_le_left).trans hVY.le))
  have hFle : (V₁ ⊓ centralizer (S : Set G)) ⊔
      (V₂ ⊓ centralizer (S : Set G)) ≤ V₁ ⊔ V₂ :=
    sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
  refine ⟨hC, swappedBinaryQuotient_of_internal_factors
    (hfix ▸ hE) ?_ ?_ ?_ ?_ hC hcard₁ hcard₂ t ht hnE hnC
    (map_fixed_subgroup_of_normalizes hnS hs₁) (map_fixed_subgroup_of_normalizes hnS hs₂)⟩
  · exact hd₀.mono_right hFle
  · exact hd₁₂.mono inf_le_left inf_le_left
  · exact hc₀.trans (centralizer_le hFle)
  · exact inf_le_left.trans (hc₁₂.trans (centralizer_le inf_le_left))

/-- In the printed decomposition, `U` is the omega center of the two-core of
`YT` and `C = C_U(Y)` is `E_Y`. The module factors lie in `U`. Their disjointness
from `C` proves the fixed-free condition, and commutativity comes from `U`.
Thus neither condition has to be added to the source witnesses. -/
theorem swappedBinaryQuotient_of_omega_decomposition
    {E T Y C V₁ V₂ S U : Subgroup G} [IsMulCommutative U]
    (hCdef : C = U ⊓ centralizer (Y : Set G)) (hVU : V₁ ⊔ V₂ ≤ U)
    (hE : C ⊔ ((V₁ ⊔ V₂) ⊓ centralizer (S : Set G)) = E)
    (hd₀ : Disjoint C (V₁ ⊔ V₂)) (hd₁₂ : Disjoint V₁ V₂)
    (hn₁ : S ≤ normalizer (V₁ : Set G)) (hn₂ : S ≤ normalizer (V₂ : Set G))
    (hcard₁ : Nat.card (V₁ ⊓ centralizer (S : Set G) : Subgroup G) = 2)
    (hcard₂ : Nat.card (V₂ ⊓ centralizer (S : Set G) : Subgroup G) = 2)
    (t : G) (ht : t ∈ T) (hnE : t ∈ normalizer (E : Set G))
    (hnC : t ∈ normalizer (C : Set G)) (hnS : t ∈ normalizer (S : Set G))
    (hs₁ : V₁.map (MulAut.conj t).toMonoidHom = V₂)
    (hs₂ : V₂.map (MulAut.conj t).toMonoidHom = V₁) :
    E ⊓ centralizer (Y : Set G) = C ∧ Nonempty (SwappedBinaryQuotient E T Y) := by
  have hCU : C ≤ U := hCdef ▸ inf_le_left
  have hCY : C ≤ centralizer (Y : Set G) := hCdef ▸ inf_le_right
  have hc₀ : C ≤ centralizer ((V₁ ⊔ V₂ : Subgroup G) : Set G) := by
    intro c hc v hv
    exact setLike_mul_comm (hVU hv) (hCU hc)
  have hc₁₂ : V₁ ≤ centralizer (V₂ : Set G) := by
    intro a ha b hb
    exact setLike_mul_comm (hVU (mem_sup_right hb)) (hVU (mem_sup_left ha))
  have hVY : (V₁ ⊔ V₂) ⊓ centralizer (Y : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hvc : v ∈ C := hCdef ▸ (show v ∈ U ⊓ centralizer (Y : Set G) from
      ⟨hVU hv.1, hv.2⟩)
    exact (disjoint_iff.mp hd₀).le ⟨hvc, hv.1⟩
  exact swappedBinaryQuotient_of_module_factors hE hd₀ hd₁₂ hc₀ hc₁₂ hCY hVY
    hn₁ hn₂ hcard₁ hcard₂ t ht hnE hnC hnS hs₁ hs₂

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors

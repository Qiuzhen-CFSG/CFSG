module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.OuterAction

/-!
# Inner actions on the whole component closure

Inner conjugators on pairwise commuting factors combine to give an inner
conjugator on their join. Theta generation kills each action on a 3′ outer
quotient separately. Thus a finite family of invariant commuting components
suffices; the outer group of their product need not itself have 3′ order.

The final theorem applies this to the actual star images. The generating
family, its mutual centralization, invariance and individual outer orders
remain explicit model inputs. No component orbit is suppressed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1144, inner-action step in the proof of 15.3.49(k).
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner
variable {D : Type*} [Group D]

private lemma inner_on_sup (A B : Subgroup D) (hcomm : A ≤ centralizer (B : Set D))
    (α : MulAut D) (a b : D) (haA : a ∈ A) (hbB : b ∈ B)
    (ha : ∀ x ∈ A, α x = a * x * a⁻¹)
    (hb : ∀ x ∈ B, α x = b * x * b⁻¹) :
    ∃ c ∈ A ⊔ B, ∀ x ∈ A ⊔ B, α x = c * x * c⁻¹ := by
  refine ⟨a * b, (A ⊔ B).mul_mem
    ((show A ≤ A ⊔ B from le_sup_left) haA)
    ((show B ≤ A ⊔ B from le_sup_right) hbB), ?_⟩
  have he : A ⊔ B ≤ α.toMonoidHom.eqLocus (MulAut.conj (a * b)).toMonoidHom := by
    apply sup_le
    · intro x hx
      change α x = a * b * x * (a * b)⁻¹
      have hbx : b * x = x * b := mem_centralizer_iff.mp (hcomm hx) b hbB
      have hfix : b * x * b⁻¹ = x := by rw [hbx, mul_assoc, mul_inv_cancel, mul_one]
      calc
        α x = a * x * a⁻¹ := ha x hx
        _ = a * (b * x * b⁻¹) * a⁻¹ := by rw [hfix]
        _ = a * b * x * (a * b)⁻¹ := by simp only [mul_inv_rev, mul_assoc]
    · intro x hx
      change α x = a * b * x * (a * b)⁻¹
      have hac : a * (b * x * b⁻¹) = b * x * b⁻¹ * a :=
        (mem_centralizer_iff.mp (hcomm haA) (b * x * b⁻¹)
          (B.mul_mem (B.mul_mem hbB hx) (B.inv_mem hbB))).symm
      calc
        α x = b * x * b⁻¹ := hb x hx
        _ = a * (b * x * b⁻¹) * a⁻¹ := by rw [hac]; simp only [mul_assoc, mul_inv_cancel, mul_one]
        _ = a * b * x * (a * b)⁻¹ := by simp only [mul_inv_rev, mul_assoc]
  exact fun x hx => he hx

private lemma inner_on_finset_sup (s : Finset (Subgroup D)) (α : MulAut D)
    (hcomm : ∀ A ∈ s, ∀ B ∈ s, A ≠ B → A ≤ centralizer (B : Set D))
    (hinner : ∀ K ∈ s, ∃ k ∈ K, ∀ x ∈ K, α x = k * x * k⁻¹) :
    ∃ c ∈ s.sup id, ∀ x ∈ s.sup id, α x = c * x * c⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, by simp, ?_⟩
    intro x hx
    have hx1 : x = 1 := by simpa using hx
    simp [hx1]
  | @insert A s hAs ih =>
    obtain ⟨a, ha, hea⟩ := hinner A (Finset.mem_insert_self A s)
    have hss := fun K hK J hJ => hcomm K (Finset.mem_insert_of_mem hK)
      J (Finset.mem_insert_of_mem hJ)
    obtain ⟨b, hb, heb⟩ := ih hss (fun K hK => hinner K (Finset.mem_insert_of_mem hK))
    have hsA : s.sup id ≤ centralizer (A : Set D) := by
      apply Finset.sup_le
      intro B hB
      exact hcomm B (Finset.mem_insert_of_mem hB) A (Finset.mem_insert_self A s)
        (fun he => hAs (he ▸ hB))
    rw [Finset.sup_insert]
    exact inner_on_sup A (s.sup id) (le_centralizer_iff.mp hsA) α a b ha hb hea heb

/-- Assemble inner conjugators on a finite family without a global outer-order assumption. -/
lemma inner_on_normalized_factors {G : Type*} [Group G]
    (Y : Subgroup G) (hY : theta Y = Y) (f : Y →* D)
    (s : Finset (Subgroup D))
    (hcomm : ∀ A ∈ s, ∀ B ∈ s, A ≠ B → A ≤ centralizer (B : Set D))
    (hn : ∀ K ∈ s, f.range ≤ normalizer (K : Set D))
    (hf : ∀ K ∈ s, Finite K)
    (hout : ∀ K ∈ s, ¬ 3 ∣ Nat.card (MulAut.Outer K)) :
    ∀ y : Y, ∃ c ∈ s.sup id, ∀ x ∈ s.sup id, c * x * c⁻¹ = f y * x * (f y)⁻¹ := by
  intro y
  obtain ⟨c, hc, he⟩ := inner_on_finset_sup s (MulAut.conj (f y)) hcomm (by
    intro K hK
    let _ := hf K hK
    let r : Y →* normalizer (K : Set D) :=
      f.codRestrict _ (fun y => hn K hK ⟨y, rfl⟩)
    let α := K.normalizerMonoidHom.comp r
    obtain ⟨k, hk⟩ := inner_of_outer_three_free Y hY α (hout K hK) y
    refine ⟨k, k.property, fun x hx => ?_⟩
    exact (congrArg (fun a : MulAut K => (a ⟨x, hx⟩).val) hk).symm)
  exact ⟨c, hc, fun x hx => (he x hx).symm⟩
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Theta generation descends to the actual star image, regardless of its order. -/
lemma star_theta_eq_self (H M Y : Subgroup G) (hθ : theta (M ⊓ H) = Y) :
    theta (starImage H Y) = starImage H Y := by
  have hYH : Y ≤ H := (hθ ▸ theta_le _).trans inf_le_right
  have ht : theta (Y.subgroupOf H) = Y.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [theta_map_of_injective _ H.subtype_injective,
      map_subgroupOf_eq_of_le hYH, ← hθ, theta_idempotent]
  apply le_antisymm (theta_le _) _
  have hh := theta_map_le (Y.subgroupOf H) (QuotientGroup.mk' (pCore 2 H))
  rwa [ht] at hh

/-- Componentwise outer orders supply the pointwise inner action needed by the
published projection theorem. The family spans the entire closure image. -/
lemma inner_star_of_factor_outer_three_free (H M Y L0 : Subgroup G)
    (hθ : theta (M ⊓ H) = Y)
    (s : Finset (Subgroup (H ⧸ pCore 2 H)))
    (hspan : s.sup id = starImage H L0)
    (hcomm : ∀ A ∈ s, ∀ B ∈ s, A ≠ B → A ≤ centralizer (B : Set (H ⧸ pCore 2 H)))
    (hn : ∀ K ∈ s, starImage H Y ≤ normalizer (K : Set (H ⧸ pCore 2 H)))
    (hout : ∀ K ∈ s, ¬ 3 ∣ Nat.card (MulAut.Outer K)) :
    ∀ y : starImage H Y, ∃ l : starImage H L0, ∀ x : starImage H L0,
      (l : H ⧸ pCore 2 H) * x * l⁻¹ = y * x * y⁻¹ := by
  intro y
  obtain ⟨c, hc, he⟩ := inner_on_normalized_factors (starImage H Y)
    (star_theta_eq_self H M Y hθ) (starImage H Y).subtype s hcomm
    (fun K hK => by simpa only [range_subtype] using hn K hK)
    (fun _ _ => inferInstance) hout y
  exact ⟨⟨c, hspan ▸ hc⟩, fun x => he x (hspan.symm ▸ x.property)⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner

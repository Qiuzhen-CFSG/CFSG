module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.LocalFusion.Basic

/-!
# Reducing the local fusion assertions to Sylow transporters

The proof of source (e) rules out fusion of factor involutions by elements
outside the intersection-generated subgroup H. Taking an involution power
extends this control to all nonidentity factor elements; hypothesis (*) then
gives full set strong closure. Conversely, any failure of strong closure
supplies precisely such an involution and outside conjugator.

For the last paragraph, Sylow conjugacy inside H reduces the unique fixed-point
assertion to transporters into S. These reductions retain the fusion arguments
as explicit premises; they do not assert (e) or the product-fusion theorem from
minimality.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4, pp.94–96, DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

private theorem involution_power (h : Hypotheses S A₁ A₂)
    {a : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (hne : a ≠ 1) :
    orderOf (a ^ (orderOf a / 2)) = 2 := by
  have haS : a ∈ S := ha.elim (fun h₁ => h.left_le h₁) (fun h₂ => h.right_le h₂)
  have hneS : (⟨a, haS⟩ : S) ≠ 1 := fun he => hne (congrArg Subtype.val he)
  have hd : 2 ∣ orderOf a := by
    simpa only [Subgroup.orderOf_mk] using S.isPGroup'.dvd_orderOf hneS
  exact orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos a)) hd

/-- It suffices to control transporters of factor involutions into S. The
half-order power of any nonidentity factor element detects its transporter;
the original element is then handled by strong closure inside H. -/
theorem Hypotheses.closed_of_involution_transporters (h : Hypotheses S A₁ A₂)
    (hf : ∀ a ∈ (A₁ : Set G) ∪ A₂, orderOf a = 2 →
      ∀ g : G, g⁻¹ * a * g ∈ S → g ∈ intersectionGenerated A₁ A₂) :
    IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤ := by
  refine ⟨fun a ha => ha.elim (fun h₁ => h.left_le h₁) (fun h₂ => h.right_le h₂), ?_⟩
  intro a ha g _ hag
  by_cases he : a = 1
  · subst a
    simp only [mul_one, inv_mul_cancel]
    exact Or.inl A₁.one_mem
  have hap : a ^ (orderOf a / 2) ∈ (A₁ : Set G) ∪ A₂ :=
    ha.elim (fun ha₁ => Or.inl (A₁.pow_mem ha₁ _))
      (fun ha₂ => Or.inr (A₂.pow_mem ha₂ _))
  have hagp : g⁻¹ * a ^ (orderOf a / 2) * g ∈ S := by
    have hp := map_pow (MulAut.conj g⁻¹) a (orderOf a / 2)
    simp only [MulAut.conj_apply, inv_inv] at hp
    rw [hp]
    exact (S : Subgroup G).pow_mem hag _
  have hg := hf _ hap (involution_power h ha he) g hagp
  exact h.closed_in_generated.2 a ha g hg
    ⟨(intersectionGenerated A₁ A₂).mul_mem
      ((intersectionGenerated A₁ A₂).mul_mem
        ((intersectionGenerated A₁ A₂).inv_mem hg) (h.union_subset_generated ha)) hg, hag⟩

/-- Sylow conjugacy inside H reduces unique conjugate membership in H to
transporters into the fixed Sylow subgroup. No involution restriction is needed. -/
theorem uniqueConjugateMembership_iff_sylow_transporters {H : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) {x : G} (hxS : x ∈ S) :
    UniqueConjugateMembership H x ↔
      ∀ g : G, g⁻¹ * x * g ∈ S → g ∈ H := by
  constructor
  · intro hu g hg
    exact (hu.2 g).mp (hSH hg)
  · intro ht
    have hxH := hSH hxS
    refine ⟨hxH, fun g => ⟨?_, fun hg => H.mul_mem (H.mul_mem (H.inv_mem hg) hxH) hg⟩⟩
    intro hxg
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_orderOf_eq_pow (⟨x, hxS⟩ : S)
    have hn' : orderOf (⟨g⁻¹ * x * g, hxg⟩ : H) = 2 ^ n := by
      rw [Subgroup.orderOf_mk]
      calc
        orderOf (g⁻¹ * x * g) = orderOf x := by
          simpa [MulAut.conj_apply] using (MulAut.conj g⁻¹).orderOf_eq x
        _ = orderOf (⟨x, hxS⟩ : S) := Subgroup.orderOf_coe (⟨x, hxS⟩ : S)
        _ = 2 ^ n := hn
    obtain ⟨b, hb⟩ := (S.subtype hSH).exists_isConj_of_orderOf_eq_prime_pow hn'
    obtain ⟨k, hk⟩ := isConj_iff.mp hb
    have hk' : (k : G) * (g⁻¹ * x * g) * (k : G)⁻¹ = ((b : H) : G) :=
      congrArg Subtype.val hk
    have hxk : (g * (k : G)⁻¹)⁻¹ * x * (g * (k : G)⁻¹) ∈ S := by
      have he : (g * (k : G)⁻¹)⁻¹ * x * (g * (k : G)⁻¹) = ((b : H) : G) := by
        rw [← hk']
        group
      rw [he]
      exact b.property
    have hmem := ht _ hxk
    simpa using H.mul_mem hmem k.property
/-- The involution-transporter condition is equivalent to full set strong
closure under the source hypotheses. -/
theorem Hypotheses.closed_iff_involution_transporters (h : Hypotheses S A₁ A₂) :
    IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤ ↔
      ∀ a ∈ (A₁ : Set G) ∪ A₂, orderOf a = 2 →
        ∀ g : G, g⁻¹ * a * g ∈ S → g ∈ intersectionGenerated A₁ A₂ := by
  constructor
  · intro hc a ha ha2 g hag
    have hne : a ≠ 1 := by
      intro he
      simp [he] at ha2
    exact transporter_mem_intersectionGenerated ha hne
      (hc.2 a ha g (Subgroup.mem_top _) hag)
  · exact h.closed_of_involution_transporters

/-- The precise contrary configuration used at the start of source (e):
an involution in a factor is fused into S by a conjugator outside H. -/
theorem Hypotheses.exists_involution_fusion_of_not_closed (h : Hypotheses S A₁ A₂)
    (hn : ¬ IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤) :
    ∃ a ∈ (A₁ : Set G) ∪ A₂, orderOf a = 2 ∧
      ∃ g : G, g ∉ intersectionGenerated A₁ A₂ ∧ g⁻¹ * a * g ∈ S := by
  classical
  by_contra hw
  apply hn
  apply h.closed_of_involution_transporters
  intro a ha ha2 g hag
  by_contra hg
  exact hw ⟨a, ha, ha2, g, hg, hag⟩

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end

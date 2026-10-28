module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Direct products and quasisimple two-group extensions

Suppose K is a normal quasisimple subgroup, G/K is a two-group and O₂(G)=1.
A normal subgroup disjoint from K embeds in the quotient, hence is trivial.
The component dichotomy puts K in one of two normal factors generating G:
otherwise K centralizes both factors and is abelian, contradicting
quasisimplicity. Consequently G cannot be a product of two nontrivial groups.

This is the intrinsic obstruction to the product branch of
Aschbacher–Smith B.5.6(3) in the terminal triple-cover comparison, p.1155.
The component calculus is GLS, vol.2, Theorem 3.5.
-/

public section
open Subgroup

namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem normal_disjoint_eq_bot_of_two_quotient (K N : Subgroup G)
    [K.Normal] [N.Normal] (hq : IsPGroup 2 (G ⧸ K))
    (hcore : pCore 2 G = ⊥) (hdis : Disjoint K N) : N = ⊥ := by
  let f := (QuotientGroup.mk' K).comp N.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    have hxK : (x : G) ∈ K := (QuotientGroup.eq_one_iff x.val).mp hx
    exact Subgroup.disjoint_def.mp hdis hxK x.property
  have hN := hq.of_injective f hf
  have hle : N ≤ pCore 2 G := le_sSup ⟨inferInstance, hN⟩
  exact le_bot_iff.mp (hcore ▸ hle)

/-- A quasisimple normal subgroup with two-group quotient prevents a nontrivial
normal direct-product decomposition when the two-core is trivial. -/
theorem no_normal_product_of_quasisimple_two_quotient (K A B : Subgroup G)
    [K.Normal] [IsQuasisimple K] [A.Normal] [B.Normal]
    (hq : IsPGroup 2 (G ⧸ K)) (hcore : pCore 2 G = ⊥)
    (hdis : Disjoint A B) (hsup : A ⊔ B = ⊤) (hA : A ≠ ⊥) (hB : B ≠ ⊥) : False := by
  have hK : IsComponent G K := ⟨(inferInstance : K.Normal).isSubnormal, inferInstance⟩
  rcases hK.normal_dichotomy A with ha | ha
  · exact hB (normal_disjoint_eq_bot_of_two_quotient K B hq hcore (hdis.mono_left ha))
  rcases hK.normal_dichotomy B with hb | hb
  · exact hA (normal_disjoint_eq_bot_of_two_quotient K A hq hcore (hdis.symm.mono_left hb))
  have hc : ⊤ ≤ centralizer (K : Set G) := by
    rw [← hsup]
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
  have he : ⁅K, K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (le_top.trans hc)
  rw [commutator_eq_self] at he
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance he
end Theory.GroupTheory

namespace Theory.GroupTheory
variable {G A B : Type*} [Group G] [Group A] [Group B]
    [Nontrivial A] [Nontrivial B]

/-- No abstract equivalence with two nontrivial direct factors can exist. -/
theorem not_product_of_quasisimple_two_quotient (K : Subgroup G)
    [K.Normal] [IsQuasisimple K] (hq : IsPGroup 2 (G ⧸ K))
    (hcore : pCore 2 G = ⊥) (e : (A × B) ≃* G) : False := by
  let L := ((⊤ : Subgroup A).prod (⊥ : Subgroup B)).map e.toMonoidHom
  let R := ((⊥ : Subgroup A).prod (⊤ : Subgroup B)).map e.toMonoidHom
  let : L.Normal := (inferInstance : ((⊤ : Subgroup A).prod (⊥ : Subgroup B)).Normal).map
    _ e.surjective
  let : R.Normal := (inferInstance : ((⊥ : Subgroup A).prod (⊤ : Subgroup B)).Normal).map
    _ e.surjective
  have hdis : Disjoint L R := by
    apply Subgroup.disjoint_def.mpr
    rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    have hab := e.injective (hax.trans hbx.symm)
    have ha1 : a = 1 := Prod.ext ((congrArg Prod.fst hab).trans hb.1) ha.2
    rw [← hax, ha1, map_one]
  have hsup : L ⊔ R = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective x
    have hl : e (a, 1) ∈ L := mem_map_of_mem _ ⟨mem_top _, rfl⟩
    have hr : e (1, b) ∈ R := mem_map_of_mem _ ⟨rfl, mem_top _⟩
    simpa only [← map_mul, Prod.mk_mul_mk, mul_one, one_mul] using
      mul_mem_sup hl hr
  have hL : L ≠ ⊥ := by
    intro he
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    have hx : e (a, 1) ∈ L := mem_map_of_mem _ ⟨mem_top _, rfl⟩
    rw [he, mem_bot, ← e.map_one] at hx
    exact ha (congrArg Prod.fst (e.injective hx))
  have hR : R ≠ ⊥ := by
    intro he
    obtain ⟨b, hb⟩ := exists_ne (1 : B)
    have hx : e (1, b) ∈ R := mem_map_of_mem _ ⟨rfl, mem_top _⟩
    rw [he, mem_bot, ← e.map_one] at hx
    exact hb (congrArg Prod.snd (e.injective hx))
  exact no_normal_product_of_quasisimple_two_quotient K L R hq hcore hdis hsup hL hR
end Theory.GroupTheory

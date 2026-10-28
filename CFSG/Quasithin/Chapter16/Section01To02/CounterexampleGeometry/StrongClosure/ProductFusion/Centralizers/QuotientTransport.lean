module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.FinalParagraph
public import Theory.GroupTheory.SetStrongClosureImage
public import BenderSuzuki.SE.Compat
public import Theory.GroupAction.Cardinalities

/-!
# The actual central quotient in Aschbacher's mixed-product argument

Strong closure lifts each quotient intersection transporter into the original
intersection-generated subgroup when the kernel lies in the fixed Sylow.
The resulting containment of preimages excludes generation of the entire
quotient. A central element of either factor would already force H = G,
so central quotient maps embed both factors and preserve their ranks.
Strong closure of the image then supplies all three closure clauses, including
both relative normalizers, for the genuine image Sylow and image factors.

The last theorem applies minimality in G/⟨ab⟩ and proves its generated subgroup
proper. Its nested strong-embedding and exceptional alternatives still need
elimination; this module does not claim source (g).

Source: M. Aschbacher, *On finite groups of component type*, Illinois J.
Math. 19 (1975), Lemma 3.4(g), pp.95–96, DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
universe u v
variable {G : Type u} [Group G] [Finite G] {Q : Type v} [Group Q]
variable {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

omit [Finite G] in
/-- Each generator in the quotient lifts to an ambient factor transporter. -/
theorem Hypotheses.generated_image_le_of_ker_le_sylow (h : Hypotheses S A₁ A₂)
    (hc : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    (q : G →* Q) (hq : Function.Surjective q) (hk : q.ker ≤ S) :
    intersectionGenerated (A₁.map q) (A₂.map q) ≤ (intersectionGenerated A₁ A₂).map q := by
  have rep (C : Subgroup Q) (hC : C ∈ ({A₁.map q, A₂.map q} : Set (Subgroup Q)))
      {x : Q} (hx : x ∈ C) : ∃ a ∈ (A₁ : Set G) ∪ A₂, q a = x := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with rfl | rfl
    · obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨a, Or.inl ha, rfl⟩
    · obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨a, Or.inr ha, rfl⟩
  apply (closure_le _).mpr
  rintro z ⟨C, hC, D, hD, hcap⟩
  obtain ⟨g, rfl⟩ := hq z
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcap
  obtain ⟨c, hcC, hcx⟩ := x.property.1
  obtain ⟨a, ha, rfl⟩ := rep C hC hcC
  obtain ⟨b, hb, hbx⟩ := rep D hD x.property.2
  have he : q (g⁻¹ * a * g) = q b := by
    rw [map_mul, map_mul, map_inv, hbx]
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, inv_inv] using hcx
  have hane : a ≠ 1 := by
    intro ha1
    apply hxne
    apply Subtype.ext
    have he' : q (g⁻¹ * a * g) = (x : Q) := he.trans hbx
    simpa [ha1] using he'.symm
  have hk' : (g⁻¹ * a * g) * b⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  have hs : g⁻¹ * a * g ∈ S := by
    change g⁻¹ * a * g ∈ (S : Subgroup G)
    have hbS := hb.elim (fun hb => h.left_le hb) (fun hb => h.right_le hb)
    simpa using (S : Subgroup G).mul_mem (hk hk') hbS
  exact mem_map_of_mem q (transporter_mem_intersectionGenerated ha hane
    (hc.2 a ha g (mem_top _) hs))

/-- The full preimage of the quotient generated subgroup lies in H. -/
theorem Hypotheses.generated_image_comap_le_of_ker_le_sylow (h : Hypotheses S A₁ A₂)
    (hc : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    (q : G →* Q) (hq : Function.Surjective q) (hk : q.ker ≤ S) :
    (intersectionGenerated (A₁.map q) (A₂.map q)).comap q ≤ intersectionGenerated A₁ A₂ := by
  intro g hg
  obtain ⟨y, hy, hqy⟩ := h.generated_image_le_of_ker_le_sylow hc q hq hk hg
  have hgk : g * y⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqy, mul_inv_cancel]
  simpa using (intersectionGenerated A₁ A₂).mul_mem
    (h.sylow_le_generated_of_closed hc (hk hgk)) hy

private theorem hypotheses_of_closed {X : Type*} [Group X]
    {P : Sylow 2 X} {B₁ B₂ : Subgroup X}
    (h₁ : B₁ ≤ P) (h₂ : B₂ ≤ P) (hm : ⁅B₁, B₂⁆ = ⊥)
    (hr₁ : TwoRankAtLeastTwo B₁) (hr₂ : TwoRankAtLeastTwo B₂)
    (hc : IsStronglyClosedSet ((B₁ : Set X) ∪ B₂) (P : Subgroup X) ⊤) :
    Hypotheses P B₁ B₂ := by
  have hne {B : Subgroup X} (hr : TwoRankAtLeastTwo B) : B ≠ ⊥ := by
    obtain ⟨E, hE, _⟩ := hr
    intro he
    have : Subsingleton B := he ▸ inferInstance
    have : Subsingleton E := inferInstance
    have hh : Nat.card E = 1 := Nat.card_unique
    omega
  have hu : (B₁ : Set X) ∪ B₂ ⊆ intersectionGenerated B₁ B₂ :=
    fun _ hx => hx.elim (fun hx => left_le_intersectionGenerated (hne hr₁) hx)
      (fun hx => right_le_intersectionGenerated (hne hr₂) hx)
  have hn₁ : (B₁ : Set X) ∪ B₂ ⊆ normalizer (B₁ : Set X) := by
    intro x hx
    rcases hx with hx | hx
    · exact le_normalizer hx
    · apply Subgroup.centralizer_le_normalizer (B₁ : Set X)
      exact commutator_eq_bot_iff_le_centralizer.mp
        (by rw [commutator_comm]; exact hm) hx
  have hn₂ : (B₁ : Set X) ∪ B₂ ⊆ normalizer (B₂ : Set X) := by
    intro x hx
    rcases hx with hx | hx
    · exact Subgroup.centralizer_le_normalizer (B₂ : Set X)
        (commutator_eq_bot_iff_le_centralizer.mp hm hx)
    · exact le_normalizer hx
  refine ⟨h₁, h₂, hm, hr₁, hr₂, ?_, ?_, ?_⟩
  · exact ⟨fun _ hx => ⟨hu hx, hc.1 hx⟩,
      fun x hx g _ hg => hc.2 x hx g (mem_top _) hg.2⟩
  · exact ⟨fun _ hx => ⟨hc.1 hx, hn₁ hx⟩,
      fun x hx g _ hg => hc.2 x hx g (mem_top _) hg.1⟩
  · exact ⟨fun _ hx => ⟨hc.1 hx, hn₂ hx⟩,
      fun x hx g _ hg => hc.2 x hx g (mem_top _) hg.1⟩

/-- Transport the source setup along a surjection that embeds both factors. -/
theorem Hypotheses.image_of_closed (h : Hypotheses S A₁ A₂)
    (hc : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    (q : G →* Q) (hq : Function.Surjective q)
    (hi₁ : Function.Injective (q.comp A₁.subtype))
    (hi₂ : Function.Injective (q.comp A₂.subtype)) :
    Hypotheses (S.mapSurjective hq) (A₁.map q) (A₂.map q) := by
  apply hypotheses_of_closed (map_mono h.left_le) (map_mono h.right_le)
  · rw [← map_commutator, h.commute, Subgroup.map_bot]
  · apply h.left_rank.map_of_injective (q.subgroupMap A₁)
    intro x y he
    exact hi₁ (congrArg Subtype.val he)
  · apply h.right_rank.map_of_injective (q.subgroupMap A₂)
    intro x y he
    exact hi₂ (congrArg Subtype.val he)
  · simpa only [Set.image_union, coe_map, Sylow.coe_mapSurjective] using hc.image S q hq

/-- A minimal counterexample has no nonidentity central element in either factor. -/
theorem MinimalCounterexample.central_factor_eq_one
    (m : MinimalCounterexample S A₁ A₂) {x : G}
    (hx : x ∈ (A₁ : Set G) ∪ A₂) (hz : x ∈ center G) : x = 1 := by
  by_contra hne
  apply m.fails
  left
  apply top_unique
  intro g _
  apply transporter_mem_intersectionGenerated hx hne
  have he : g⁻¹ * x * g = x := by
    rw [mul_assoc, ← mem_center_iff.mp hz g, inv_mul_cancel_left]
  rwa [he]

/-- A central quotient map is injective on each literal factor. -/
theorem MinimalCounterexample.central_quotient_injective
    (m : MinimalCounterexample S A₁ A₂) (N : Subgroup G) [N.Normal]
    (hN : N ≤ center G) :
    Function.Injective ((QuotientGroup.mk' N).comp A₁.subtype) ∧
    Function.Injective ((QuotientGroup.mk' N).comp A₂.subtype) := by
  constructor
  · apply (injective_iff_map_eq_one _).mpr
    intro x hx
    apply Subtype.ext
    exact m.central_factor_eq_one (Or.inl x.property)
      (hN ((QuotientGroup.eq_one_iff (N := N) (x : G)).mp hx))
  · apply (injective_iff_map_eq_one _).mpr
    intro x hx
    apply Subtype.ext
    exact m.central_factor_eq_one (Or.inr x.property)
      (hN ((QuotientGroup.eq_one_iff (N := N) (x : G)).mp hx))

/-- All source hypotheses hold for the actual central quotient and image Sylow. -/
theorem MinimalCounterexample.central_quotient_hypotheses
    (m : MinimalCounterexample S A₁ A₂)
    (hc : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    (N : Subgroup G) [N.Normal] (hN : N ≤ center G) :
    Hypotheses (S.mapSurjective (QuotientGroup.mk'_surjective N))
      (A₁.map (QuotientGroup.mk' N)) (A₂.map (QuotientGroup.mk' N)) :=
  m.setup.image_of_closed hc _ (QuotientGroup.mk'_surjective N)
    (m.central_quotient_injective N hN).1 (m.central_quotient_injective N hN).2

/-- The quotient by a normal mixed cyclic subgroup cannot satisfy alternative (1). -/
theorem MinimalCounterexample.mixed_quotient_generated_ne_top
    (m : MinimalCounterexample S A₁ A₂)
    (hc : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₂)
    [(zpowers (a * b)).Normal] :
    intersectionGenerated (A₁.map (QuotientGroup.mk' (zpowers (a * b))))
      (A₂.map (QuotientGroup.mk' (zpowers (a * b)))) ≠ ⊤ := by
  intro he
  apply m.fails
  left
  apply top_unique
  have hker : (QuotientGroup.mk' (zpowers (a * b))).ker ≤ S := by
    rw [QuotientGroup.ker_mk']
    exact zpowers_le.mpr ((S : Subgroup G).mul_mem (m.setup.left_le ha) (m.setup.right_le hb))
  have hh := m.setup.generated_image_comap_le_of_ker_le_sylow hc
    (QuotientGroup.mk' (zpowers (a * b))) (QuotientGroup.mk'_surjective _) hker
  simpa only [he, comap_top] using hh

/-- Minimality applies to the actual central quotient, with every source
setup clause transported and its generated subgroup still proper. -/
theorem MinimalCounterexample.mixed_central_quotient_conclusion
    (m : MinimalCounterexample S A₁ A₂)
    (hc : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₂)
    (hu : a * b ∈ center G) (hne : a * b ≠ 1)
    [(zpowers (a * b)).Normal] :
    Conclusion (A₁.map (QuotientGroup.mk' (zpowers (a * b))))
      (A₂.map (QuotientGroup.mk' (zpowers (a * b)))) ∧
    intersectionGenerated (A₁.map (QuotientGroup.mk' (zpowers (a * b))))
      (A₂.map (QuotientGroup.mk' (zpowers (a * b)))) ≠ ⊤ := by
  have hN : zpowers (a * b) ≠ ⊥ := by
    intro he
    exact hne (mem_bot.mp (he ▸ mem_zpowers (a * b)))
  refine ⟨?_, m.mixed_quotient_generated_ne_top hc ha hb⟩
  exact m.smaller (natCard_quotient_lt_natCard_of_ne_bot _ hN)
    (S.mapSurjective (QuotientGroup.mk'_surjective _)) _ _
    (m.central_quotient_hypotheses hc _ (zpowers_le.mpr hu))

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end

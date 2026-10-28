module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.LocalFusion.Basic
public import Theory.GroupTheory.PGroup.NormalizerBarrier

/-!
# Pair geometry and local Sylow containment for Aschbacher 3.4

A two-subgroup of order greater than two which permutes the factors has a
nonidentity element normalizing the first factor. Hypothesis (*) puts its
transporter in H. Normalizer ascent in S then proves permutation of the pair
when the factors are incomparable. Sylow conjugacy inside H gives the unique
fixed-coset assertion (c) for every subgroup of either factor of order greater
than two.

For nested factors, their union is a subgroup. A separate normalizer ascent
proves global strong closure directly, giving (c) in this case too. This does
not assert permutation of the smaller nested factor.

Finally, (c) and the p-group normalizer condition put every two-overgroup of a
large factor subgroup in H. In particular, a Sylow subgroup of C_G(u) containing
C_S(u) has its actual ambient image in H. Replacing the ambient Sylow while
retaining the restricted factor data is a further obligation; C_S(u) itself
is not asserted to be Sylow.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4(b)--(d), printed pp.94--95, DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

private def pairNormalizer (A B : Subgroup G) : Subgroup G where
  carrier := {g | (conjugate A g = A ∧ conjugate B g = B) ∨
    (conjugate A g = B ∧ conjugate B g = A)}
  one_mem' := Or.inl ⟨conjugate_one _, conjugate_one _⟩
  mul_mem' := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl ⟨by rw [← conjugate_conjugate, hx.1, hy.1],
        by rw [← conjugate_conjugate, hx.2, hy.2]⟩
    · exact Or.inr ⟨by rw [← conjugate_conjugate, hx.1, hy.1],
        by rw [← conjugate_conjugate, hx.2, hy.2]⟩
    · exact Or.inr ⟨by rw [← conjugate_conjugate, hx.1, hy.2],
        by rw [← conjugate_conjugate, hx.2, hy.1]⟩
    · exact Or.inl ⟨by rw [← conjugate_conjugate, hx.1, hy.2],
        by rw [← conjugate_conjugate, hx.2, hy.1]⟩
  inv_mem' := by
    intro x hx
    have ha : conjugate (conjugate A x) x⁻¹ = A := by simp [conjugate_conjugate]
    have hb : conjugate (conjugate B x) x⁻¹ = B := by simp [conjugate_conjugate]
    rcases hx with hx | hx
    · rw [hx.1] at ha
      rw [hx.2] at hb
      exact Or.inl ⟨ha, hb⟩
    · rw [hx.1] at ha
      rw [hx.2] at hb
      exact Or.inr ⟨hb, ha⟩

omit [Finite G] in
private theorem card_conjugate (X : Subgroup G) (g : G) :
    Nat.card (conjugate X g) = Nat.card X :=
  card_map_of_injective (MulAut.conj g⁻¹).injective

private theorem permutes_of_union_images {A B : Subgroup G} {g : G}
    (hAB : ¬ A ≤ B) (hBA : ¬ B ≤ A)
    (ha : (conjugate A g : Set G) ⊆ (A : Set G) ∪ B)
    (hb : (conjugate B g : Set G) ⊆ (A : Set G) ∪ B) :
    g ∈ pairNormalizer A B := by
  have hback {X Y : Subgroup G} (hX : conjugate X g = X)
      (hYX : conjugate Y g ≤ X) : Y ≤ X := by
    have hh := map_mono (f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) hYX
    change conjugate (conjugate Y g) g⁻¹ ≤ conjugate X g⁻¹ at hh
    have hhX : conjugate X g⁻¹ = X := by
      calc
        conjugate X g⁻¹ = conjugate (conjugate X g) g⁻¹ := congrArg (fun Y => conjugate Y g⁻¹) hX.symm
        _ = X := by rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
    simpa only [conjugate_conjugate, mul_inv_cancel, conjugate_one, hhX] using hh
  rcases SubgroupClass.subset_union.mp ha with ha | ha
  · have heA : conjugate A g = A := eq_of_le_of_card_ge ha (by rw [card_conjugate])
    rcases SubgroupClass.subset_union.mp hb with hb | hb
    · exact (hBA (hback heA hb)).elim
    · exact Or.inl ⟨heA, eq_of_le_of_card_ge hb (by rw [card_conjugate])⟩
  · rcases SubgroupClass.subset_union.mp hb with hb | hb
    · have hac : Nat.card A ≤ Nat.card B := by
        simpa only [card_conjugate] using Subgroup.card_le_of_le ha
      have hbc : Nat.card B ≤ Nat.card A := by
        simpa only [card_conjugate] using Subgroup.card_le_of_le hb
      exact Or.inr ⟨eq_of_le_of_card_ge ha (by rwa [card_conjugate]),
        eq_of_le_of_card_ge hb (by rwa [card_conjugate])⟩
    · have heB : conjugate B g = B := eq_of_le_of_card_ge hb (by rw [card_conjugate])
      exact (hAB (hback heB ha)).elim

omit [Finite G] in
private theorem exists_nonidentity_normalizer_of_pair {X A B : Subgroup G}
    (hX : X ≤ pairNormalizer A B) (hcard : 2 < Nat.card X) :
    ∃ x ∈ X, x ≠ 1 ∧ x ∈ normalizer (A : Set G) := by
  classical
  by_contra hn
  have hfix {x : G} (hx : x ∈ X) (hxa : conjugate A x = A) : x = 1 := by
    by_contra hne
    exact hn ⟨x, hx, hne, (mem_normalizer_iff_conjugate_eq A x).mpr hxa⟩
  let f : X → Bool := fun x => decide (conjugate A (x : G) = A)
  have hf : Function.Injective f := by
    intro x y hxy
    have he : (conjugate A (x : G) = A) ↔ (conjugate A (y : G) = A) :=
      by simpa only [f, decide_eq_decide] using hxy
    apply Subtype.ext
    by_cases hx : conjugate A (x : G) = A
    · rw [hfix x.property hx, hfix y.property (he.mp hx)]
    · have hy : conjugate A (y : G) ≠ A := fun hy => hx (he.mpr hy)
      have hxs : conjugate A (x : G) = B :=
        ((hX x.property).resolve_left (fun h => hx h.1)).1
      have hys : conjugate A (y : G) = B :=
        ((hX y.property).resolve_left (fun h => hy h.1)).1
      have hi : conjugate B (y : G)⁻¹ = A := by
        rw [← hys, conjugate_conjugate, mul_inv_cancel, conjugate_one]
      have hprod := hfix (X.mul_mem x.property (X.inv_mem y.property))
        (show conjugate A ((x : G) * (y : G)⁻¹) = A by
          rw [← conjugate_conjugate, hxs, hi])
      exact mul_inv_eq_one.mp hprod
  have hc := Nat.card_le_card_of_injective f hf
  have hbool : Nat.card Bool = 2 := by simp
  rw [hbool] at hc
  exact (not_lt_of_ge hc) hcard

omit [Finite G] in
/-- The transporter argument immediately preceding source (b). -/
theorem Hypotheses.large_transporter_mem_of_pair_normalizing (h : Hypotheses S A₁ A₂)
    {X : Subgroup G} (hX : X ≤ A₁ ∨ X ≤ A₂) (hc : 2 < Nat.card X)
    {g : G} (hXS : conjugate X g ≤ S)
    (hperm : ∀ x ∈ conjugate X g,
      (conjugate A₁ x = A₁ ∧ conjugate A₂ x = A₂) ∨
      (conjugate A₁ x = A₂ ∧ conjugate A₂ x = A₁)) :
    g ∈ intersectionGenerated A₁ A₂ := by
  obtain ⟨y, hy, hyne, hyN⟩ := exists_nonidentity_normalizer_of_pair
    (show conjugate X g ≤ pairNormalizer A₁ A₂ from hperm)
    (by rwa [card_conjugate])
  obtain ⟨x, hx, he⟩ := hy
  have he' : g⁻¹ * x * g = y := by simpa using he
  apply h.transporter_mem_of_left_normalizer
    (hX.elim (fun hh => Or.inl (hh hx)) (fun hh => Or.inr (hh hx)))
  · intro hone
    exact hyne (by simpa [hone] using he'.symm)
  · rw [he']
    exact ⟨hXS (he ▸ mem_map_of_mem _ hx), hyN⟩

/-- The normalizer condition in the Sylow group proves source (b) for
incomparable factors. The nested case is deliberately not asserted here. -/
theorem Hypotheses.permutes_pair_of_nonnested (h : Hypotheses S A₁ A₂)
    (hn₁ : ¬ A₁ ≤ A₂) (hn₂ : ¬ A₂ ≤ A₁) :
    ∀ s ∈ S, (conjugate A₁ s = A₁ ∧ conjugate A₂ s = A₂) ∨
      (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁) := by
  let P : Subgroup G := (S : Subgroup G) ⊓ pairNormalizer A₁ A₂
  have hUP {x : G} (hx : x ∈ (A₁ : Set G) ∪ A₂) : x ∈ P := by
    exact ⟨(h.closed_in_left_normalizer.1 hx).1, Or.inl
      ⟨(mem_normalizer_iff_conjugate_eq _ _).mp (h.closed_in_left_normalizer.1 hx).2,
       (mem_normalizer_iff_conjugate_eq _ _).mp (h.closed_in_right_normalizer.1 hx).2⟩⟩
  have hAP : A₁ ≤ P := fun _ hx => hUP (Or.inl hx)
  have hBP : A₂ ≤ P := fun _ hx => hUP (Or.inr hx)
  have hr : 2 < Nat.card A₁ := by
    obtain ⟨E, hc, _⟩ := h.left_rank
    have hb := card_le_card_group E
    rw [hc] at hb
    omega
  let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  have hself : normalizer (P.subgroupOf S : Set S) ≤ P.subgroupOf S := by
    intro g hg
    have hNg : (g : G) ∈ normalizer (P : Set G) := by
      rw [← subgroupOf_normalizer_eq (show P ≤ S from inf_le_left)] at hg
      exact hg
    have himg {X : Subgroup G} (hXP : X ≤ P) : conjugate X (g : G) ≤ P := by
      rw [← (mem_normalizer_iff_conjugate_eq P g).mp hNg]
      exact map_mono hXP
    have hgH := h.large_transporter_mem_of_pair_normalizing (Or.inl (le_refl A₁)) hr
      ((himg hAP).trans inf_le_left) (fun x hx => (himg hAP hx).2)
    have hclosed {X : Subgroup G} (hXP : X ≤ P)
        (hXU : (X : Set G) ⊆ (A₁ : Set G) ∪ A₂) :
        (conjugate X (g : G) : Set G) ⊆ (A₁ : Set G) ∪ A₂ := by
      rintro x ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      apply h.closed_in_generated.2 a (hXU ha) g hgH
      exact ⟨(intersectionGenerated A₁ A₂).mul_mem
        ((intersectionGenerated A₁ A₂).mul_mem
          ((intersectionGenerated A₁ A₂).inv_mem hgH) (h.union_subset_generated (hXU ha))) hgH,
        by simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
          (himg hXP (mem_map_of_mem _ ha)).1⟩
    exact ⟨g.property, permutes_of_union_images hn₁ hn₂
      (hclosed hAP (fun _ hx => Or.inl hx)) (hclosed hBP (fun _ hx => Or.inr hx))⟩
  have htop : P.subgroupOf S = ⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent _ (le_antisymm hself le_normalizer)
  exact fun s hs => (subgroupOf_eq_top.mp htop hs).2

/-- Pair permutation puts the original Sylow subgroup in H, independently
of global strong closure. -/
theorem Hypotheses.sylow_le_generated_of_permuting (h : Hypotheses S A₁ A₂)
    (hperm : ∀ s ∈ S,
      (conjugate A₁ s = A₁ ∧ conjugate A₂ s = A₂) ∨
      (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁)) :
    (S : Subgroup G) ≤ intersectionGenerated A₁ A₂ := by
  obtain ⟨a, hane⟩ := ne_bot_iff_exists_ne_one.mp h.left_ne_bot
  have hane' : (a : G) ≠ 1 := fun he => hane (Subtype.ext he)
  intro g hg
  apply transporter_mem_intersectionGenerated (Or.inl a.property) hane'
  have hm : g⁻¹ * (a : G) * g ∈ conjugate A₁ g :=
    mem_map.mpr ⟨a, a.property, by simp⟩
  rcases hperm g hg with hp | hp
  · rw [hp.1] at hm
    exact Or.inl hm
  · rw [hp.1] at hm
    exact Or.inr hm


/-- Source (c) follows from pair permutation and Sylow conjugacy inside H.
The two-subgroup is transported as a whole, not element by element. -/
theorem Hypotheses.unique_large_of_permuting (h : Hypotheses S A₁ A₂)
    (hperm : ∀ s ∈ S,
      (conjugate A₁ s = A₁ ∧ conjugate A₂ s = A₂) ∨
      (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁))
    (X : Subgroup G) (hX : X ≤ A₁ ∨ X ≤ A₂) (hc : 2 < Nat.card X) :
    UniqueSubgroupConjugateMembership (intersectionGenerated A₁ A₂) X := by
  let H := intersectionGenerated A₁ A₂
  have hSH : (S : Subgroup G) ≤ H := h.sylow_le_generated_of_permuting hperm
  have hXS : X ≤ S := hX.elim (fun hh => hh.trans h.left_le)
    (fun hh => hh.trans h.right_le)
  have hXH : X ≤ H := hXS.trans hSH
  refine ⟨hXH, fun g => ⟨?_, ?_⟩⟩
  · intro hg
    have hp : IsPGroup 2 ((conjugate X g).subgroupOf H) :=
      ((S.isPGroup'.to_le hXS).map (MulAut.conj g⁻¹).toMonoidHom).comap_subtype
    obtain ⟨T, hT⟩ := hp.exists_le_sylow
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq H T (S.subtype hSH)
    have hplace : conjugate X (g * (k : G)⁻¹) ≤ S := by
      rintro x ⟨a, ha, rfl⟩
      have hag : g⁻¹ * a * g ∈ conjugate X g :=
        mem_map.mpr ⟨a, ha, by simp⟩
      let y : H := ⟨g⁻¹ * a * g, hg hag⟩
      have hy : y ∈ T := hT hag
      have hky : k * y * k⁻¹ ∈ S.subtype hSH := by
        rw [← hk]
        exact mem_map_of_mem (MulAut.conj k).toMonoidHom hy
      have hky' : (k : G) * (g⁻¹ * a * g) * (k : G)⁻¹ ∈ S := hky
      change (MulAut.conj (g * (k : G)⁻¹)⁻¹) a ∈ (S : Subgroup G)
      change (k : G) * (g⁻¹ * a * g) * (k : G)⁻¹ ∈ (S : Subgroup G) at hky'
      simpa only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc] using hky'
    have hgk : g * (k : G)⁻¹ ∈ H :=
      h.large_transporter_mem_of_pair_normalizing hX hc hplace
        (fun x hx => hperm x (hplace hx))
    simpa only [inv_mul_cancel_right] using H.mul_mem hgk k.property
  · intro hg
    rintro x ⟨a, ha, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      H.mul_mem (H.mul_mem (H.inv_mem hg) (hXH ha)) hg

/-- The nonnested source configuration satisfies (b) and (c) without
minimality or any global strong-closure premise. -/
theorem Hypotheses.local_pair_geometry_of_nonnested (h : Hypotheses S A₁ A₂)
    (hn₁ : ¬ A₁ ≤ A₂) (hn₂ : ¬ A₂ ≤ A₁) :
    (∀ s ∈ S, (conjugate A₁ s = A₁ ∧ conjugate A₂ s = A₂) ∨
      (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁)) ∧
    ∀ X : Subgroup G, (X ≤ A₁ ∨ X ≤ A₂) → 2 < Nat.card X →
      UniqueSubgroupConjugateMembership (intersectionGenerated A₁ A₂) X := by
  have hp := h.permutes_pair_of_nonnested hn₁ hn₂
  exact ⟨hp, h.unique_large_of_permuting hp⟩


private theorem closed_subgroup_of_closed_in_normalizer {B : Subgroup G}
    (hc : IsStronglyClosedSet (B : Set G)
      ((S : Subgroup G) ⊓ normalizer (B : Set G)) ⊤) :
    IsStronglyClosedSet (B : Set G) (S : Subgroup G) ⊤ := by
  let P := (S : Subgroup G) ⊓ normalizer (B : Set G)
  have hBP : B ≤ P := hc.1
  let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  have hself : normalizer (P.subgroupOf S : Set S) ≤ P.subgroupOf S := by
    intro g hg
    have hgP : (g : G) ∈ normalizer (P : Set G) := by
      rw [← subgroupOf_normalizer_eq (show P ≤ S from inf_le_left)] at hg
      exact hg
    have himg : conjugate B (g : G) ≤ P := by
      rw [← (mem_normalizer_iff_conjugate_eq P g).mp hgP]
      exact map_mono hBP
    have hBB : conjugate B (g : G) ≤ B := by
      rintro x ⟨a, ha, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, SetLike.mem_coe] using
        hc.2 a ha g (mem_top _) (by
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
            himg (mem_map_of_mem _ ha))
    exact ⟨g.property, (mem_normalizer_iff_conjugate_eq B g).mpr
      (eq_of_le_of_card_ge hBB (by rw [card_conjugate]))⟩
  have htop : P.subgroupOf S = ⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent _ (le_antisymm hself le_normalizer)
  have hSP : (S : Subgroup G) ≤ P := subgroupOf_eq_top.mp htop
  exact ⟨fun x hx => (hc.1 hx).1,
    fun x hx g _ hg => hc.2 x hx g (mem_top _) (hSP hg)⟩

/-- In the nested case the union is a subgroup. Normalizer ascent proves
its global strong closure directly, without minimality or Theorem ZD. -/
theorem Hypotheses.closed_of_nested (h : Hypotheses S A₁ A₂)
    (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁) :
    IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤ := by
  rcases hn with hn | hn
  · have he : (A₁ : Set G) ∪ A₂ = (A₂ : Set G) := Set.union_eq_right.mpr hn
    have hc := h.closed_in_right_normalizer
    rw [he] at hc ⊢
    exact closed_subgroup_of_closed_in_normalizer hc
  · have he : (A₁ : Set G) ∪ A₂ = (A₁ : Set G) := Set.union_eq_left.mpr hn
    have hc := h.closed_in_left_normalizer
    rw [he] at hc ⊢
    exact closed_subgroup_of_closed_in_normalizer hc

/-- Source (c), including the nested factors: every subgroup of either
factor of order greater than two has the unique fixed coset H. -/
theorem Hypotheses.unique_large (h : Hypotheses S A₁ A₂)
    (X : Subgroup G) (hX : X ≤ A₁ ∨ X ≤ A₂) (hc : 2 < Nat.card X) :
    UniqueSubgroupConjugateMembership (intersectionGenerated A₁ A₂) X := by
  by_cases hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁
  · have hclosed := h.closed_of_nested hn
    have hXU : (X : Set G) ⊆ (A₁ : Set G) ∪ A₂ := SubgroupClass.subset_union.mpr hX
    have hne : X ≠ ⊥ := by
      intro he
      simp only [he, card_bot] at hc
      omega
    obtain ⟨a, hane⟩ := ne_bot_iff_exists_ne_one.mp hne
    have ha : UniqueConjugateMembership (intersectionGenerated A₁ A₂) (a : G) :=
      h.unique_of_closed hclosed (hXU a.property)
        (fun he => hane (Subtype.ext he))
    refine ⟨fun x hx => h.union_subset_generated (hXU hx), fun g => ⟨?_, ?_⟩⟩
    · intro hg
      apply (ha.2 g).mp
      apply hg
      exact mem_map.mpr ⟨a, a.property, by simp⟩
    · intro hg
      rintro x ⟨b, hb, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        (intersectionGenerated A₁ A₂).mul_mem
          ((intersectionGenerated A₁ A₂).mul_mem
            ((intersectionGenerated A₁ A₂).inv_mem hg) (h.union_subset_generated (hXU hb))) hg
  · exact h.unique_large_of_permuting
      (h.permutes_pair_of_nonnested (fun h₁ => hn (Or.inl h₁)) (fun h₂ => hn (Or.inr h₂))) X hX hc

/-- The first Sylow-placement assertion on source p.95: for each local
subgroup whose left intersection has rank at least two, a Sylow subgroup
containing the original Sylow intersection lies in H. This does not assert
that the original intersection was already Sylow. -/
theorem Hypotheses.exists_local_sylow_le_generated (h : Hypotheses S A₁ A₂)
    (K : Subgroup G) (hr : TwoRankAtLeastTwo (A₁.subgroupOf K)) :
    ∃ P : Sylow 2 K, (S : Subgroup G).subgroupOf K ≤ P ∧
      (P : Subgroup K).map K.subtype ≤ intersectionGenerated A₁ A₂ := by
  obtain ⟨E, hE, _⟩ := hr
  have hrank := card_le_card_group E
  rw [hE] at hrank
  have hcard : Nat.card (A₁ ⊓ K : Subgroup G) = Nat.card (A₁.subgroupOf K) := by
    simpa only [subgroupOf_map_subtype] using
      (card_map_of_injective (K := A₁.subgroupOf K) K.subtype_injective)
  have hu := h.unique_large (A₁ ⊓ K) (Or.inl inf_le_left) (by omega)
  obtain ⟨P, hP⟩ := (S.isPGroup'.comap_subtype (K := K)).exists_le_sylow
  refine ⟨P, hP, ?_⟩
  apply p_overgroup_le_of_normalizers_le (U := A₁ ⊓ K) (P.isPGroup'.map K.subtype)
  · intro x hx
    exact mem_map.mpr ⟨⟨x, hx.2⟩, hP (h.left_le hx.1), rfl⟩
  · exact hu.1
  · intro W _ hXW hWH g hg
    apply (hu.2 g).mp
    have hc : conjugate (A₁ ⊓ K) g ≤ W := by
      rw [← (mem_normalizer_iff_conjugate_eq W g).mp hg]
      exact map_mono hXW
    exact hc.trans hWH

/-- Actual centralizer application of the Sylow-placement assertion in (d).
The selected Sylow contains C_S(u), and its ambient image lies in H. -/
theorem Hypotheses.exists_centralizer_sylow_le_generated (h : Hypotheses S A₁ A₂)
    (u : G) (hr : TwoRankAtLeastTwo (A₁.subgroupOf (centralizer ({u} : Set G)))) :
    ∃ P : Sylow 2 (centralizer ({u} : Set G)),
      (S : Subgroup G).subgroupOf (centralizer ({u} : Set G)) ≤ P ∧
      (P : Subgroup (centralizer ({u} : Set G))).map
        (centralizer ({u} : Set G)).subtype ≤ intersectionGenerated A₁ A₂ :=
  h.exists_local_sylow_le_generated _ hr

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end

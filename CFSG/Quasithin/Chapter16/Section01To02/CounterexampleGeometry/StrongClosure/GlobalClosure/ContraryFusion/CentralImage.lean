module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.Basic

/-!
# Central images of the source hypotheses

A central multiple of a factor element centralizes the other factor. Clause
(c), transported through a factor-element centralizer, therefore controls
all generators of the intersection-generated subgroup in a central image.
When the image factors are distinct, pair permutation aligns both image
normalizers with the original ones. This constructs every clause of the
actual `Hypotheses` record in the image Sylow subgroup.

Minimality then forces equality of the image factors if their orders agree
and their intersection does not have order two. The generated, nested, and
exceptional conclusions are all discharged explicitly. The numerical and
rank premises are kept visible for the central-diagonal quotient application.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, central quotient in the proof of (e).
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
universe u
variable {G : Type u} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

theorem LocalControl.transporter_mem_of_centralizing_factor
    (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1)
    (hc : A₁ ≤ centralizer ({g⁻¹ * a * g} : Set G) ∨
      A₂ ≤ centralizer ({g⁻¹ * a * g} : Set G)) :
    g ∈ intersectionGenerated A₁ A₂ := by
  have aux (B : Subgroup G) (hB : B ≤ A₁ ∨ B ≤ A₂)
      (hr : TwoRankAtLeastTwo B) (hBC : B ≤ centralizer ({g⁻¹ * a * g} : Set G)) :
      g ∈ intersectionGenerated A₁ A₂ := by
    obtain ⟨E, hE, _⟩ := hr
    have hcard : 2 < Nat.card B := by
      have hh := card_le_card_group E
      omega
    have hconj : conjugate B g⁻¹ ≤ intersectionGenerated A₁ A₂ := by
      rintro _ ⟨b, hb, rfl⟩
      apply h.centralizer_le_generated ha ha1
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg (MulAut.conj g)
        (mem_centralizer_singleton_iff.mp (hBC hb))
      simpa [MulAut.conj_apply, mul_assoc] using hh
    have hh := ((l.unique_large B hB hcard).2 g⁻¹).mp hconj
    exact (intersectionGenerated A₁ A₂).inv_mem_iff.mp hh
  exact hc.elim (aux A₁ (Or.inl le_rfl) h.left_rank)
    (aux A₂ (Or.inr le_rfl) h.right_rank)

theorem LocalControl.transporter_mem_of_central_image
    (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {Q : Type*} [Group Q] (q : G →* Q) (hZ : q.ker ≤ center G)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1)
    (hq : q (g⁻¹ * a * g) ∈ (A₁.map q : Set Q) ∪ A₂.map q) :
    g ∈ intersectionGenerated A₁ A₂ := by
  have aux (B C : Subgroup G) (hBC : ⁅B, C⁆ = ⊥)
      (hb : q (g⁻¹ * a * g) ∈ B.map q) :
      C ≤ centralizer ({g⁻¹ * a * g} : Set G) := by
    obtain ⟨b, hb, he⟩ := hb
    let z := (g⁻¹ * a * g) * b⁻¹
    have hz : z ∈ center G := hZ (by
      change q ((g⁻¹ * a * g) * b⁻¹) = 1
      rw [map_mul, map_inv, ← he, mul_inv_cancel])
    have heq : g⁻¹ * a * g = z * b := by dsimp [z]; group
    intro c hc
    apply mem_centralizer_singleton_iff.mpr
    rw [heq]
    have hcb : Commute c b :=
      mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hBC hb) c hc
    have hcz : Commute c z := (mem_center_iff.mp hz c)
    exact (hcz.mul_right hcb).eq
  apply l.transporter_mem_of_centralizing_factor h ha ha1
  exact hq.elim (fun hx => Or.inr (aux A₁ A₂ h.commute hx))
    (fun hx => Or.inl (aux A₂ A₁ (by rw [commutator_eq_bot_iff_le_centralizer,
      le_centralizer_iff, ← commutator_eq_bot_iff_le_centralizer]; exact h.commute) hx))

theorem LocalControl.intersectionGenerated_central_image_le
    (l : LocalControl S A₁ A₂) (h : Hypotheses S A₁ A₂)
    {Q : Type*} [Group Q] (q : G →* Q) (hq : Function.Surjective q)
    (hZ : q.ker ≤ center G) :
    intersectionGenerated (A₁.map q) (A₂.map q) ≤ (intersectionGenerated A₁ A₂).map q := by
  apply (closure_le _).mpr
  rintro x ⟨C, hC, D, hD, hcap⟩
  obtain ⟨g, rfl⟩ := hq x
  obtain ⟨w, hw1⟩ := ne_bot_iff_exists_ne_one.mp hcap
  obtain ⟨b, hb, hbq⟩ := w.property.1
  have hbU : b ∈ (A₁.map q : Set Q) ∪ A₂.map q := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with rfl | rfl
    · exact Or.inl hb
    · exact Or.inr hb
  have ha : ∃ a ∈ (A₁ : Set G) ∪ A₂, q a = b := by
    rcases hbU with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact ⟨a, Or.inl ha, rfl⟩
    · exact ⟨a, Or.inr ha, rfl⟩
  obtain ⟨a, ha, rfl⟩ := ha
  have ha1 : a ≠ 1 := by
    intro he
    apply hw1
    apply Subtype.ext
    simpa [he] using hbq.symm
  have hwU : (w : Q) ∈ (A₁.map q : Set Q) ∪ A₂.map q := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl
    · exact Or.inl w.property.2
    · exact Or.inr w.property.2
  have hqa : q (g⁻¹ * a * g) ∈ (A₁.map q : Set Q) ∪ A₂.map q := by
    have he : q (g⁻¹ * a * g) = (w : Q) := by simpa using hbq
    exact he ▸ hwU
  exact mem_map_of_mem q (l.transporter_mem_of_central_image h q hZ ha ha1 hqa)

omit [Finite G] in
private theorem map_conjugate {Q : Type*} [Group Q] (q : G →* Q)
    (A : Subgroup G) (g : G) :
    (conjugate A g).map q = conjugate (A.map q) (q g) := by
  unfold conjugate
  rw [map_map, map_map]
  congr 1
  ext x
  simp

theorem Hypotheses.central_image (h : Hypotheses S A₁ A₂)
    (l : LocalControl S A₁ A₂) {Q : Type*} [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) (hZ : q.ker ≤ center G)
    (hker : q.ker ≤ (S : Subgroup G))
    (hr₁ : TwoRankAtLeastTwo (A₁.map q)) (hr₂ : TwoRankAtLeastTwo (A₂.map q))
    (hne : A₁.map q ≠ A₂.map q) :
    Hypotheses (S.mapSurjective hq) (A₁.map q) (A₂.map q) := by
  let : Finite Q := Finite.of_surjective q hq
  let H := intersectionGenerated A₁ A₂
  let J := intersectionGenerated (A₁.map q) (A₂.map q)
  have hSH : (S : Subgroup G) ≤ H := l.sylow_le_generated h
  have hJS : J ≤ H.map q := l.intersectionGenerated_central_image_le h q hq hZ
  have hS (x : G) (hx : q x ∈ (S : Subgroup G).map q) : x ∈ S := by
    change x ∈ (S : Subgroup G)
    rw [← comap_map_eq_self hker]
    exact hx
  have hH (x : G) (hx : q x ∈ H.map q) : x ∈ H := by
    rw [← comap_map_eq_self (hker.trans hSH)]
    exact hx
  have hlift (b : Q) (hb : b ∈ (A₁.map q : Set Q) ∪ A₂.map q) :
      ∃ a ∈ (A₁ : Set G) ∪ A₂, q a = b := by
    rcases hb with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact ⟨a, Or.inl ha, rfl⟩
    · exact ⟨a, Or.inr ha, rfl⟩
  have hmem (a : G) (ha : a ∈ (A₁ : Set G) ∪ A₂) :
      q a ∈ (A₁.map q : Set Q) ∪ A₂.map q :=
    ha.elim (fun ha => Or.inl (mem_map_of_mem q ha)) (fun ha => Or.inr (mem_map_of_mem q ha))
  have hrank_ne {B : Subgroup Q} (hr : TwoRankAtLeastTwo B) : B ≠ ⊥ := by
    obtain ⟨E, hE, _⟩ := hr
    have hc := card_le_card_group E
    rw [hE] at hc
    intro he
    rw [he] at hc
    simp at hc
  have hN (i : Bool) (x : G) (hx : x ∈ S)
      (hn : q x ∈ normalizer ((if i then A₁.map q else A₂.map q) : Set Q)) :
      x ∈ normalizer ((if i then A₁ else A₂) : Set G) := by
    cases i with
    | false =>
      change q x ∈ normalizer (A₂.map q : Set Q) at hn
      change x ∈ normalizer (A₂ : Set G)
      have he := (mem_normalizer_iff_conjugate_eq _ _).mp hn
      rcases l.permutes_pair x hx with hh | hh
      · exact (mem_normalizer_iff_conjugate_eq _ _).mpr hh.2
      · exact (hne ((congrArg (map q) hh.2).symm.trans ((map_conjugate q A₂ x).trans he))).elim
    | true =>
      change q x ∈ normalizer (A₁.map q : Set Q) at hn
      change x ∈ normalizer (A₁ : Set G)
      have he := (mem_normalizer_iff_conjugate_eq _ _).mp hn
      rcases l.permutes_pair x hx with hh | hh
      · exact (mem_normalizer_iff_conjugate_eq _ _).mpr hh.1
      · exact (hne (((map_conjugate q A₁ x).trans he).symm.trans (congrArg (map q) hh.1))).elim
  refine ⟨map_mono h.left_le, map_mono h.right_le, ?_, hr₁, hr₂, ?_, ?_, ?_⟩
  · rw [← map_commutator, h.commute, Subgroup.map_bot]
  · refine ⟨?_, ?_⟩
    · intro b hb
      refine ⟨hb.elim (fun hh => left_le_intersectionGenerated (hrank_ne hr₁) hh)
        (fun hh => right_le_intersectionGenerated (hrank_ne hr₂) hh), ?_⟩
      exact hb.elim (fun hh => map_mono h.left_le hh) (fun hh => map_mono h.right_le hh)
    · intro b hb x hx hbx
      obtain ⟨a, ha, rfl⟩ := hlift b hb
      obtain ⟨g, rfl⟩ := hq x
      have hconj : q (g⁻¹ * a * g) ∈ J ⊓ (S : Subgroup G).map q := by simpa using hbx
      have ha' := h.closed_in_generated.2 a ha g (hH g (hJS hx))
        ⟨hH _ (hJS hconj.1), hS _ hconj.2⟩
      simpa using hmem _ ha'
  · refine ⟨?_, ?_⟩
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := hlift b hb
      refine ⟨mem_map_of_mem q (h.closed_in_left_normalizer.1 ha).1, ?_⟩
      apply (mem_normalizer_iff_conjugate_eq _ _).mpr
      rw [← map_conjugate, (mem_normalizer_iff_conjugate_eq _ _).mp
        (h.closed_in_left_normalizer.1 ha).2]
    · intro b hb x _ hbx
      obtain ⟨a, ha, rfl⟩ := hlift b hb
      obtain ⟨g, rfl⟩ := hq x
      have hcS : q (g⁻¹ * a * g) ∈ (S : Subgroup G).map q := by
        have hh : (q g)⁻¹ * q a * q g ∈ (S.mapSurjective hq : Subgroup Q) := hbx.1
        rw [Sylow.coe_mapSurjective] at hh
        simpa only [map_mul, map_inv] using hh
      have hcN : q (g⁻¹ * a * g) ∈ normalizer (A₁.map q : Set Q) := by simpa using hbx.2
      have ha' := h.closed_in_left_normalizer.2 a ha g (mem_top _)
        ⟨hS _ hcS, hN true _ (hS _ hcS) hcN⟩
      simpa using hmem _ ha'
  · refine ⟨?_, ?_⟩
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := hlift b hb
      refine ⟨mem_map_of_mem q (h.closed_in_right_normalizer.1 ha).1, ?_⟩
      apply (mem_normalizer_iff_conjugate_eq _ _).mpr
      rw [← map_conjugate, (mem_normalizer_iff_conjugate_eq _ _).mp
        (h.closed_in_right_normalizer.1 ha).2]
    · intro b hb x _ hbx
      obtain ⟨a, ha, rfl⟩ := hlift b hb
      obtain ⟨g, rfl⟩ := hq x
      have hcS : q (g⁻¹ * a * g) ∈ (S : Subgroup G).map q := by
        have hh : (q g)⁻¹ * q a * q g ∈ (S.mapSurjective hq : Subgroup Q) := hbx.1
        rw [Sylow.coe_mapSurjective] at hh
        simpa only [map_mul, map_inv] using hh
      have hcN : q (g⁻¹ * a * g) ∈ normalizer (A₂.map q : Set Q) := by simpa using hbx.2
      have ha' := h.closed_in_right_normalizer.2 a ha g (mem_top _)
        ⟨hS _ hcS, hN false _ (hS _ hcS) hcN⟩
      simpa using hmem _ ha'

theorem MinimalCounterexample.central_image_factors_eq
    (m : MinimalCounterexample S A₁ A₂) (l : LocalControl S A₁ A₂)
    {Q : Type u} [Group Q] [Finite Q]
    (q : G →* Q) (hq : Function.Surjective q) (hZ : q.ker ≤ center G)
    (hker : q.ker ≤ (S : Subgroup G)) (hsmall : Nat.card Q < Nat.card G)
    (hr₁ : TwoRankAtLeastTwo (A₁.map q)) (hr₂ : TwoRankAtLeastTwo (A₂.map q))
    (hcard : Nat.card (A₁.map q) = Nat.card (A₂.map q))
    (hcap : Nat.card (A₁.map q ⊓ A₂.map q : Subgroup Q) ≠ 2) :
    A₁.map q = A₂.map q := by
  by_contra hne
  have hh := m.setup.central_image l q hq hZ hker hr₁ hr₂ hne
  rcases m.smaller hsmall (S.mapSurjective hq) (A₁.map q) (A₂.map q) hh with
    hgen | ⟨hn, _⟩ | he
  · apply m.fails
    apply Or.inl
    have hle := l.intersectionGenerated_central_image_le m.setup q hq hZ
    rw [hgen] at hle
    have hmap := top_le_iff.mp hle
    have hh := congrArg (comap q) hmap
    simpa only [comap_map_eq_self (hker.trans (l.sylow_le_generated m.setup)), comap_top] using hh
  · rcases hn with hn | hn
    · exact hne (eq_of_le_of_card_ge hn hcard.ge)
    · exact hne (eq_of_le_of_card_ge hn hcard.le).symm
  · exact hcap he.2.2

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end

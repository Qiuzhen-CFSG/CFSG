module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers.Reduction
public import Theory.GroupTheory.InvolutionCentralizerFourRecognition
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.SemidihedralSquareData
public import Theory.Frattini.DihedralOmega

/-!
# Recognizing the ambient mixed-centralizer factors

The model calculation at the end of Aschbacher's printed p.95 and the start
of p.96 has two cases. An elementary four involution centralizer recognizes
the ambient two-group, including the case where the involution is central.
A nonabelian dihedral or semidihedral centralizer has center of order two;
its normalizer centralizes that center, and the two-group normalizer condition
forces the centralizer to be the entire factor.

The final applications use the actual equivalence between
`Aᵢ.subgroupOf C_G(ab)` and `C_{Aᵢ}(aᵢ)`. Conjugacy inside `C_G(ab)` then
recognizes both ambient factors. The last definition isolates the remaining
source argument for those full factors; it does not assert its conclusion.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J.
Math. 19 (1975), Lemma 3.4(g), pp.95–96, DOI 10.1215/ijm/1256050927.
The reusable four-centralizer recognition is proved in
`Theory.GroupTheory.InvolutionCentralizerFourRecognition`; the semidihedral
center calculation uses the explicit standard model and presentation.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
universe u v

/-- Transport the actual model equivalences, including their parameter bounds. -/
theorem DihedralOrSemidihedral.of_equiv {P : Type u} {Q : Type v}
    [Group P] [Group Q] (h : DihedralOrSemidihedral P) (e : P ≃* Q) :
    DihedralOrSemidihedral Q := by
  rcases h with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  · exact Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨n, hn, ⟨e.symm.trans f⟩⟩

private theorem dihedral_center_card {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (center (DihedralGroup (2 ^ n))) = 2 := by
  have hp : 0 < 2 ^ (n - 1) := by positivity
  have he : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hr : DihedralGroup.r ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) =
      DihedralGroup.r (1 : ZMod (2 ^ n)) ^ (2 ^ (n - 1)) := by
    simp [DihedralGroup.r_pow]
  rw [DihedralFrattini.center_eq_half hn, Nat.card_zpowers, hr,
    orderOf_pow_of_dvd (by omega) (by rw [DihedralGroup.orderOf_r_one, he]; exact dvd_mul_right _ _),
    DihedralGroup.orderOf_r_one, he, Nat.mul_div_cancel_left _ hp]

/-- The four-group is the only model whose center has order greater than two. -/
theorem DihedralOrSemidihedral.four_or_center_two {P : Type u} [Group P]
    (h : DihedralOrSemidihedral P) :
    (Nat.card P = 4 ∧ ∀ x : P, x ^ 2 = 1) ∨ Nat.card (center P) = 2 := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · by_cases he : n = 1
    · subst n
      change P ≃* DihedralGroup 2 at e
      refine Or.inl ⟨(Nat.card_congr e.toEquiv).trans (by norm_num [DihedralGroup.nat_card]), ?_⟩
      intro x
      apply e.injective
      simpa only [map_pow, map_one, pow_one, pow_two, map_mul] using IsKleinFour.mul_self (e x)
    · exact Or.inr ((Nat.card_congr (centerCongr e).toEquiv).trans
        (dihedral_center_card (by omega)))
  · exact Or.inr ((Nat.card_congr (centerCongr e).toEquiv).trans
      (Semidihedral.square_data hn (Semidihedral.standardRotation n hn)
        (Semidihedral.standardReflection n hn) (Semidihedral.standardRotation_order n hn)
        (Semidihedral.standardReflection_order n hn) (Semidihedral.standard_conjugation n hn)
        (Semidihedral.standard_generators n hn)).1)

private theorem centralizer_eq_top_of_center_card_two
    {P : Type u} [Group P] [Finite P] (hp : IsPGroup 2 P)
    (a : P) (hc : Nat.card (center (centralizer ({a} : Set P))) = 2) :
    centralizer ({a} : Set P) = ⊤ := by
  let C := centralizer ({a} : Set P)
  let : Group.IsNilpotent P := hp.isNilpotent
  have hc' : Nat.card (centerIn C) = 2 := by
    rw [centerIn_eq_map_center, card_map_of_injective C.subtype_injective]
    exact hc
  have ha : a ∈ centerIn C := by
    refine ⟨mem_centralizer_singleton_iff.mpr rfl, ?_⟩
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hself : normalizer (C : Set P) ≤ C := by
    intro g hg
    apply mem_centralizer_singleton_iff.mpr
    exact centralizes_of_normalizes_card_two hc'
      (normalizes_centerIn (S := C) (A := normalizer (C : Set P)) le_rfl) hg a ha |>.symm
  exact normalizerCondition_iff_only_full_group_self_normalizing.mp
    Group.normalizerCondition_of_isNilpotent C (le_antisymm hself le_normalizer)

private theorem model_of_centralizer_four
    {P : Type u} [Group P] [Finite P] (hp : IsPGroup 2 P)
    (a : P) (ha : orderOf a = 2)
    (hc : Nat.card (centralizer ({a} : Set P)) = 4)
    (hsq : ∀ x : centralizer ({a} : Set P), x ^ 2 = 1) :
    DihedralOrSemidihedral P := by
  by_cases hz : a ∈ center P
  · have he : centralizer ({a} : Set P) = ⊤ := by
      apply top_unique
      intro x _
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hz x)
    have hcP : Nat.card P = 4 := by simpa only [he, card_top] using hc
    have hsP (x : P) : x ^ 2 = 1 := by
      exact congrArg Subtype.val (hsq ⟨x, he ▸ mem_top x⟩)
    have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    let : IsKleinFour P := ⟨hcP, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr
      (fun x hx => orderOf_eq_prime_iff.mpr ⟨hsP x, hx⟩)⟩
    refine Or.inl ⟨1, le_rfl, ?_⟩
    change Nonempty (P ≃* DihedralGroup 2)
    exact IsKleinFour.nonempty_mulEquiv
  · rcases exists_dihedral_or_semidihedral_of_involution_centralizer_card_four
      hp a ha hz hc with ⟨r, ⟨e⟩⟩ | ⟨n, hn, hcard, x, y, hx, hy, hxy, hgen⟩
    · obtain ⟨n, hn⟩ := hp.exists_orderOf_eq_pow (e.symm (DihedralGroup.r 1))
      have hr : r = 2 ^ n := by
        simpa only [e.symm.orderOf_eq, DihedralGroup.orderOf_r_one] using hn
      subst r
      refine Or.inl ⟨n, ?_, ⟨e⟩⟩
      have hbound := card_le_card_group (centralizer ({a} : Set P))
      rw [hc, Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at hbound
      by_contra h
      have : n = 0 := by omega
      simp [this] at hbound
    · exact Or.inr ⟨n, hn, Semidihedral.standardModel_equiv_of_presentation
        hn x y hx hy hxy hgen hcard⟩

/-- An actual dihedral or semidihedral involution centralizer determines
an actual model of the whole two-group. -/
theorem DihedralOrSemidihedral.of_involution_centralizer
    {P : Type u} [Group P] [Finite P] (hp : IsPGroup 2 P)
    (a : P) (ha : orderOf a = 2)
    (hm : DihedralOrSemidihedral (centralizer ({a} : Set P))) :
    DihedralOrSemidihedral P := by
  rcases hm.four_or_center_two with ⟨hc, hs⟩ | hc
  · exact model_of_centralizer_four hp a ha hc hs
  · have he := centralizer_eq_top_of_center_card_two hp a hc
    exact hm.of_equiv ((MulEquiv.subgroupCongr he).trans (Subgroup.topEquiv))

private def restrictedCentralizerEquiv
    {G : Type u} [Group G] (A K : Subgroup G) (a : A)
    (he : A ⊓ K = A ⊓ centralizer ({(a : G)} : Set G)) :
    A.subgroupOf K ≃* centralizer ({a} : Set A) := by
  have hc (x : G) (hx : x ∈ A) : x ∈ K ↔ x * (a : G) = (a : G) * x := by
    constructor
    · intro hk
      exact mem_centralizer_singleton_iff.mp ((he ▸ (show x ∈ A ⊓ K from ⟨hx, hk⟩)).2)
    · intro heq
      exact (he.symm ▸ (show x ∈ A ⊓ centralizer ({(a : G)} : Set G) from
        ⟨hx, mem_centralizer_singleton_iff.mpr heq⟩)).2
  exact
    { toFun := fun x => ⟨⟨((x : K) : G), x.property⟩,
        mem_centralizer_singleton_iff.mpr (Subtype.ext ((hc _ x.property).mp x.val.property))⟩
      invFun := fun x => ⟨⟨((x : A) : G), (hc _ x.val.property).mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }

/-- The four-group and nonabelian cases recognize both ambient factors from
conjugate mixed centralizer factors. The conjugacy is inside the literal C_G(ab). -/
theorem Hypotheses.factor_models_of_conjugate_mixed_centralizers
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}
    (h : Hypotheses S A₁ A₂) {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₂)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2)
    (g : centralizer ({a * b} : Set G))
    (hg : conjugate (A₁.subgroupOf (centralizer ({a * b} : Set G))) g =
      A₂.subgroupOf (centralizer ({a * b} : Set G)))
    (hm : DihedralOrSemidihedral (A₁.subgroupOf (centralizer ({a * b} : Set G)))) :
    DihedralOrSemidihedral A₁ ∧ DihedralOrSemidihedral A₂ := by
  have hi := h.mixed_centralizer_intersections ha hb
  have hm₂ : DihedralOrSemidihedral (A₂.subgroupOf (centralizer ({a * b} : Set G))) :=
    hm.of_equiv (((MulAut.conj g⁻¹).subgroupMap _).trans (MulEquiv.subgroupCongr hg))
  constructor
  · exact DihedralOrSemidihedral.of_involution_centralizer
      (S.isPGroup'.to_le h.left_le) (⟨a, ha⟩ : A₁) (by simpa using ha2)
      (hm.of_equiv (restrictedCentralizerEquiv A₁ _ ⟨a, ha⟩ hi.1))
  · exact DihedralOrSemidihedral.of_involution_centralizer
      (S.isPGroup'.to_le h.right_le) (⟨b, hb⟩ : A₂) (by simpa using hb2)
      (hm₂.of_equiv (restrictedCentralizerEquiv A₂ _ ⟨b, hb⟩ hi.2))

/-- The nonabelian case in the first sentence of printed p.96: the
restricted factor is the entire ambient factor. -/
theorem Hypotheses.mixed_centralizer_left_eq_of_nonabelian
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}
    (h : Hypotheses S A₁ A₂) {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₂)
    (hm : DihedralOrSemidihedral (A₁.subgroupOf (centralizer ({a * b} : Set G))))
    (hn : ¬ IsMulCommutative (A₁.subgroupOf (centralizer ({a * b} : Set G)))) :
    A₁ ⊓ centralizer ({a * b} : Set G) = A₁ := by
  have hi := (h.mixed_centralizer_intersections ha hb).1
  let e := restrictedCentralizerEquiv A₁ (centralizer ({a * b} : Set G)) ⟨a, ha⟩ hi
  have hz : Nat.card (center (centralizer ({(⟨a, ha⟩ : A₁)} : Set A₁))) = 2 := by
    rcases hm.four_or_center_two with ⟨_, hs⟩ | hc
    · exact (hn (isMulCommutative_of_forall_sq_one hs)).elim
    · exact (Nat.card_congr (centerCongr e).toEquiv).symm.trans hc
  have he := centralizer_eq_top_of_center_card_two (S.isPGroup'.to_le h.left_le)
    (⟨a, ha⟩ : A₁) hz
  rw [hi]
  apply inf_eq_left.mpr
  intro x hx
  have hxC : (⟨x, hx⟩ : A₁) ∈ centralizer ({(⟨a, ha⟩ : A₁)} : Set A₁) :=
    he ▸ mem_top _
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hxC))

/-- The remaining proper-centralizer source branch after recognizing the full
ambient factors. This is an obligation, not an asserted consequence of minimality.
Conjugacy remains inside the literal mixed centralizer. -/
def ModelFactorMixedCentralizerBound {G : Type u} [Group G]
    (A₁ A₂ : Subgroup G) : Prop :=
  DihedralOrSemidihedral A₁ → DihedralOrSemidihedral A₂ →
    ∀ a ∈ A₁, ∀ b ∈ A₂, orderOf a = 2 → orderOf b = 2 → a * b ≠ 1 →
      let K := centralizer ({a * b} : Set G)
      K ≠ ⊤ → ∀ g : K, conjugate (A₁.subgroupOf K) g = A₂.subgroupOf K →
        K ≤ intersectionGenerated A₁ A₂

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

end

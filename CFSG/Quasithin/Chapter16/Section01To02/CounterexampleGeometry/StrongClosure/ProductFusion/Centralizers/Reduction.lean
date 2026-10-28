module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.FinalParagraph
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalControl
public import Theory.GroupTheory.PGroup.InvolutionFour

/-!
# Reductions for the mixed-involution centralizer bound

For commuting factors, C_A(ab) = C_A(a). Every involution in a finite
two-group of rank at least two belongs to an elementary four, giving the
rank hypotheses inside C_G(ab). If either restricted factor lies in the
other ambient factor, ab belongs to that factor and its unique conjugate
membership immediately bounds its centralizer.

The two final definitions specify the remaining proper-centralizer model
exclusion and central-quotient exclusion. They are proof obligations, not
assertions that the exclusions hold in a minimal counterexample.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J.
Math. 19 (1975), Lemma 3.4(g), pp.95–96, DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
universe u
variable {G : Type u} [Group G] [Finite G]
variable {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

omit [Finite G] in
private theorem commuting_factors (h : Hypotheses S A₁ A₂)
    {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₂) : Commute a b :=
  (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h.commute ha) b hb).symm

omit [Finite G] in
private theorem inf_centralizer_mul {A : Subgroup G} {a b : G}
    (hb : ∀ x ∈ A, Commute x b) :
    A ⊓ centralizer ({a * b} : Set G) = A ⊓ centralizer ({a} : Set G) := by
  ext x
  constructor
  · rintro ⟨hxA, hx⟩
    refine ⟨hxA, mem_centralizer_singleton_iff.mpr ?_⟩
    have hc : Commute x (a * b) := mem_centralizer_singleton_iff.mp hx
    have hh := hc.mul_right (hb x hxA).inv_right
    simpa using hh.eq
  · rintro ⟨hxA, hx⟩
    have hc : Commute x a := mem_centralizer_singleton_iff.mp hx
    exact ⟨hxA, mem_centralizer_singleton_iff.mpr (hc.mul_right (hb x hxA)).eq⟩

omit [Finite G] in
/-- Identify both literal ambient intersections with the factor involution centralizers. -/
theorem Hypotheses.mixed_centralizer_intersections (h : Hypotheses S A₁ A₂)
    {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₂) :
    (A₁ ⊓ centralizer ({a * b} : Set G) = A₁ ⊓ centralizer ({a} : Set G)) ∧
    (A₂ ⊓ centralizer ({a * b} : Set G) = A₂ ⊓ centralizer ({b} : Set G)) := by
  refine ⟨inf_centralizer_mul (fun _ hx => commuting_factors h hx hb), ?_⟩
  rw [(commuting_factors h ha hb).eq]
  exact inf_centralizer_mul (fun _ hx => (commuting_factors h ha hx).symm)

omit [Finite G] in
/-- A nonidentity product of the two commuting factor involutions is an involution. -/
theorem Hypotheses.mixed_orderOf (h : Hypotheses S A₁ A₂)
    {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₂)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a * b ≠ 1) :
    orderOf (a * b) = 2 := by
  apply orderOf_eq_prime_iff.mpr
  refine ⟨?_, hab⟩
  rw [(commuting_factors h ha hb).mul_pow]
  simp only [(orderOf_eq_prime_iff.mp ha2).1, (orderOf_eq_prime_iff.mp hb2).1, one_mul]

private theorem factor_centralizer_rank {A B : Subgroup G}
    (hp : IsPGroup 2 A) (hr : TwoRankAtLeastTwo A)
    (hc : ∀ x ∈ A, ∀ y ∈ B, Commute x y)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B) (ha2 : orderOf a = 2) :
    TwoRankAtLeastTwo (A.subgroupOf (centralizer ({a * b} : Set G))) := by
  obtain ⟨E, hE, hEsq⟩ := hr
  let : IsElementaryAbelian 2 E :=
    { toIsMulCommutative := isMulCommutative_of_forall_sq_one hEsq
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hEsq }
  obtain ⟨V, hV, hVcard, haV⟩ := hp.exists_elementary_four_mem_of_four_le E hE.ge
    (⟨a, ha⟩ : A) (by simpa using ha2)
  let := hV
  let K := centralizer ({a * b} : Set G)
  have hVK (x : V) : ((x : A) : G) ∈ K := by
    apply mem_centralizer_singleton_iff.mpr
    have hxa : Commute ((x : A) : G) a := by
      have he := congrArg (fun v : V => ((v : A) : G))
        (mul_comm x (⟨⟨a, ha⟩, haV⟩ : V))
      exact he
    exact (hxa.mul_right (hc _ x.val.property b hb)).eq
  let f : V →* A.subgroupOf K :=
    { toFun := fun x => ⟨⟨((x : A) : G), hVK x⟩, x.val.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : A.subgroupOf K => ((v : K) : G)) he
  refine ⟨f.range, ?_, ?_⟩
  · change Nat.card (Set.range f) = 4
    exact (Nat.card_range_of_injective hf).trans hVcard
  · rintro ⟨x, y, rfl⟩
    apply Subtype.ext
    change f y ^ 2 = 1
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) y, map_one]

/-- Both factors restricted to the mixed centralizer contain an elementary four. -/
theorem Hypotheses.mixed_centralizer_ranks (h : Hypotheses S A₁ A₂)
    {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₂)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) :
    TwoRankAtLeastTwo (A₁.subgroupOf (centralizer ({a * b} : Set G))) ∧
    TwoRankAtLeastTwo (A₂.subgroupOf (centralizer ({a * b} : Set G))) := by
  constructor
  · exact factor_centralizer_rank (S.isPGroup'.to_le h.left_le) h.left_rank
      (fun _ hx _ hy => commuting_factors h hx hy) ha hb ha2
  · rw [(commuting_factors h ha hb).eq]
    exact factor_centralizer_rank (S.isPGroup'.to_le h.right_le) h.right_rank
      (fun _ hx _ hy => (commuting_factors h hy hx).symm) hb ha hb2

private theorem centralizer_factor_le (h : Hypotheses S A₁ A₂)
    (hc : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    {x : G} (hx : x ∈ (A₁ : Set G) ∪ A₂) (hne : x ≠ 1) :
    centralizer ({x} : Set G) ≤ intersectionGenerated A₁ A₂ := by
  intro g hg
  apply ((h.unique_of_closed hc hx hne).2 g).mp
  have he := mem_centralizer_singleton_iff.mp hg
  have he' : g⁻¹ * x * g = x := by
    calc
      g⁻¹ * x * g = g⁻¹ * (x * g) := mul_assoc _ _ _
      _ = g⁻¹ * (g * x) := by rw [he]
      _ = x := inv_mul_cancel_left _ _
  rw [he']
  exact h.union_subset_generated hx

/-- An unbounded mixed centralizer forces both local noncontainments in source (d). -/
theorem Hypotheses.mixed_centralizer_nonnesting (h : Hypotheses S A₁ A₂)
    (hc : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤)
    {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₂) (hab : a * b ≠ 1)
    (hK : ¬ centralizer ({a * b} : Set G) ≤ intersectionGenerated A₁ A₂) :
    (¬ A₁ ⊓ centralizer ({a * b} : Set G) ≤ A₂) ∧
    (¬ A₂ ⊓ centralizer ({a * b} : Set G) ≤ A₁) := by
  have hac : a ∈ centralizer ({a * b} : Set G) :=
    mem_centralizer_singleton_iff.mpr ((Commute.refl a).mul_right (commuting_factors h ha hb)).eq
  have hbc : b ∈ centralizer ({a * b} : Set G) :=
    mem_centralizer_singleton_iff.mpr ((commuting_factors h ha hb).symm.mul_right (Commute.refl b)).eq
  constructor
  · intro hn
    exact hK (centralizer_factor_le h hc (Or.inr (A₂.mul_mem (hn ⟨ha, hac⟩) hb)) hab)
  · intro hn
    exact hK (centralizer_factor_le h hc (Or.inl (A₁.mul_mem ha (hn ⟨hb, hbc⟩))) hab)

/-- The model exclusion needed only in a proper centralizer outside H. -/
def MixedCentralizerModelExclusion (A₁ A₂ : Subgroup G) : Prop :=
  ∀ a ∈ A₁, ∀ b ∈ A₂, orderOf a = 2 → orderOf b = 2 → a * b ≠ 1 →
    let K := centralizer ({a * b} : Set G)
    K ≠ ⊤ → (¬ K ≤ intersectionGenerated A₁ A₂) →
    ∀ g : K, conjugate (A₁.subgroupOf K) g = A₂.subgroupOf K →
      ¬ DihedralOrSemidihedral (A₁.subgroupOf K)

/-- The remaining central-quotient branch, before product fusion. -/
def MixedCentralQuotientExclusion (A₁ A₂ : Subgroup G) : Prop :=
  ∀ a ∈ A₁, ∀ b ∈ A₂, orderOf a = 2 → orderOf b = 2 → a * b ≠ 1 →
    a * b ∉ center G

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end

module

public import Theory.GroupAction.NormalizerFrattini
public import Theory.Frattini.PGroup
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.SpecificGroups.SL2.PrimeFieldOddSubgroups

/-!
# Irreducible noncyclic actors on small elementary abelian groups

A finite noncyclic odd p-subgroup P whose full normalizer acts irreducibly
on P/Φ(P) acts trivially on an elementary abelian r-group of order at most
r² whenever the action extends to the ambient finite group.

Embed the automorphism group in GL₂ over the prime field, padding smaller
spaces. The determinant image is cyclic. Its normalizer-invariant kernel
is either all of P or lies in Φ(P); the latter would make P cyclic by
lifting a generator of the image. Thus the image lies in SL₂, where every
odd-prime subgroup is cyclic. Applying the same kernel argument again
makes the entire image trivial. All maps are restrictions of the supplied
ambient action, so the kernel invariance is proved for its actual normalizer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.1.32,
printed p.28. The proof does not require exponent p or oddness of r; the
last theorem retains both hypotheses for the source application.
-/

namespace Subgroup
variable {G H : Type*} [Group G] [Finite G] [Group H]

private theorem cyclic_of_ker_le_frattini (f : G →* H)
    (hf : IsCyclic f.range) (hk : f.ker ≤ frattini G) : IsCyclic G := by
  obtain ⟨y, hy⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top f.range).mp hf
  obtain ⟨x, rfl⟩ := hy ▸ mem_zpowers y
  have hm : (zpowers x).map f = f.range := by rwa [MonoidHom.map_zpowers]
  have hs : zpowers x ⊔ f.ker = ⊤ := by
    have h := congrArg (Subgroup.comap f) hm
    simpa only [comap_map_eq, MonoidHom.comap_range_self] using h
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨x, frattini_nongenerating ?_⟩
  exact top_unique (hs ▸ sup_le_sup_left hk _)

/-- A cyclic image of a noncyclic normalizer-irreducible Frattini actor is trivial.
The kernel is invariant because the map is defined on the whole ambient group. -/
public theorem IsNormalizerFrattiniIrreducible.comp_eq_one_of_cyclic_range
    {P : Subgroup G} (hirr : IsNormalizerFrattiniIrreducible P)
    (hnc : ¬ IsCyclic P) (ρ : G →* H) (hc : IsCyclic (ρ.comp P.subtype).range) :
    ρ.comp P.subtype = 1 := by
  let f := ρ.comp P.subtype
  have hk := hirr.invariant_le_frattini_or_eq f.ker (by
    intro s d hd
    change ρ ((s : G) * (d : G) * (s : G)⁻¹) = 1
    change ρ (d : G) = 1 at hd
    simp only [map_mul, map_inv, hd, mul_one, mul_inv_cancel])
  rcases hk with hk | hk
  · exact (hnc (cyclic_of_ker_le_frattini f hc hk)).elim
  · ext x
    exact (show x ∈ f.ker from hk ▸ mem_top x)

/-- A noncyclic odd-prime actor with irreducible normalizer action on its Frattini
quotient has trivial image in GL₂ over any prime field. -/
public theorem IsNormalizerFrattiniIrreducible.comp_eq_one_of_generalLinear_two
    {P : Subgroup G} (hirr : IsNormalizerFrattiniIrreducible P)
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] (hp : p ≠ 2)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod r)) :
    ρ.comp P.subtype = 1 := by
  let d := Matrix.GeneralLinearGroup.det.comp ρ
  have hd : d.comp P.subtype = 1 := hirr.comp_eq_one_of_cyclic_range hnc d
    (isCyclic_subgroup_units _)
  let f := ρ.comp P.subtype
  let j : f.range →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r) := {
    toFun x := ⟨x.val.val, by
      obtain ⟨y, hy⟩ := x.property
      rw [← hy]
      exact congrArg Units.val (DFunLike.congr_fun hd y)⟩
    map_one' := rfl
    map_mul' _ _ := rfl
  }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Units.ext (congrArg Subtype.val h))
  have hc : IsCyclic f.range := Matrix.SpecialLinearGroup.isCyclic_of_odd_pGroup_injective_primeField
    (hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective) hp j hj
  exact hirr.comp_eq_one_of_cyclic_range hnc ρ hc

/-- Such an actor acts trivially on every elementary abelian r-group of order
at most r². This stronger form needs neither oddness of r nor exponent p. -/
public theorem IsNormalizerFrattiniIrreducible.comp_eq_one_of_elementaryAbelian_card_le_sq
    {P : Subgroup G} (hirr : IsNormalizerFrattiniIrreducible P)
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] (hp : p ≠ 2)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian r V]
    (hcard : Nat.card V ≤ r ^ 2) (ρ : G →* MulAut V) :
    ρ.comp P.subtype = 1 := by
  obtain ⟨e, he⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le V hcard
  have h := hirr.comp_eq_one_of_generalLinear_two hp hP hnc (e.comp ρ)
  apply MonoidHom.ext
  intro x
  apply he
  exact (DFunLike.congr_fun h x).trans e.map_one.symm

/-- Application to the literal conjugation action on R/Φ(R). Together with
a source bound on that quotient's order, this discharges the trivial-action
premise in the group-theoretic reductions of A.1.32. -/
public theorem IsNormalizerFrattiniIrreducible.frattiniConjugationHom_eq_one_of_card_le_sq
    {P R : Subgroup G} [R.Normal]
    (hirr : IsNormalizerFrattiniIrreducible P)
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] (hp : p ≠ 2)
    (hR : IsPGroup r R) (hcard : Nat.card (R ⧸ frattini R) ≤ r ^ 2)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) :
    frattiniConjugationHom P R le_normalizer_of_normal = 1 := by
  let : Fact (IsPGroup r R) := ⟨hR⟩
  let : IsElementaryAbelian r (R ⧸ frattini R) := isElementaryAbelian_quotient_frattini
  let ρ : G →* MulAut (R ⧸ frattini R) :=
    (quotientAut (frattini R)).comp MulAut.conjNormal
  have h := hirr.comp_eq_one_of_elementaryAbelian_card_le_sq hp hP hnc hcard ρ
  have hcompat : frattiniConjugationHom P R le_normalizer_of_normal = ρ.comp P.subtype := by
    apply MonoidHom.ext
    intro a
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro x
    rfl
  exact hcompat.trans h

/-- The small linear-action obstruction in A.1.32, with the source's odd-prime
and exponent hypotheses. The actual ambient action restricts trivially to P. -/
public theorem IsNormalizerFrattiniIrreducible.small_linear_action_eq_one
    {P : Subgroup G} (hirr : IsNormalizerFrattiniIrreducible P)
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] (_hr : Odd r) (hp : Odd p)
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian r V]
    (hcard : Nat.card V ≤ r ^ 2) (hP : IsPGroup p P)
    (_hexp : Monoid.exponent P ∣ p) (hnc : ¬ IsCyclic P) (ρ : G →* MulAut V) :
    ρ.comp P.subtype = 1 := by
  apply hirr.comp_eq_one_of_elementaryAbelian_card_le_sq (p := p) _ hP hnc hcard ρ
  rintro rfl
  exact hp.not_two_dvd_nat (dvd_refl 2)

end Subgroup

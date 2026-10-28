module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers.ModelExclusion.Recognition
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers.ModelExclusion.FullFactorGeometry.LocalException

/-!
# Proper mixed centralizers under global strong closure

This proves the full-factor bound consumed by mixed-centralizer recognition.
In fact, the direct induction argument proves the bound for every proper
centralizer of a nonidentity product of factor involutions.

Reselect a Sylow subgroup in the centralizer using the checked source (c)
construction. Both restricted factors retain rank at least two and nonnesting,
and ambient strong closure restricts to the new Sylow subgroup. Apply minimality
to this literal centralizer. The generated and nested alternatives are immediate;
`LocalException` excludes the remaining alternative using the central involution.
The bound transports back by the actual conjugation equivalence inside H.

Only pair permutation is used from the explicit `LocalControl` input. Neither
mixed-product unique membership nor an assumed centralizer model exclusion is
used. The last theorem has exactly the interface requested by the recognition
consumer, including both actual ambient model hypotheses.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J.
Math. 19 (1975), Lemma 3.4(g), bottom of p.95 and top of p.96,
DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
universe u
variable {G : Type u} [Group G] [Finite G] {S : Sylow 2 G} {A B : Subgroup G}

private theorem factor_centralizer_bound
    (h : Hypotheses S A B)
    (hc : IsStronglyClosedSet ((A : Set G) ∪ B) (S : Subgroup G) ⊤)
    {x : G} (hx : x ∈ (A : Set G) ∪ B) (hne : x ≠ 1) :
    centralizer ({x} : Set G) ≤ intersectionGenerated A B := by
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

/-- Proper mixed centralizers are bounded using global strong closure and
induction inside a reselected centralizer. -/
theorem MinimalCounterexample.proper_mixed_centralizer_bound_of_closed
    (m : MinimalCounterexample S A B)
    (hc : IsStronglyClosedSet ((A : Set G) ∪ B) (S : Subgroup G) ⊤)
    (hl : LocalControl S A B)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) (hab : a * b ≠ 1)
    (hproper : centralizer ({a * b} : Set G) ≠ ⊤) :
    centralizer ({a * b} : Set G) ≤ intersectionGenerated A B := by
  classical
  by_contra hK
  have hr := m.setup.mixed_centralizer_ranks ha hb ha2 hb2
  have hn := m.setup.mixed_centralizer_nonnesting hc ha hb hab hK
  have hu : a * b ∈ A ⊔ B := mul_mem_sup ha hb
  have hu2 := m.setup.mixed_orderOf ha hb ha2 hb2 hab
  obtain ⟨g, hg, hv, _hreturn, ⟨P, hP⟩, hrA, hrB, hnA, hnB⟩ :=
    m.setup.exists_centralizer_reselection hl.permutes_pair (a * b) hu hr.1 hr.2 hn.1 hn.2
  let v := g⁻¹ * (a * b) * g
  let L := centralizer ({v} : Set G)
  have hL : ¬ L ≤ intersectionGenerated A B := by
    intro hLH
    apply hK
    intro x hx
    have hxe : (centralizerReselectionEquiv (a * b) g ⟨x, hx⟩ : G) ∈ L :=
      (centralizerReselectionEquiv (a * b) g ⟨x, hx⟩).property
    rw [centralizerReselectionEquiv_apply] at hxe
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using
      (intersectionGenerated A B).mul_mem
        ((intersectionGenerated A B).mul_mem hg (hLH hxe))
        ((intersectionGenerated A B).inv_mem hg)
  have hLproper : L ≠ ⊤ := by
    intro htop
    apply hproper
    apply top_unique
    intro x _
    have hx : g⁻¹ * x * g ∈ L := htop.symm ▸ mem_top _
    apply mem_centralizer_singleton_iff.mpr
    apply (MulAut.conj g⁻¹).injective
    simpa only [v, map_mul, MulAut.conj_apply, inv_inv, mul_assoc, mul_inv_cancel_left] using
      mem_centralizer_singleton_iff.mp hx
  have hlocal : Hypotheses P (A.subgroupOf L) (B.subgroupOf L) := by
    apply m.setup.restrict L P hP hrA hrB
    · intro x hx hN
      have hxS : (x : G) ∈ S := by
        change x ∈ (P : Subgroup L) at hx
        rw [hP] at hx
        exact hx
      exact normalizer_restriction_of_permuting
        (fun s hs => (hl.permutes_pair s hs).imp And.left And.left) hnA x hxS hN
    · intro x hx hN
      have hxS : (x : G) ∈ S := by
        change x ∈ (P : Subgroup L) at hx
        rw [hP] at hx
        exact hx
      exact normalizer_restriction_of_permuting
        (fun s hs => (hl.permutes_pair s hs).imp And.right And.right) hnB x hxS hN
  have hclosed : IsStronglyClosedSet
      ((A.subgroupOf L : Set L) ∪ B.subgroupOf L) (P : Subgroup L) ⊤ := by
    refine ⟨fun x hx => hx.elim (fun hh => hlocal.left_le hh) (fun hh => hlocal.right_le hh), ?_⟩
    intro x hx y _ hxy
    have hxyS : (y : G)⁻¹ * (x : G) * (y : G) ∈ S := by
      change y⁻¹ * x * y ∈ (P : Subgroup L) at hxy
      rw [hP] at hxy
      exact hxy
    exact hc.2 x hx y (mem_top _) hxyS
  have hnlocalA : ¬ A.subgroupOf L ≤ B.subgroupOf L := by
    intro hnest
    exact hnA (fun x hx => hnest (show (⟨x, hx.2⟩ : L) ∈ A.subgroupOf L from hx.1))
  have hnlocalB : ¬ B.subgroupOf L ≤ A.subgroupOf L := by
    intro hnest
    exact hnB (fun x hx => hnest (show (⟨x, hx.2⟩ : L) ∈ B.subgroupOf L from hx.1))
  have hv2 : orderOf v = 2 := by
    simpa only [v, MulAut.conj_apply, inv_inv] using
      ((MulAut.conj g⁻¹).orderOf_eq (a * b)).trans hu2
  have hvne : v ≠ 1 := (orderOf_eq_prime_iff.mp hv2).2
  have hvA : v ∉ A := fun hh => hL (factor_centralizer_bound m.setup hc (Or.inl hh) hvne)
  have hvB : v ∉ B := fun hh => hL (factor_centralizer_bound m.setup hc (Or.inr hh) hvne)
  let vL : L := ⟨v, mem_centralizer_singleton_iff.mpr rfl⟩
  have hvZ : vL ∈ center L := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  have hvprod : vL ∈ A.subgroupOf L ⊔ B.subgroupOf L := by
    obtain ⟨c, hcA, d, hdB, hcd, hcL, hdL⟩ := centralizer_reselection_factorization m.setup.commute hv
    have he : (⟨c, hcL⟩ : L) * ⟨d, hdL⟩ = vL := Subtype.ext hcd
    exact he ▸ mul_mem_sup (show (⟨c, hcL⟩ : L) ∈ A.subgroupOf L from hcA)
      (show (⟨d, hdL⟩ : L) ∈ B.subgroupOf L from hdB)
  have hcard : Nat.card L < Nat.card G :=
    lt_of_le_of_ne (card_le_card_group L) (fun he => hLproper (L.eq_top_of_card_eq he))
  rcases m.smaller hcard P (A.subgroupOf L) (B.subgroupOf L) hlocal with
    hgen | ⟨hnest, _⟩ | hex
  · apply hL
    intro x hx
    apply intersectionGenerated_subgroupOf_le L (x := ⟨x, hx⟩)
    rw [hgen]
    exact mem_top _
  · exact hnest.elim hnlocalA hnlocalB
  · exact Hypotheses.not_exceptional_of_closed_central_involution hlocal hclosed
      (hlocal.permutes_pair_of_nonnested hnlocalA hnlocalB) vL hvprod
      (by simpa [vL] using hv2) hvZ hvA hvB hex

/-- The full-factor branch requested by the recognition consumer. -/
theorem MinimalCounterexample.modelFactorMixedCentralizerBound_of_closed
    (m : MinimalCounterexample S A B)
    (hc : IsStronglyClosedSet ((A : Set G) ∪ B) (S : Subgroup G) ⊤)
    (hl : LocalControl S A B) : ModelFactorMixedCentralizerBound A B := by
  intro _ _ a ha b hb ha2 hb2 hab K hproper _ _
  exact m.proper_mixed_centralizer_bound_of_closed hc hl ha hb ha2 hb2 hab hproper

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

end

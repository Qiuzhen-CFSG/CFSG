module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.SylowImageIntersection

/-!
# Sylow transport for the sufficient invariant embedding variant

The additional genuine hypothesis that T is Sylow in H restricts to LT and
to the relatively normal component L. Its images remain Sylow after the
two-core quotient and the central quotient. Sylow maximality also identifies
the image of T intersect L with the intersection of the two images.

The literal equality PT = TP follows separately from the two factorizations
in LocalInput, and is preserved under restriction and homomorphisms. For
p greater than three, the complement has full three-residual.

The input record contains only the supplied local and component hypotheses.
It neither changes LocalInput nor asserts the classification for arbitrary
two-groups. Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.4, printed pp.510–511; Lemma A.3.15, pp.50–51.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
universe u
variable {G : Type u} [Group G]

/-- The separately strengthened local input for the invariant-component case.
No embedding alternative or conclusion is included among its fields. -/
structure SylowInput (κ : GroupClass.{u}) (p : ℕ) (T X P H L : Subgroup G) : Prop
    extends LocalInput p T X P H where
  sqtk : IsSQTK κ H
  two_sylow : IsSylowIn 2 T H
  component : L ∈ cComponentsIn H
  component_normal : (L.subgroupOf H).Normal
  component_quasisimple : Theory.GroupTheory.IsQuasisimple (XiQuotient L)
  component_invariant : T ≤ normalizer L
  complement_le_component : P ≤ L
  component_commutator : ⁅L, P⁆ = L


/-- The source's literal permutability follows from the two factorizations. -/
theorem complement_mul_two_group {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) :
    (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) := by
  let C := X.pCoreIn 2
  let S := T ⊓ normalizer P
  have hPC : P ≤ normalizer C :=
    (le_sup_right.trans_eq h.complement).trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  have hSC : S ≤ normalizer C := inf_le_left.trans (h.invariant.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  have hT : (T : Set G) = (C : Set G) * (S : Set G) := by
    rw [h.normalizer_factor]
    exact coe_mul_of_right_le_normalizer_left C S hSC
  rw [hT, ← mul_assoc, set_mul_normalizer_comm (P : Set G) C hPC, mul_assoc,
    ← set_mul_normalizer_comm (S : Set G) P inf_le_right, ← mul_assoc]

/-- Sylow restriction to the component and its acting two-group. -/
theorem component_join_sylow_of_sylow {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hT : IsSylowIn 2 T H) (hLH : L ≤ H) :
    IsSylowIn 2 T (L ⊔ T) :=
  hT.restrict le_sup_right (sup_le hLH (le_sup_right.trans h.overgroup))

/-- Relative normality, rather than ambient normality, gives the component Sylow subgroup. -/
theorem exists_component_sylow_of_sylow [Finite G] {T H L : Subgroup G}
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hn : (L.subgroupOf H).Normal) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = T.subgroupOf L := by
  obtain ⟨S, hS⟩ := Section02.IndexTwo.isSylowIn_inf_of_subnormal hT hLH hn.isSubnormal
  refine ⟨S, map_injective L.subtype_injective ?_⟩
  rw [hS, subgroupOf_map_subtype]

/-- The image of T intersect L is Sylow in L/O₂(L). -/
theorem exists_component_quotient_sylow_of_sylow [Finite G] {T H L : Subgroup G}
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hn : (L.subgroupOf H).Normal) :
    ∃ S : Sylow 2 (XiQuotient L), (S : Subgroup (XiQuotient L)) =
      (T.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) := by
  obtain ⟨S, hS⟩ := exists_component_sylow_of_sylow hT hLH hn
  exact ⟨S.mapSurjective (QuotientGroup.mk'_surjective _), congrArg (map _) hS⟩

/-- A second quotient gives the genuine Sylow subgroup in the simple central quotient. -/
theorem exists_component_central_quotient_sylow_of_sylow [Finite G]
    {T H L : Subgroup G}
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hn : (L.subgroupOf H).Normal) :
    ∃ S : Sylow 2 (XiQuotient L ⧸ center (XiQuotient L)),
      (S : Subgroup (XiQuotient L ⧸ center (XiQuotient L))) =
        ((T.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))).map
          (QuotientGroup.mk' (center (XiQuotient L))) := by
  obtain ⟨S, hS⟩ := exists_component_quotient_sylow_of_sylow hT hLH hn
  exact ⟨S.mapSurjective (QuotientGroup.mk'_surjective _), congrArg (map _) hS⟩

/-- Sylow maximality preserves the component intersection under any homomorphism. -/
theorem component_intersection_image_of_sylow [Finite G] {T H L : Subgroup G}
    (hT : IsSylowIn 2 T H) (_hLH : L ≤ H) (hn : (L.subgroupOf H).Normal)
    {A : Type*} [Group A] (f : H →* A) :
    ((T ⊓ L).subgroupOf H).map f =
      (T.subgroupOf H).map f ⊓ (L.subgroupOf H).map f := by
  obtain ⟨S, hS⟩ := hT
  have hTS : T.subgroupOf H = (S : Subgroup H) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (isSylowIn_iff.mp ⟨S, hS⟩).2.1, hS]
  let _ := hn
  obtain ⟨U, hU⟩ := S.exists_subgroupOf_eq_of_normal (L.subgroupOf H)
  have hUm : (U : Subgroup (L.subgroupOf H)).map (L.subgroupOf H).subtype =
      (T ⊓ L).subgroupOf H := by
    rw [hU, subgroupOf_map_subtype, ← hTS]
    rfl
  rw [hTS]
  exact S.map_image_eq_inf _ _ U hUm (by rw [← hTS]; exact comap_mono inf_le_left) f

/-- A surjective representation retains the Sylow subgroup as its literal image. -/
theorem exists_sylow_image_of_sylow [Finite G] {T H : Subgroup G}
    (hT : IsSylowIn 2 T H) {A : Type*} [Group A] (f : H →* A)
    (hf : Function.Surjective f) :
    ∃ S : Sylow 2 A, (S : Subgroup A) = (T.subgroupOf H).map f := by
  obtain ⟨S, hS⟩ := hT
  have hTS : T.subgroupOf H = (S : Subgroup H) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (isSylowIn_iff.mp ⟨S, hS⟩).2.1, hS]
  exact ⟨S.mapSurjective hf, congrArg (map f) hTS.symm⟩

/-- The actual images of the complement and two-group still permute. -/
theorem complement_image_mul_two_image {p : ℕ} {T X P H J : Subgroup G}
    (h : LocalInput p T X P H) (hPJ : P ≤ J) (hTJ : T ≤ J)
    {A : Type*} [Group A] (f : J →* A) :
    ((P.subgroupOf J).map f : Set A) * ((T.subgroupOf J).map f : Set A) =
      ((T.subgroupOf J).map f : Set A) * ((P.subgroupOf J).map f : Set A) := by
  have hi : (P.subgroupOf J : Set J) * (T.subgroupOf J : Set J) =
      (T.subgroupOf J : Set J) * (P.subgroupOf J : Set J) := by
    apply Set.image_injective.mpr J.subtype_injective
    simpa only [Set.image_mul, ← Subgroup.coe_map,
      map_subgroupOf_eq_of_le hPJ, map_subgroupOf_eq_of_le hTJ]
      using complement_mul_two_group h
  simpa only [Set.image_mul, ← Subgroup.coe_map] using congrArg (Set.image f) hi

/-- For p greater than three, O³(P) is all of P, as required in A.3.15. -/
theorem complement_three_residual_eq_top [Finite G] {p : ℕ} {T X P H : Subgroup G}
    (h : LocalInput p T X P H) (hp : 3 < p) : pResidual 3 P = ⊤ := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  apply (pResidual_eq_top_iff 3 P).mpr
  intro N hN hQ
  let _ := hN
  have hc : Nat.Coprime p 3 := (Nat.coprime_primes h.prime (by decide)).mpr (by omega)
  have hd := (h.odd_complement.isPGroup.to_quotient N).to_subgroup ⊤ |>.disjoint_of_coprime
    (hQ.to_subgroup ⊤) hc
  apply top_unique
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (hd.le_bot ⟨mem_top _, mem_top _⟩)

private theorem mul_restrict_forward {P T L : Subgroup G}
    (hPL : P ≤ L) (hm : (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G)) :
    (P.subgroupOf L : Set L) * (T.subgroupOf L : Set L) ⊆
      (T.subgroupOf L : Set L) * (P.subgroupOf L : Set L) := by
  rintro x ⟨a, ha, b, hb, rfl⟩
  have hx : (a : G) * (b : G) ∈ (T : Set G) * (P : Set G) :=
    hm ▸ Set.mul_mem_mul ha hb
  obtain ⟨t, ht, p, hp, he⟩ := hx
  change t * p = (a : G) * (b : G) at he
  have htL : t ∈ L := by
    have hh : t * p ∈ L := by rw [he]; exact L.mul_mem a.property b.property
    simpa only [mul_inv_cancel_right] using L.mul_mem hh (L.inv_mem (hPL hp))
  exact ⟨⟨t, htL⟩, ht, ⟨p, hPL hp⟩, hp, Subtype.ext he⟩

/-- Permutability restricts to the component, even though T need not lie in it. -/
theorem complement_mul_component_intersection {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L) :
    (P.subgroupOf L : Set L) * (T.subgroupOf L : Set L) =
      (T.subgroupOf L : Set L) * (P.subgroupOf L : Set L) := by
  apply Set.Subset.antisymm (mul_restrict_forward hPL (complement_mul_two_group h))
  rintro x ⟨a, ha, b, hb, rfl⟩
  have hx : (a : G) * (b : G) ∈ (P : Set G) * (T : Set G) :=
    (complement_mul_two_group h).symm ▸ Set.mul_mem_mul ha hb
  obtain ⟨p, hp, t, ht, he⟩ := hx
  change p * t = (a : G) * (b : G) at he
  have htL : t ∈ L := by
    have hh : p * t ∈ L := by rw [he]; exact L.mul_mem a.property b.property
    simpa only [inv_mul_cancel_left] using L.mul_mem (L.inv_mem (hPL hp)) hh
  exact ⟨⟨p, hPL hp⟩, hp, ⟨t, htL⟩, ht, Subtype.ext he⟩
/-- The complement and the component Sylow intersection still permute in every image. -/
theorem complement_image_mul_component_intersection {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L)
    {A : Type*} [Group A] (f : L →* A) :
    ((P.subgroupOf L).map f : Set A) * ((T.subgroupOf L).map f : Set A) =
      ((T.subgroupOf L).map f : Set A) * ((P.subgroupOf L).map f : Set A) := by
  simpa only [Set.image_mul, ← Subgroup.coe_map] using
    congrArg (Set.image f) (complement_mul_component_intersection h hPL)

/-- Both the literal Sylow image and the product condition needed in A.3.15
survive passage to any quotient of the relatively normal component. -/
theorem exists_component_sylow_image_permuting_of_sylow [Finite G]
    {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hT : IsSylowIn 2 T H)
    (hLH : L ≤ H) (hn : (L.subgroupOf H).Normal) (hPL : P ≤ L)
    {A : Type*} [Group A] (f : L →* A) (hf : Function.Surjective f) :
    ∃ S : Sylow 2 A, (S : Subgroup A) = (T.subgroupOf L).map f ∧
      ((P.subgroupOf L).map f : Set A) * (S : Set A) =
        (S : Set A) * ((P.subgroupOf L).map f : Set A) := by
  obtain ⟨S, hS⟩ := exists_component_sylow_of_sylow hT hLH hn
  refine ⟨S.mapSurjective hf, congrArg (map f) hS, ?_⟩
  change ((P.subgroupOf L).map f : Set A) * ((S : Subgroup L).map f : Set A) =
    ((S : Subgroup L).map f : Set A) * ((P.subgroupOf L).map f : Set A)
  rw [hS]
  exact complement_image_mul_component_intersection h hPL f

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge

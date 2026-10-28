module

public import Theory.GroupTheory.ChiefFactorDirectPower
public import CFSG.Quasithin.ChapterE.Section01.MinimalSupplement

/-!
# Chief-factor structure for minimal supplements

E.1.10(1) identifies `X/Y` with the image of `K ∩ X` in `G/Y`. When `X/Y` is
a chief factor of the finite group `G`, the chief-factor structure theorem
constructs a positive direct-power isomorphism for `X/Y`, which transports to
that image. Projecting onto a coordinate also records a genuine simple normal
section of a subnormal subgroup of `G`. This establishes E.1.10(5).

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.10(1),(5), p.211.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE

universe u v
variable {G : Type u} [Group G] {S : Type v} [Group S]

/-- Transport an actual direct-power isomorphism through E.1.10(1). -/
noncomputable def IsMinimalSupplement.directPowerImageEquiv
    {T X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement T X Y K) (hYX : Y ≤ X) {n : ℕ}
    (e : X ⧸ Y.subgroupOf X ≃* (Fin n → S)) :
    (K ⊓ X).map (QuotientGroup.mk' Y) ≃* (Fin n → S) :=
  (h.quotientImageEquiv hYX).symm.trans e

/-- A supplied positive simple direct-power decomposition yields both the image
isomorphism and an explicit composition-factor witness. This is conditional
transport, not the assertion that every chief factor admits the decomposition. -/
theorem IsMinimalSupplement.directPower_and_simpleSection_of_quotient_equiv
    [IsSimpleGroup S] {T X Y K : Subgroup G} [X.Normal] [Y.Normal]
    (h : IsMinimalSupplement T X Y K) (hYX : Y ≤ X) {n : ℕ} (hn : 0 < n)
    (e : X ⧸ Y.subgroupOf X ≃* (Fin n → S)) :
    Nonempty ((K ⊓ X).map (QuotientGroup.mk' Y) ≃* (Fin n → S)) ∧
      Nonempty (ChiefFactor.SimpleSection G S) :=
  ⟨⟨h.directPowerImageEquiv hYX e⟩,
    ⟨ChiefFactor.simpleSectionOfPower X Y
      (Subgroup.Normal.isSubnormal inferInstance) hn e⟩⟩

/-- E.1.10(5): the image of `K ∩ X` is a positive direct power of a composition
factor of `G` whenever `X/Y` is an ambient chief factor. Both the multiplicative
equivalence and an explicit simple normal section are retained. Finiteness of
the simple carrier `S` is inherited from the quotient of `G`. -/
theorem IsMinimalSupplement.exists_directPower_and_simpleSection_of_isChief
    [Finite G] {T X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement T X Y K) (hchief : ChiefFactor.IsChief X Y) :
    ∃ S : Subgroup (X.map (QuotientGroup.mk' Y)), IsSimpleGroup S ∧
      ∃ n : ℕ, 0 < n ∧
        Nonempty ((K ⊓ X).map (QuotientGroup.mk' Y) ≃* (Fin n → S)) ∧
        Nonempty (ChiefFactor.SimpleSection G S) := by
  obtain ⟨S, hS, n, hn, ⟨e⟩, hsection⟩ :=
    hchief.exists_directPower_and_simpleSection X Y
  exact ⟨S, hS, n, hn, ⟨h.directPowerImageEquiv hchief.lt.le e⟩, hsection⟩

end CFSG.Quasithin.ChapterE

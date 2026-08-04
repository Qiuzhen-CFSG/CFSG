module

public import BenderSuzuki.FinalTheorem
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# 𝒦-groups

This module formalises the notion of a **𝒦-group** (`K-group`) from the
Gorenstein–Lyons–Solomon series *The Classification of the Finite Simple Groups*:

* the definition of a *section* of a group and of the class 𝒦 of *known simple
  groups* (Vol. 1, "Almost Simple 𝒦-Groups");
* the definition of a 𝒦-group and of a 𝒦-proper simple group, and their basic
  closure properties, as used throughout Vol. 4, Chapter 4 ("Properties of
  𝒦-Groups", pp. 237–331).

Following GLS, a group `G` is a **𝒦-group** if every nonabelian simple section of
`G` is isomorphic to a *known* simple group — one on the classification list.  The
class 𝒦 is the union of the three families `Qhev ∪ Alt ∪ Spor` (groups of Lie type,
alternating, sporadic); each family is an inductive predicate whose clauses are added
as the structure theory of its members is formalized.  The Lie-type family currently
contains the simple Bender groups `L₂(2ⁿ)`, `Sz(2^(2n+1))`, `U₃(2ⁿ)` (see
`BenderSuzuki.FinalTheorem`).

The genuinely classification-dependent properties of Chapter 4 (Schreier's
property for automorphism groups, Schur multipliers, Sylow structure of specific
groups, …) are not stated here: each depends on the detailed structure of the
families in 𝒦 and will be added as those families are developed.
-/

noncomputable section

namespace GroupTheory

universe u

/-! ## The class of known simple groups -/

/-- The class `Qhev` of simple groups of Lie type (Chevalley groups).  Clauses are
added as the Lie-type families are formalized; currently the simple Bender groups
`L₂(2ⁿ)`, `Sz(2^(2n+1))`, `U₃(2ⁿ)` (see `BenderSuzuki.FinalTheorem`). -/
public inductive IsChevGroup (S : Type u) [Group S] [Finite S] : Prop where
  | isBenderGroup (e : BenderSuzuki.IsSimpleBenderGroup S) : IsChevGroup S

/-- The class `Alt` of alternating groups. -/
public inductive IsAltGroup (S : Type u) [Group S] : Prop where
  | isAlternating (n : ℕ) (_ : 5 ≤ n) (e : S ≃* alternatingGroup (Fin n)) : IsAltGroup S

/-- The class `Spor` of the sporadic simple groups.  Clauses are added as the
sporadic groups are formalized. -/
public inductive IsSporGroup (S : Type u) [Group S] : Prop where

/-- The class 𝒦 of **known simple groups**: `Qhev ∪ Alt ∪ Spor` (GLS Vol. 1). -/
public def IsKnownSimpleGroup (S : Type u) [Group S] [Finite S] : Prop :=
  IsChevGroup S ∨ IsAltGroup S ∨ IsSporGroup S

/-! ## Sections -/

/-- `S` is a **section of the subgroup `H` of `G`**: `S` is isomorphic to a quotient
`A/C` of a subgroup `C ⊴ A ≤ H`.  (GLS Vol. 1: a section of `G` is a quotient of a
subgroup of `G`.) -/
public def IsSectionOfSubgroup (S : Type u) [Group S] {G : Type u} [Group G]
    (H : Subgroup G) : Prop :=
  ∃ (A C : Subgroup G) (_hAH : A ≤ H) (_hCA : C ≤ A)
      (_hN : (C.subgroupOf A).Normal),
    letI : (C.subgroupOf A).Normal := _hN
    Nonempty (S ≃* ↥A ⧸ C.subgroupOf A)

/-- `S` is a **section of `G`**: `S` is isomorphic to a quotient of a subgroup of `G`. -/
public def IsSectionOf (S : Type u) [Group S] (G : Type u) [Group G] : Prop :=
  IsSectionOfSubgroup S (⊤ : Subgroup G)

/-- `S` is **nonabelian simple**: simple and not solvable.  For simple groups this is
equivalent to "simple and not commutative": a solvable simple group is abelian
(`IsSolvable.commutator_lt_top_of_nontrivial`). -/
public def IsNonabelianSimpleGroup (S : Type u) [Group S] : Prop :=
  IsSimpleGroup S ∧ ¬ IsSolvable S

/-! ## 𝒦-groups -/

/-- `G` is a **𝒦-group**: every nonabelian simple section of `G` is a known simple
group.  (GLS Vol. 1, Definition 1.1; used throughout Vol. 4, Chapter 4.) -/
public def IsKGroup (G : Type u) [Group G] : Prop :=
  ∀ (S : Type u) [Group S] [Finite S], IsSectionOf S G →
    IsNonabelianSimpleGroup S → IsKnownSimpleGroup S

/-- `G` is **𝒦-proper**: every proper subgroup of `G` is a 𝒦-group. -/
public def IsKProper (G : Type u) [Group G] : Prop :=
  ∀ H : Subgroup G, H < ⊤ → IsKGroup H

/-- `G` is **𝒦-proper simple**: simple and 𝒦-proper.  (GLS Vol. 1: the minimal
counterexamples to the Classification Theorem are 𝒦-proper simple.) -/
public def IsKProperSimple (G : Type u) [Group G] : Prop :=
  IsSimpleGroup G ∧ IsKProper G

/-! ### The surjective encoding of sections -/

/-- `S` is a **quotient of the subgroup `H` of `G`**: there is a surjective
homomorphism onto `S` from a subgroup of `G` contained in `H`.  Equivalent to
`IsSectionOfSubgroup` by the first isomorphism theorem. -/
private def IsQuotientOfSubgroup (S : Type u) [Group S] {G : Type u} [Group G]
    (H : Subgroup G) : Prop :=
  ∃ (A : Subgroup G) (_hAH : A ≤ H) (f : ↥A →* S), Function.Surjective f

private def IsQuotientOf (S : Type u) [Group S] (G : Type u) [Group G] : Prop :=
  IsQuotientOfSubgroup S (⊤ : Subgroup G)

/-- The surjectivity and injectivity of a `MulEquiv` viewed as a monoid homomorphism. -/
private theorem injective_of_mulEquiv {M N : Type u} [MulOneClass M] [MulOneClass N]
    (e : M ≃* N) : Function.Injective (e.toMonoidHom) := by
  simpa using (Equiv.injective e.toEquiv)

private theorem surjective_of_mulEquiv {M N : Type u} [MulOneClass M] [MulOneClass N]
    (e : M ≃* N) : Function.Surjective (e.toMonoidHom) := by
  simpa using (Equiv.surjective e.toEquiv)

private theorem bijective_of_mulEquiv {M N : Type u} [MulOneClass M] [MulOneClass N]
    (e : M ≃* N) : Function.Bijective (e.toMonoidHom) := by
  exact ⟨injective_of_mulEquiv e, surjective_of_mulEquiv e⟩

private theorem isSectionOfSubgroup_iff_isQuotientOfSubgroup (S : Type u) [Group S]
    {G : Type u} [Group G] (H : Subgroup G) :
    IsSectionOfSubgroup S H ↔ IsQuotientOfSubgroup S H := by
  constructor
  · rintro ⟨A, C, hAH, _hCA, hN, ⟨e⟩⟩
    letI : (C.subgroupOf A).Normal := hN
    exact ⟨A, hAH, (e.symm.toMonoidHom).comp (QuotientGroup.mk' (C.subgroupOf A)),
      (surjective_of_mulEquiv e.symm).comp (QuotientGroup.mk'_surjective (C.subgroupOf A))⟩
  · rintro ⟨A, hAH, f, hf⟩
    let C : Subgroup G := f.ker.map A.subtype
    have hCA : C ≤ A := by
      intro x hx
      rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, hxy⟩
      exact hxy ▸ y.2
    have hCker : C.subgroupOf A = f.ker := by
      ext x
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        rcases (Subgroup.mem_map).1 hx with ⟨y, hy, hxy⟩
        have hyx : y = x := by
          apply Subtype.ext
          exact hxy
        rw [← hyx]
        exact hy
      · intro hx
        rw [Subgroup.mem_map]
        exact ⟨x, hx, rfl⟩
    have hN : (C.subgroupOf A).Normal := by
      simpa [hCker] using (inferInstance : f.ker.Normal)
    letI : (C.subgroupOf A).Normal := hN
    refine ⟨A, C, hAH, hCA, hN, ?_⟩
    refine ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hCker.symm)⟩

private theorem isSectionOf_iff_isQuotientOf (S : Type u) [Group S]
    (G : Type u) [Group G] : IsSectionOf S G ↔ IsQuotientOf S G :=
  isSectionOfSubgroup_iff_isQuotientOfSubgroup S (⊤ : Subgroup G)

/-! ### Transfers between groups and their subgroups -/

/-- Sections of a subgroup of a group are sections of the group: transfer along the
inclusion. -/
private theorem isQuotientOfSubgroup_of_isQuotientOf {S : Type u} [Group S]
    {G : Type u} [Group G] {H : Subgroup G} :
    IsQuotientOf S H → IsQuotientOfSubgroup S H := by
  rintro ⟨A, hAH, f, hf⟩
  refine ⟨A.map H.subtype, ?_, f.comp (Subgroup.equivMapOfInjective A H.subtype
    (Subgroup.subtype_injective H)).symm.toMonoidHom, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, hxy⟩
    exact hxy ▸ y.2
  · exact hf.comp (Subgroup.equivMapOfInjective A H.subtype
      (Subgroup.subtype_injective H)).symm.surjective

/-- Sections of a subgroup, expressed with ambient subgroups of `G`, are sections of
the subgroup as a group: transfer along `subgroupOfEquivOfLe`. -/
private theorem isQuotientOf_of_isQuotientOfSubgroup {S : Type u} [Group S]
    {G : Type u} [Group G] {H : Subgroup G} :
    IsQuotientOfSubgroup S H → IsQuotientOf S H := by
  rintro ⟨A, hAH, f, hf⟩
  refine ⟨A.subgroupOf H, le_top, f.comp (Subgroup.subgroupOfEquivOfLe hAH).toMonoidHom, ?_⟩
  exact hf.comp (Subgroup.subgroupOfEquivOfLe hAH).surjective

/-- Sections of a quotient of `G` are sections of `G`: transfer along the quotient
map. -/
private theorem isQuotientOf_of_quotient {S : Type u} [Group S]
    {G : Type u} [Group G] {N : Subgroup G} (hN : N.Normal) :
    IsQuotientOf S (G ⧸ N) → IsQuotientOf S G := by
  rintro ⟨A, _hAH, f, hf⟩
  let A' : Subgroup G := A.comap (QuotientGroup.mk' N)
  let φ : ↥A' →* ↥A :=
    ((QuotientGroup.mk' N).comp A'.subtype).codRestrict A
      (fun x => (Subgroup.mem_comap).1 x.2)
  have hφsurj : Function.Surjective φ := by
    intro a
    rcases (QuotientGroup.mk'_surjective N) a with ⟨x, hx⟩
    refine ⟨⟨x, (Subgroup.mem_comap).2 (hx.symm ▸ a.2)⟩, ?_⟩
    apply Subtype.ext
    exact hx
  exact ⟨A', le_top, f.comp φ, hf.comp hφsurj⟩

/-- Sections of a smaller subgroup are sections of a larger one. -/
private theorem isQuotientOfSubgroup_mono {S : Type u} [Group S] {G : Type u} [Group G]
    {H K : Subgroup G} (hHK : H ≤ K) : IsQuotientOfSubgroup S H → IsQuotientOfSubgroup S K := by
  rintro ⟨A, hAH, f, hf⟩
  exact ⟨A, hAH.trans hHK, f, hf⟩

/-- `(A ⊓ N)`, viewed as a subgroup of `A`, is just `N` restricted to `A`. -/
private theorem subgroupOf_inf_comm {G : Type u} [Group G] {A N : Subgroup G} :
    (A ⊓ N).subgroupOf A = N.subgroupOf A := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    exact (Subgroup.mem_inf.mp hx).2
  · intro hx
    exact (Subgroup.mem_inf.mpr ⟨x.2, hx⟩)

/-- Sections of sections are sections: transitivity of the section relation. -/
private theorem isQuotientOf_trans {T S G : Type u} [Group T] [Group S] [Group G]
    (hTS : IsQuotientOf T S) (hSG : IsQuotientOf S G) : IsQuotientOf T G := by
  rcases hTS with ⟨B, _hB, g, hg⟩
  rcases hSG with ⟨A, _hA, f, hf⟩
  let B' : Subgroup ↥A := B.comap f
  let ψ : ↥B' →* ↥B :=
    (f.comp B'.subtype).codRestrict B (fun x => (Subgroup.mem_comap).1 x.2)
  have hψsurj : Function.Surjective ψ := by
    intro b
    rcases hf b with ⟨x, hx⟩
    refine ⟨⟨x, (Subgroup.mem_comap).2 (hx.symm ▸ b.2)⟩, ?_⟩
    apply Subtype.ext
    exact hx
  refine ⟨B'.map A.subtype, le_top,
    (g.comp ψ).comp (Subgroup.equivMapOfInjective B' A.subtype
      (Subgroup.subtype_injective A)).symm.toMonoidHom, ?_⟩
  exact hg.comp (hψsurj.comp (Subgroup.equivMapOfInjective B' A.subtype
    (Subgroup.subtype_injective A)).symm.surjective)

/-- Quotients are transported along a bijective homomorphism. -/
private def quotientEquiv_of_bijective {G H : Type u} [Group G] [Group H]
    (f : G →* H) (hf : Function.Bijective f) (K : Subgroup G)
    [K.Normal] (hK : (K.map f).Normal) :
    G ⧸ K ≃* H ⧸ K.map f := by
  letI : (K.map f).Normal := hK
  have hsurj : Function.Surjective ((QuotientGroup.mk' (K.map f)).comp f) :=
    (QuotientGroup.mk'_surjective (K.map f)).comp hf.2
  have hker : ((QuotientGroup.mk' (K.map f)).comp f).ker = K := by
    apply le_antisymm
    · intro x hx
      have hx' : (QuotientGroup.mk' (K.map f)) (f x) = 1 := by
        simpa [MonoidHom.mem_ker] using hx
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
      rw [Subgroup.mem_map] at hx'
      rcases hx' with ⟨y, hy, hy'⟩
      rw [hf.1 hy'.symm]
      exact hy
    · intro x hx
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk' (K.map f)) (f x) = 1
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_map]
      exact ⟨x, hx, rfl⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' (K.map f)).comp f) hsurj)

/-- For a bijective homomorphism, the image of a subgroup is everything exactly when
the subgroup is everything. -/
private theorem map_eq_top_iff_of_bijective {G N : Type u} [Group G] [Group N]
    (f : G →* N) (hf : Function.Bijective f) {H : Subgroup G} :
    H.map f = ⊤ ↔ H = ⊤ := by
  constructor
  · intro h
    have h' : H ⊔ f.ker = ⊤ := by
      calc
        H ⊔ f.ker = Subgroup.comap f (Subgroup.map f H) := (Subgroup.comap_map_eq f H).symm
        _ = Subgroup.comap f ⊤ := by rw [h]
        _ = ⊤ := Subgroup.comap_top f
    rw [MonoidHom.ker_eq_bot f hf.1, sup_bot_eq] at h'
    exact h'
  · intro h
    rw [h]
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, _hx, rfl⟩
      exact Subgroup.mem_top (f x)
    · intro _hy
      refine ⟨Classical.choose (hf.2 y), Subgroup.mem_top (Classical.choose (hf.2 y)), ?_⟩
      exact Classical.choose_spec (hf.2 y)

/-! ### Basic properties of sections -/

/-- A group is a section of itself. -/
public theorem section_of_self (G : Type u) [Group G] : IsSectionOf G G := by
  rw [isSectionOf_iff_isQuotientOf]
  refine ⟨⊤, le_top, Subgroup.topEquiv.toMonoidHom, ?_⟩
  intro y
  refine ⟨Subgroup.topEquiv.symm y, ?_⟩
  exact Subgroup.topEquiv.apply_symm_apply y

/-- Every subgroup of a group is a section of it. -/
public theorem section_of_subgroup {G : Type u} [Group G] (H : Subgroup G) :
    IsSectionOf H G := by
  rw [isSectionOf_iff_isQuotientOf]
  exact ⟨H, le_top, MonoidHom.id H, Function.surjective_id⟩

/-- Every quotient of a group by a normal subgroup is a section of it. -/
public theorem section_of_quotient {G : Type u} [Group G] {N : Subgroup G} (hN : N.Normal) :
    IsSectionOf (G ⧸ N) G := by
  rw [isSectionOf_iff_isQuotientOf]
  refine ⟨⊤, le_top, (QuotientGroup.mk' N).comp Subgroup.topEquiv.toMonoidHom, ?_⟩
  intro y
  rcases (QuotientGroup.mk'_surjective N) y with ⟨g, hg⟩
  refine ⟨Subgroup.topEquiv.symm g, ?_⟩
  simpa using (congrArg (QuotientGroup.mk' N)
    (Subgroup.topEquiv.apply_symm_apply g)).trans hg

/-- Sections of sections are sections. -/
public theorem section_of_section {T S G : Type u} [Group T] [Group S] [Group G]
    (hTS : IsSectionOf T S) (hSG : IsSectionOf S G) : IsSectionOf T G := by
  rw [isSectionOf_iff_isQuotientOf] at hTS hSG ⊢
  exact isQuotientOf_trans hTS hSG

/-- Sections of solvable groups are solvable. -/
public theorem isSolvable_of_section {S G : Type u} [Group S] [Group G]
    (hSec : IsSectionOf S G) (hG : IsSolvable G) : IsSolvable S := by
  rcases hSec with ⟨A, C, _hAH, _hCA, hN, ⟨e⟩⟩
  letI : (C.subgroupOf A).Normal := hN
  haveI : IsSolvable ↥A := subgroup_solvable_of_solvable A
  haveI : IsSolvable (↥A ⧸ C.subgroupOf A) := solvable_quotient_of_solvable (C.subgroupOf A)
  exact solvable_of_surjective (f := e.symm.toMonoidHom) (surjective_of_mulEquiv e.symm)

/-! ### Closure properties of 𝒦-groups -/

/-- Subgroups of 𝒦-groups are 𝒦-groups. -/
public theorem isKGroup_of_subgroup {G : Type u} [Group G] (H : Subgroup G) :
    IsKGroup G → IsKGroup H := by
  intro hG S _ _ hSec hSnonab
  have hSecG : IsSectionOf S G := by
    rw [isSectionOf_iff_isQuotientOf] at hSec ⊢
    exact isQuotientOfSubgroup_mono (le_top : H ≤ ⊤)
      (isQuotientOfSubgroup_of_isQuotientOf (S := S) (H := H) hSec)
  exact hG S hSecG hSnonab

/-- Quotients of 𝒦-groups by normal subgroups are 𝒦-groups. -/
public theorem isKGroup_of_quotient {G : Type u} [Group G] {N : Subgroup G} (hN : N.Normal) :
    IsKGroup G → IsKGroup (G ⧸ N) := by
  intro hG S _ _ hSec hSnonab
  have hSecG : IsSectionOf S G := by
    rw [isSectionOf_iff_isQuotientOf] at hSec ⊢
    exact isQuotientOf_of_quotient (S := S) (N := N) hN hSec
  exact hG S hSecG hSnonab

/-- 𝒦-groups are closed under extensions: if `N ⊴ G` and both `N` and `G/N` are
𝒦-groups, then so is `G`. -/
public theorem isKGroup_of_extension {G : Type u} [Group G] {N : Subgroup G} (hN : N.Normal)
    (hNkg : IsKGroup N) (hQkg : IsKGroup (G ⧸ N)) : IsKGroup G := by
  haveI : N.Normal := hN
  intro S _ _ hSec hSnonab
  rcases hSec with ⟨A, C, _hAH, hCA, hN', ⟨e⟩⟩
  letI : (C.subgroupOf A).Normal := hN'
  let q : ↥A →* ↥A ⧸ C.subgroupOf A := QuotientGroup.mk' (C.subgroupOf A)
  -- The image of `(A ∩ N)C/C` in the simple group `S ≅ A/C` is normal, hence either
  -- everything or trivial.
  let J : Subgroup ↥A := (A ⊓ N).subgroupOf A ⊔ C.subgroupOf A
  have hJNormal : J.Normal := by
    haveI : ((A ⊓ N).subgroupOf A).Normal := by
      simpa [subgroupOf_inf_comm] using (Subgroup.Normal.subgroupOf hN A)
    exact Subgroup.sup_normal ((A ⊓ N).subgroupOf A) (C.subgroupOf A)
  have hJImageNormal : ((J.map q).map e.symm.toMonoidHom).Normal := by
    exact Subgroup.Normal.map (Subgroup.Normal.map hJNormal q
      (QuotientGroup.mk'_surjective (C.subgroupOf A))) e.symm.toMonoidHom
        (surjective_of_mulEquiv e.symm)
  haveI : IsSimpleGroup S := hSnonab.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((J.map q).map e.symm.toMonoidHom)
    hJImageNormal with hImBot | hImTop
  · -- The image of `A ∩ N` in `S` is trivial: then `A ∩ N ≤ C` and `S` is a section of
    -- `G/N`.
    have hJbot : J.map q = ⊥ := by
      exact (Subgroup.map_eq_bot_iff_of_injective (H := J.map q) (injective_of_mulEquiv e.symm)).mp hImBot
    have hJleC : J ≤ C.subgroupOf A := by
      simpa [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff (H := J) (f := q)).mp hJbot
    have hACN : A ⊓ N ≤ C := by
      intro x hx
      let a : ↥A := ⟨x, hx.1⟩
      have hx' : a ∈ (A ⊓ N).subgroupOf A := (Subgroup.mem_subgroupOf).2 hx
      have hx'' : a ∈ C.subgroupOf A := hJleC ((le_sup_left : (A ⊓ N).subgroupOf A ≤ J) hx')
      exact (Subgroup.mem_subgroupOf).1 hx''
    -- `S ≅ A/C` is a quotient of a quotient of `A`, and `A/(A ∩ N) ≅ (A ⊔ N)/N ≤ G/N`.
    let N₁ : Subgroup ↥A := (A ⊓ N).subgroupOf A
    let M₁ : Subgroup ↥A := C.subgroupOf A
    have hN₁ : ((A ⊓ N).subgroupOf A).Normal := by
      simpa [subgroupOf_inf_comm] using (Subgroup.Normal.subgroupOf hN A)
    have hM₁ : (C.subgroupOf A).Normal := hN'
    have h₁ : N₁ ≤ M₁ := by
      intro x hx
      exact (Subgroup.mem_subgroupOf).2 (hACN ((Subgroup.mem_subgroupOf).1 hx))
    haveI : N₁.Normal := hN₁
    haveI : M₁.Normal := hM₁
    have hQuot : (↥A ⧸ N₁) ⧸ M₁.map (QuotientGroup.mk' N₁) ≃* ↥A ⧸ C.subgroupOf A := by
      simpa [N₁, M₁] using (QuotientGroup.quotientQuotientEquivQuotient N₁ M₁ h₁)
    -- `A/(A ∩ N) ≅ (A ⊔ N)/N`.
    haveI : (N.subgroupOf A).Normal := Subgroup.Normal.subgroupOf hN A
    haveI : (N.subgroupOf (A ⊔ N)).Normal := Subgroup.Normal.subgroupOf hN (A ⊔ N)
    have hN₁' : N₁ = N.subgroupOf A := subgroupOf_inf_comm (A := A) (N := N)
    have hQuotA : ↥A ⧸ N₁ ≃* ↥(A ⊔ N) ⧸ N.subgroupOf (A ⊔ N) := by
      exact (QuotientGroup.quotientMulEquivOfEq hN₁').trans
        (QuotientGroup.quotientInfEquivProdNormalQuotient A N)
    -- `(A ⊔ N)/N ≅ (A ⊔ N).map (mk' N)`, a subgroup of `G/N`.
    let P : Subgroup (G ⧸ N) := (A ⊔ N).map (QuotientGroup.mk' N)
    let φ : ↥(A ⊔ N) →* ↥P :=
      ((QuotientGroup.mk' N).comp (A ⊔ N).subtype).codRestrict P
        (fun x => (Subgroup.mem_map).2 ⟨x.1, x.2, rfl⟩)
    have hφsurj : Function.Surjective φ := by
      intro p
      rcases (Subgroup.mem_map).1 p.2 with ⟨x, hx, hp⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hp
    have hφker : φ.ker = N.subgroupOf (A ⊔ N) := by
      ext x
      constructor
      · intro hx
        have hx' : (QuotientGroup.mk' N) x.1 = 1 := by
          change φ x = 1 at hx
          exact congrArg Subtype.val hx
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
        exact (Subgroup.mem_subgroupOf).2 hx'
      · intro hx
        change φ x = 1
        apply Subtype.ext
        change (QuotientGroup.mk' N) x.1 = 1
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact (Subgroup.mem_subgroupOf).1 hx
    have hQuotP : ↥(A ⊔ N) ⧸ N.subgroupOf (A ⊔ N) ≃* ↥P := by
      exact (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
    have hQuotAP : ↥A ⧸ N₁ ≃* ↥P := hQuotA.trans hQuotP
    -- Transport the quotient structure to `P`.
    haveI : ((M₁.map (QuotientGroup.mk' N₁)).map hQuotAP.toMonoidHom).Normal :=
      Subgroup.Normal.map (Subgroup.Normal.map hM₁ (QuotientGroup.mk' N₁)
        (QuotientGroup.mk'_surjective N₁)) hQuotAP.toMonoidHom (surjective_of_mulEquiv hQuotAP)
    have hQuotP' : (↥A ⧸ N₁) ⧸ M₁.map (QuotientGroup.mk' N₁) ≃* ↥P ⧸
        (M₁.map (QuotientGroup.mk' N₁)).map hQuotAP.toMonoidHom := by
      exact quotientEquiv_of_bijective hQuotAP.toMonoidHom (bijective_of_mulEquiv hQuotAP)
        (M₁.map (QuotientGroup.mk' N₁)) (inferInstance : ((M₁.map (QuotientGroup.mk' N₁)).map
          hQuotAP.toMonoidHom).Normal)
    let C' : Subgroup (G ⧸ N) :=
      ((M₁.map (QuotientGroup.mk' N₁)).map hQuotAP.toMonoidHom).map P.subtype
    have hC'leP : C' ≤ P := by
      intro x hx
      rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, hxy⟩
      exact hxy ▸ y.2
    have hC' : C'.subgroupOf P = (M₁.map (QuotientGroup.mk' N₁)).map hQuotAP.toMonoidHom := by
      dsimp [C']
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq]
      rw [MonoidHom.ker_eq_bot P.subtype (Subgroup.subtype_injective P), sup_bot_eq]
    have hC'Normal : (C'.subgroupOf P).Normal := by
      simpa [hC'] using (inferInstance : ((M₁.map (QuotientGroup.mk' N₁)).map
        hQuotAP.toMonoidHom).Normal)
    haveI : (C'.subgroupOf P).Normal := hC'Normal
    have hSecP : IsSectionOfSubgroup S P := by
      refine ⟨P, C', le_rfl, hC'leP, hC'Normal, ?_⟩
      refine ⟨((e.trans hQuot.symm).trans hQuotP').trans
        (QuotientGroup.quotientMulEquivOfEq hC'.symm)⟩
    have hSecS : IsSectionOf S (G ⧸ N) := by
      rw [isSectionOf_iff_isQuotientOf]
      exact isQuotientOfSubgroup_mono (le_top : P ≤ ⊤)
        ((isSectionOfSubgroup_iff_isQuotientOfSubgroup S P).1 hSecP)
    exact hQkg S hSecS hSnonab
  · -- The image of `A ∩ N` in `S` is everything: then `S` is a quotient of `A ∩ N`,
    -- hence a section of `N`.
    have hJtop : J.map q = ⊤ := by
      exact (map_eq_top_iff_of_bijective e.symm.toMonoidHom
        (bijective_of_mulEquiv e.symm)).mp hImTop
    have hJ : J = ⊤ := by
      apply le_antisymm le_top
      have hJ' : J ⊔ q.ker = ⊤ := by
        calc
          J ⊔ q.ker = Subgroup.comap q (Subgroup.map q J) := (Subgroup.comap_map_eq q J).symm
          _ = Subgroup.comap q ⊤ := by rw [hJtop]
          _ = ⊤ := Subgroup.comap_top q
      rw [← hJ']
      refine sup_le le_rfl ?_
      dsimp [q]
      rw [QuotientGroup.ker_mk']
      exact le_sup_right
    have hqIm : Subgroup.map q (Subgroup.subgroupOf (A ⊓ N) A) = ⊤ := by
      have hJ' : Subgroup.map q (Subgroup.subgroupOf (A ⊓ N) A) ⊔ Subgroup.map q (Subgroup.subgroupOf C A) = ⊤ := by
        simpa [J, Subgroup.map_sup] using hJtop
      have hC : Subgroup.map q (C.subgroupOf A) = ⊥ := by
        exact (Subgroup.map_eq_bot_iff (H := C.subgroupOf A) (f := q)).mpr (by
          change C.subgroupOf A ≤ (QuotientGroup.mk' (C.subgroupOf A)).ker
          rw [QuotientGroup.ker_mk'])
      rwa [hC, sup_bot_eq] at hJ'
    let g : ↥((A ⊓ N).subgroupOf A) →* S :=
      (e.symm.toMonoidHom).comp (q.comp ((A ⊓ N).subgroupOf A).subtype)
    have hgSurj : Function.Surjective g := by
      intro s
      let y := e s
      have hy : y ∈ Subgroup.map q (Subgroup.subgroupOf (A ⊓ N) A) := by
        rw [hqIm]
        exact Subgroup.mem_top y
      rcases (Subgroup.mem_map).1 hy with ⟨x, hx, hxeq⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      -- `g ⟨x, hx⟩ = s`
      change e.symm (q (((A ⊓ N).subgroupOf A).subtype ⟨x, hx⟩)) = s
      have hsub : ((A ⊓ N).subgroupOf A).subtype ⟨x, hx⟩ = x := rfl
      rw [hsub, hxeq]
      change e.symm (e s) = s
      exact MulEquiv.symm_apply_apply e s
    have hQuotN : IsQuotientOfSubgroup S N := by
      refine ⟨A ⊓ N, inf_le_right, g.comp (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : A ⊓ N ≤ A)).symm.toMonoidHom, ?_⟩
      exact hgSurj.comp (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ N ≤ A)).symm.surjective
    have hSecS : IsSectionOf S N := by
      rw [isSectionOf_iff_isQuotientOf]
      exact isQuotientOf_of_isQuotientOfSubgroup (S := S) (H := N) hQuotN
    exact hNkg S hSecS hSnonab

/-- Solvable groups are 𝒦-groups. -/
public theorem isKGroup_of_isSolvable {G : Type u} [Group G] (hG : IsSolvable G) : IsKGroup G := by
  intro S _ _ hSec hSnonab
  exact False.elim (hSnonab.2 (isSolvable_of_section hSec hG))

/-- Sections of 𝒦-groups are 𝒦-groups. -/
public theorem isKGroup_of_section {S G : Type u} [Group S] [Group G]
    (hSec : IsSectionOf S G) (hG : IsKGroup G) : IsKGroup S := by
  intro T _ _ hSecT hTnonab
  exact hG T (section_of_section hSecT hSec) hTnonab

/-! ### Minimal counterexamples -/

/-- A minimal (by order) group which is not a 𝒦-group is nonabelian simple.  This is
the standard minimal-counterexample reduction of the Classification Theorem (GLS
Vol. 1). -/
public theorem isNonabelianSimpleGroup_of_minimal_not_isKGroup {G : Type u} [Group G] [Finite G]
    (hG : ¬ IsKGroup G)
    (hmin : ∀ (S : Type u) [Group S] [Finite S], IsSectionOf S G →
      Nat.card S < Nat.card G → IsKGroup S) :
    IsNonabelianSimpleGroup G := by
  have hNotSolv : ¬ IsSolvable G := by
    intro hSolv
    exact hG (isKGroup_of_isSolvable hSolv)
  have hNontr : Nontrivial G := by
    by_contra hnot
    have hsub : Subsingleton G := (not_nontrivial_iff_subsingleton).1 hnot
    haveI := hsub
    exact hG (isKGroup_of_isSolvable (inferInstance : IsSolvable G))
  have hSimp : IsSimpleGroup G := by
    refine (isSimpleGroup_iff G).2 ⟨hNontr, ?_⟩
    intro N hNnorm
    by_cases hNbot : N = ⊥
    · exact Or.inl hNbot
    by_cases hNtop : N = ⊤
    · exact Or.inr hNtop
    exfalso
    have hSecN : IsSectionOf N G := by
      rw [isSectionOf_iff_isQuotientOf]
      exact ⟨N, le_top, MonoidHom.id N, Function.surjective_id⟩
    have hSecQ : IsSectionOf (G ⧸ N) G := section_of_quotient hNnorm
    have hcardN : Nat.card N < Nat.card G := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
      have hq : 1 < Nat.card (G ⧸ N) := by
        rw [← Subgroup.index_eq_card]
        exact Subgroup.one_lt_index_of_ne_top (by exact ne_top_of_lt (lt_of_le_of_ne le_top hNtop))
      have hcN : 0 < Nat.card N := Nat.card_pos
      nlinarith
    have hcardQ : Nat.card (G ⧸ N) < Nat.card G := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
      have hcN : 1 < Nat.card N := by
        have hNontrN : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hNbot
        haveI : Nontrivial N := hNontrN
        rcases exists_pair_ne ↥N with ⟨x, y, hxy⟩
        have hpos : 0 < Nat.card N := Nat.card_pos
        have hne : Nat.card N ≠ 1 := by
          intro h
          have hsub : Subsingleton N := (Nat.card_eq_one_iff_unique.mp h).1
          haveI := hsub
          exact hxy (Subsingleton.elim x y)
        omega
      have hq : 0 < Nat.card (G ⧸ N) := Nat.card_pos
      nlinarith
    have hKgN : IsKGroup N := hmin N hSecN hcardN
    have hKgQ : IsKGroup (G ⧸ N) := hmin (G ⧸ N) hSecQ hcardQ
    exact hG (isKGroup_of_extension hNnorm hKgN hKgQ)
  exact ⟨hSimp, hNotSolv⟩

/-- A minimal (by order) group which is not a 𝒦-group is 𝒦-proper simple. -/
public theorem isKProperSimple_of_minimal_not_isKGroup {G : Type u} [Group G] [Finite G]
    (hG : ¬ IsKGroup G)
    (hmin : ∀ (S : Type u) [Group S] [Finite S], IsSectionOf S G →
      Nat.card S < Nat.card G → IsKGroup S) :
    IsKProperSimple G := by
  refine ⟨(isNonabelianSimpleGroup_of_minimal_not_isKGroup hG hmin).1, ?_⟩
  intro H hHtop
  have hSecH : IsSectionOf H G := by
    rw [isSectionOf_iff_isQuotientOf]
    exact ⟨H, le_top, MonoidHom.id H, Function.surjective_id⟩
  have hcardH : Nat.card H < Nat.card G := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H]
    have hq : 1 < Nat.card (G ⧸ H) := by
      rw [← Subgroup.index_eq_card]
      exact Subgroup.one_lt_index_of_ne_top (ne_top_of_lt hHtop)
    have hcH : 0 < Nat.card H := Nat.card_pos
    nlinarith
  exact hmin H hSecH hcardH

/-! ## The Schreier property (Chapter 4, Lemma 1.1(a)) -/

/-- The group of **inner automorphisms** of `G`, the image of the conjugation map
`G →* Aut(G)`.  `@[expose]`: the definitional unfolding is needed to reason about
membership in `Out(G)` (e.g. in `AutAlternating.isSolvable_Out_of_isAltGroup`). -/
@[expose]
public def innerAutGroup (G : Type u) [Group G] : Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range

/-- The inner automorphisms form a normal subgroup of the automorphism group. -/
public instance innerAutGroup_normal (G : Type u) [Group G] : (innerAutGroup G).Normal where
  conj_mem := by
    intro n hn g
    rcases (by simpa [innerAutGroup, MonoidHom.range_eq_map] using hn) with ⟨x, hxn⟩
    have h : MulAut.conj (g x) = g * MulAut.conj x * g⁻¹ := by
      ext y
      rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply,
        MulAut.inv_apply, map_mul, map_inv, map_mul, MulEquiv.apply_symm_apply]
    exact (by
      simpa [innerAutGroup, MonoidHom.range_eq_map] using
        (Subgroup.mem_map).2 ⟨g x, Subgroup.mem_top (g x), by rw [h, hxn]⟩)

/-- The **outer automorphism group** `Out(G) = Aut(G)/Inn(G)`. -/
public abbrev Out (G : Type u) [Group G] : Type u := MulAut G ⧸ innerAutGroup G

/-- The kernel of the conjugation action of `G` on its normal subgroup `K` is the
centralizer of `K` in `G`. -/
public theorem conjNormal_ker {G : Type u} [Group G] {K : Subgroup G} [K.Normal] :
    (MulAut.conjNormal (H := K)).ker = Subgroup.centralizer (K : Set G) := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 : MulAut.conjNormal x ⟨k, hk⟩ = ⟨k, hk⟩ := by
      have h1' := congrArg (fun e : MulAut K => e ⟨k, hk⟩) hx
      rw [MulAut.one_apply] at h1'
      exact h1'
    have h : x * k * x⁻¹ = k := by
      exact (MulAut.conjNormal_apply x ⟨k, hk⟩).symm.trans (congrArg Subtype.val h1)
    calc
      k * x = (x * k * x⁻¹) * x := by rw [h]
      _ = x * k := by simp [mul_assoc]
  · intro hx
    ext k
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have hx' : (k : G) * x = x * (k : G) := (Subgroup.mem_centralizer_iff.mp hx) (k : G) k.2
    calc
      x * (k : G) * x⁻¹ = ((k : G) * x) * x⁻¹ := by rw [hx']
      _ = (k : G) := by simp [mul_assoc]

/-- Conjugation by an element of a subgroup, viewed as an automorphism of the
subgroup, is the restriction of conjugation in the ambient group: for `x ∈ K`,
`conjNormal x` agrees with `conj x`. -/
public theorem conjNormal_eq_conj {G : Type u} [Group G] {K : Subgroup G} [K.Normal]
    (x : K) : MulAut.conjNormal (H := K) (x : G) = MulAut.conj x := by
  ext y
  change (x : G) * (y : G) * (x : G)⁻¹ = (x : G) * (y : G) * (x : G)⁻¹
  rfl

/-- A homomorphism with trivial kernel is injective. -/
public theorem injective_of_ker_eq_bot {G N : Type u} [Group G] [Group N] (f : G →* N)
    (h : f.ker = ⊥) : Function.Injective f := by
  intro x y hxy
  have : x * y⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy]
    simp
  have hxy' : x * y⁻¹ = 1 := by
    have : x * y⁻¹ ∈ (⊥ : Subgroup G) := by simpa [h] using this
    exact (Subgroup.mem_bot).1 this
  simpa [mul_assoc] using congrArg (fun t : G => t * y) hxy'

/-- If `K ⊴ H` has trivial centralizer in `H`, then `H/K` embeds in `Out(K)`.  This
is the reduction behind the Schreier property (Chapter 4, Lemma 1.1(a)). -/
public theorem quotient_embedding_in_Out {H : Type u} [Group H] {K : Subgroup H}
    (hK : K.Normal) (hC : Subgroup.centralizer (K : Set H) = ⊥) :
    ∃ φ : H ⧸ K →* Out K, Function.Injective φ := by
  letI : K.Normal := hK
  let φ : H →* Out K :=
    (QuotientGroup.mk' (innerAutGroup K)).comp (MulAut.conjNormal : H →* MulAut K)
  have hker : φ.ker = K := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' : MulAut.conjNormal x ∈ innerAutGroup K := by
        exact (QuotientGroup.ker_mk' (N := innerAutGroup K)).symm ▸
          (MonoidHom.mem_ker).2 (by simpa [φ] using hx)
      rcases (MonoidHom.mem_range).1
        (show MulAut.conjNormal x ∈ (MulAut.conj : ↥K →* MulAut ↥K).range from by
          simpa [innerAutGroup] using hx') with ⟨k, hck⟩
      have hck' : ∀ y : ↥K, (↑(MulAut.conj k y) : H) = ↑(MulAut.conjNormal x y) := by
        intro y
        exact congrArg Subtype.val (congrArg (fun e : MulAut K => e y) hck)
      have hcentral : (k : H)⁻¹ * x ∈ Subgroup.centralizer (K : Set H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hxy' : x * y * x⁻¹ = (k : H) * y * (k : H)⁻¹ := by
          simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using (hck' ⟨y, hy⟩).symm
        have hconj : ((k : H)⁻¹ * x) * y * (((k : H)⁻¹ * x)⁻¹) = y := by
          calc
            ((k : H)⁻¹ * x) * y * (((k : H)⁻¹ * x)⁻¹)
                = (k : H)⁻¹ * (x * y * x⁻¹) * (k : H) := by simp [mul_assoc]
            _ = (k : H)⁻¹ * ((k : H) * y * (k : H)⁻¹) * (k : H) := by rw [hxy']
            _ = y := by simp [mul_assoc]
        calc
          y * ((k : H)⁻¹ * x) =
              (((k : H)⁻¹ * x) * y * (((k : H)⁻¹ * x)⁻¹)) * ((k : H)⁻¹ * x) := by
            rw [hconj]
          _ = ((k : H)⁻¹ * x) * y := by simp [mul_assoc]
      have hxK : (k : H)⁻¹ * x = 1 := by
        have : (k : H)⁻¹ * x ∈ (⊥ : Subgroup H) := by simpa [hC] using hcentral
        exact (Subgroup.mem_bot).1 this
      have hxk : x = (k : H) := by
        simpa [mul_assoc] using congrArg (fun t : H => (k : H) * t) hxK
      exact hxk ▸ k.2
    · intro hx
      have hmem : MulAut.conjNormal x ∈ innerAutGroup K := by
        have heq : MulAut.conj ⟨x, hx⟩ = MulAut.conjNormal x := by
          ext y
          change (x : H) * ↑y * (x : H)⁻¹ = x * ↑y * x⁻¹
          rfl
        have hmem' : MulAut.conjNormal x ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := by
          exact (MonoidHom.mem_range).2 ⟨⟨x, hx⟩, heq⟩
        simpa [innerAutGroup] using hmem'
      change (QuotientGroup.mk' (innerAutGroup K)) (MulAut.conjNormal x) = 1
      exact (MonoidHom.mem_ker).1
        ((QuotientGroup.ker_mk' (N := innerAutGroup K)).symm ▸ hmem)
  let ψ : H ⧸ K →* Out K := QuotientGroup.lift K φ (by rw [hker])
  have hψker : ψ.ker = ⊥ := by
    rw [QuotientGroup.ker_lift, hker]
    exact (Subgroup.map_eq_bot_iff K).mpr (by rw [QuotientGroup.ker_mk'])
  exact ⟨ψ, injective_of_ker_eq_bot ψ hψker⟩

/-- Chapter 4, Lemma 1.1(a) (the **Schreier property**).  In the setup (1A) of
Chapter 4 — `H` a 𝒦-group with `O_{p'}(H) = 1` and `K = F*(H)` nonabelian simple —
`H/K` is solvable.  The hypotheses stated here are those that (1A) supplies for this
part: `K ⊴ H` with trivial centralizer (both consequences of `K = F*(H)`), and `K` a
known simple group (a consequence of "`H` is a 𝒦-group", since `K = F*(H)` is a
section of `H`).  The proof embeds `H/K` into `Out(K)` via
`quotient_embedding_in_Out`; the solvability of `Out(K)` — the Schreier property for
known simple groups — GLS vol. 3, Theorem 7.1.1(a): `Alt ∪ Spor` has `|Out(K)| ≤ 4`
(Theorem 5.2.1 and Table 5.3, so `Out(K)` is solvable by `isSolvable_of_card_le_four`),
while for `K ∈ Qhev` the solvability is read off the structure of `Out(K)`
(2.5.12b–f, 2.5.15) — is proved per family as the structure theory of each family in
𝒦 is developed; the sporadic arm is already complete
(`isSolvable_Out_of_isSporGroup`). -/
public theorem schreier_property {H : Type u} [Group H] {K : Subgroup H} (hK : K.Normal)
    (hcentralizer : Subgroup.centralizer (K : Set H) = ⊥)
    (hOut : IsSolvable (Out K)) : IsSolvable (H ⧸ K) := by
  obtain ⟨φ, hφinj⟩ := quotient_embedding_in_Out hK hcentralizer
  have hrange : IsSolvable ↥φ.range := subgroup_solvable_of_solvable φ.range
  have hφker : φ.ker = ⊥ := MonoidHom.ker_eq_bot φ hφinj
  have hrinj : Function.Injective φ.rangeRestrict := by
    exact injective_of_ker_eq_bot φ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, hφker])
  let e : H ⧸ K ≃* ↥φ.range :=
    MulEquiv.ofBijective φ.rangeRestrict
      ⟨hrinj, MonoidHom.rangeRestrict_surjective φ⟩
  exact solvable_of_surjective (f := e.symm.toMonoidHom) (surjective_of_mulEquiv e.symm)


/-! ### The Schreier property for known simple groups (GLS vol. 3, Theorem 7.1.1(a)) -/

/-- A finite group of order at most four is solvable.  This is the mechanism behind
the alternating and sporadic arm of the Schreier property: GLS vol. 3, Theorem
7.1.1(a) proves `|Out(K)| ≤ 4` for `K ∈ Alt ∪ Spor` (via Theorem 5.2.1 — `Aut(Aₙ) = Sₙ`
for `n ≥ 5`, `n ≠ 6`, and `Aut(A₆)` contains `S₆` with index two — and Table 5.3 for
the sporadic groups), and the solvability follows from this smallness. -/
public theorem isSolvable_of_card_le_four {G : Type u} [Group G] [Finite G]
    (h : Nat.card G ≤ 4) : IsSolvable G := by
  by_cases h1 : Nat.card G = 1
  · have hsub : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    haveI := hsub
    exact isSolvable_of_subsingleton G
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hge2 : 2 ≤ Nat.card G := by omega
  by_cases htwo : ∀ x : G, x ≠ 1 → orderOf x = 2
  · -- every nonidentity element has order two, so `x² = 1` for all `x` and the group
    -- is commutative
    have hsq : ∀ x : G, x * x = 1 := by
      intro x
      by_cases hx : x = 1
      · simp [hx]
      · simpa [htwo x hx, pow_two] using (pow_orderOf_eq_one x)
    have hcomm : ∀ a b : G, a * b = b * a := by
      intro a b
      have hab : (a * b)⁻¹ = a * b := (eq_inv_of_mul_eq_one_right (hsq (a * b))).symm
      calc
        a * b = (a * b)⁻¹ := hab.symm
        _ = b⁻¹ * a⁻¹ := by rw [mul_inv_rev]
        _ = b * a := by
          rw [← eq_inv_of_mul_eq_one_right (hsq a), ← eq_inv_of_mul_eq_one_right (hsq b)]
    letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
    exact (inferInstance : IsSolvable G)
  · -- some nonidentity element has order different from two; since the order of an
    -- element divides the order of the group (≤ 4), its order is the order of the
    -- group, so the group is cyclic and commutative
    have hnot : ∃ x : G, x ≠ 1 ∧ orderOf x ≠ 2 := by
      by_contra h
      apply htwo
      intro x hx
      by_contra hord
      exact h ⟨x, hx, hord⟩
    rcases hnot with ⟨x, hxne, hord2⟩
    letI : Fintype G := Fintype.ofFinite G
    have hdiv : orderOf x ∣ Nat.card G := by
      rw [Nat.card_eq_fintype_card]
      exact orderOf_dvd_card
    have hord : orderOf x = Nat.card G := by
      have hne1 : orderOf x ≠ 1 := by
        intro h
        exact hxne ((orderOf_eq_one_iff).1 h)
      have hne0 : orderOf x ≠ 0 := by
        intro h
        rw [h] at hdiv
        rcases hdiv with ⟨k, hk⟩
        exact hpos.ne' (by rw [hk]; simp)
      have hge3 : 3 ≤ orderOf x := by omega
      have hle4 : orderOf x ≤ 4 := le_trans (Nat.le_of_dvd hpos hdiv) h
      have hcases : orderOf x = 3 ∨ orderOf x = 4 := by
        by_cases h3 : orderOf x = 3
        · exact Or.inl h3
        · right
          apply le_antisymm hle4
          have hge4 : 4 ≤ orderOf x := by omega
          exact hge4
      rcases hcases with h3 | h4
      · rcases hdiv with ⟨k, hk⟩
        rw [h3] at hk
        rw [h3, hk]
        have hk1 : k = 1 := by omega
        rw [hk1]
      · rcases hdiv with ⟨k, hk⟩
        rw [h4] at hk
        rw [h4, hk]
        have hk1 : k = 1 := by omega
        rw [hk1]
    have hz : Subgroup.zpowers x = ⊤ := by
      have hzcard : Nat.card (Subgroup.zpowers x) = Nat.card G := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_zpowers]
        exact hord.trans Nat.card_eq_fintype_card
      exact Subgroup.eq_top_of_card_eq (Subgroup.zpowers x) hzcard
    have hcomm : ∀ a b : G, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.zpowers x := by simp [hz]
      rcases (Subgroup.mem_zpowers_iff).1 ha with ⟨m, hm⟩
      have hb : b ∈ Subgroup.zpowers x := by simp [hz]
      rcases (Subgroup.mem_zpowers_iff).1 hb with ⟨n, hn⟩
      rw [← hm, ← hn]
      calc
        x ^ m * x ^ n = x ^ (m + n) := (zpow_add x m n).symm
        _ = x ^ (n + m) := congrArg (fun t : ℤ => x ^ t) (add_comm m n)
        _ = x ^ n * x ^ m := zpow_add x n m
    letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
    exact (inferInstance : IsSolvable G)

/-- The sporadic arm of the Schreier property (GLS vol. 3, Theorem 7.1.1(a)): the
outer automorphism group of a sporadic simple group is solvable.  Currently the
`Spor` family has no members formalized, so the statement is vacuous. -/
public theorem isSolvable_Out_of_isSporGroup {K : Type u} [Group K]
    (h : IsSporGroup K) : IsSolvable (Out K) := by
  cases h


end GroupTheory

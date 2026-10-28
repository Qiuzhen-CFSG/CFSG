module

public import Mathlib.GroupTheory.Solvable

/-!
# Minimal finite simple groups

A minimal simple group is a finite nonsolvable simple group whose proper
subgroups are solvable. For a simple group, nonsolvability is equivalent to
noncommutativity; simplicity already includes nontriviality. The predicate
therefore describes the standard nonabelian minimal-simple groups, excluding
cyclic groups of prime order.

This module provides the subgroup and isomorphism interface for Thompson's
classification. A nonsolvable subgroup must be the whole group. Applying this
to the range of an injective homomorphism gives a useful obstruction to proper
embeddings. Proper subgroups of any homomorphic image are solvable as well,
by pulling them back and using preservation of solvability under surjections.
Isomorphism transport sends proper subgroups through the inverse
map and transfers solvability along the induced subgroup equivalence.

Source: the definition of minimal simple in GLS, The Classification of the
Finite Simple Groups, volume 1, §28, preceding (28.1). All proofs here use
only elementary group theory and no classification theorem.
-/

/-- A finite nonabelian simple group with solvable proper subgroups. -/
public structure IsMinimalSimple (G : Type*) [Group G] [Finite G] : Prop where
  isSimpleGroup : IsSimpleGroup G
  not_isSolvable : ¬ Group.IsSolvable G
  solvable_of_lt : ∀ H : Subgroup G, H < ⊤ → Group.IsSolvable H

namespace IsMinimalSimple

variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- Every nonsolvable subgroup of a minimal simple group is the whole group. -/
public theorem eq_top_of_not_isSolvable (hG : IsMinimalSimple G)
    (K : Subgroup G) (hK : ¬ Group.IsSolvable K) : K = ⊤ := by
  by_contra hproper
  exact hK (hG.solvable_of_lt K (lt_top_iff_ne_top.mpr hproper))

/-- In a minimal simple group, solvable subgroups are exactly proper subgroups. -/
public theorem isSolvable_iff_ne_top (hG : IsMinimalSimple G) (K : Subgroup G) :
    Group.IsSolvable K ↔ K ≠ ⊤ := by
  constructor
  · intro hK htop
    subst K
    let _ := hK
    exact hG.not_isSolvable
      (Group.isSolvable_of_surjective (f := Subgroup.topEquiv.toMonoidHom)
        Subgroup.topEquiv.surjective)
  · exact fun hK => hG.solvable_of_lt K (lt_top_iff_ne_top.mpr hK)

/-- A nonsolvable group cannot embed properly into a minimal simple group. -/
public theorem surjective_of_injective (hG : IsMinimalSimple G)
    (hH : ¬ Group.IsSolvable H) (f : H →* G) (hf : Function.Injective f) :
    Function.Surjective f := by
  apply MonoidHom.range_eq_top.mp
  apply hG.eq_top_of_not_isSolvable
  intro hrange
  let _ := hrange
  exact hH (Group.isSolvable_of_isSolvable_injective
    (f := f.rangeRestrict) (by
      intro a b hab
      exact hf (congrArg Subtype.val hab)))

/-- Every proper subgroup of a homomorphic image of a minimal simple group
is solvable. No injectivity or finiteness assumption on the target is needed. -/
public theorem isSolvable_of_lt_range (hG : IsMinimalSimple G)
    (f : G →* H) (K : Subgroup H) (hK : K < f.range) : Group.IsSolvable K := by
  have hproper : K.comap f ≠ ⊤ := by
    intro htop
    apply (not_le_of_gt hK)
    rintro y ⟨x, rfl⟩
    have hx : x ∈ K.comap f := htop ▸ Subgroup.mem_top x
    exact hx
  let _ := hG.solvable_of_lt (K.comap f) (lt_top_iff_ne_top.mpr hproper)
  let fK : K.comap f →* K :=
    (f.domRestrict (K.comap f)).codRestrict K (fun x => x.property)
  apply Group.isSolvable_of_surjective (f := fK)
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hK.le hy
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  change f x ∈ K
  rwa [hx]

/-- A nontrivial solvable subgroup has proper normalizer in a minimal simple group. -/
public theorem normalizer_lt_top (hG : IsMinimalSimple G)
    (K : Subgroup G) (hne : K ≠ ⊥) (hK : Group.IsSolvable K) :
    Subgroup.normalizer (K : Set G) < ⊤ := by
  let _ := hG.isSimpleGroup
  apply lt_top_iff_ne_top.mpr
  intro hnormalizer
  have hnormal := Subgroup.normalizer_eq_top_iff.mp hnormalizer
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · exact hne hbot
  · exact (hG.isSolvable_iff_ne_top K).mp hK htop

/-- Minimal simplicity transports along any multiplicative equivalence. -/
public theorem of_mulEquiv [Finite H] (hG : IsMinimalSimple G) (e : G ≃* H) :
    IsMinimalSimple H := by
  refine ⟨e.isSimpleGroup_congr.mp hG.isSimpleGroup, ?_, ?_⟩
  · intro hH
    let _ := hH
    exact hG.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · intro K hK
    have hproper : K.map e.symm.toMonoidHom ≠ ⊤ := by
      intro htop
      apply (ne_of_lt hK)
      apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
      rw [htop, Subgroup.map_top_of_surjective _ e.symm.surjective]
    let : Group.IsSolvable (K.map e.symm.toMonoidHom) :=
      hG.solvable_of_lt (K.map e.symm.toMonoidHom)
      (lt_top_iff_ne_top.mpr hproper)
    exact Group.isSolvable_of_isSolvable_injective
      (f := e.symm.toMonoidHom.subgroupMap K) (by
        intro a b hab
        apply Subtype.ext
        exact e.symm.injective (congrArg Subtype.val hab))

/-- Minimal simplicity is an isomorphism invariant. -/
public theorem iff_of_mulEquiv [Finite H] (e : G ≃* H) :
    IsMinimalSimple G ↔ IsMinimalSimple H :=
  ⟨fun hG => hG.of_mulEquiv e, fun hH => hH.of_mulEquiv e.symm⟩

end IsMinimalSimple

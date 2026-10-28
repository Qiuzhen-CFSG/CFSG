module

public import Theory.GroupTheory.CentricRadicalObstructions

/-!
# Normalizer witnesses in the automorphism p-core

An element outside U that normalizes U and acts in O_p(Aut(U)) obstructs
intrinsic radicality when U is centric. Such witnesses transport through
ambient group isomorphisms. In a finite p-group every proper subgroup with
p-group automorphism group has a witness by the normalizer condition.

Source: the normal-p-subgroup obstruction underlying Alperin fusion,
as in `CentricRadicalObstructions`.
-/

namespace Subgroup

/-- A normalizer element outside U whose intrinsic action lies in the
p-core of the full automorphism group. -/
@[expose] public def HasPCoreNormalizerWitness
    {G : Type*} [Group G] (U : Subgroup G) (p : ℕ) : Prop :=
  ∃ g : normalizer (U : Set G), (g : G) ∉ U ∧
    U.normalizerMonoidHom g ∈ pCore p (MulAut U)

/-- These witnesses are preserved by ambient group isomorphisms. -/
public theorem HasPCoreNormalizerWitness.map
    {G H : Type*} [Group G] [Group H] (p : ℕ)
    (U : Subgroup G) (e : G ≃* H)
    (hw : U.HasPCoreNormalizerWitness p) :
    (U.map e.toMonoidHom).HasPCoreNormalizerWitness p := by
  obtain ⟨g, hg, ha⟩ := hw
  let V := U.map e.toMonoidHom
  let g' : normalizer (V : Set H) :=
    ⟨e g, U.le_normalizer_map e.toMonoidHom (mem_map_of_mem _ g.property)⟩
  refine ⟨g', ?_, ?_⟩
  · intro hh
    obtain ⟨u, hu, he⟩ := hh
    exact hg (e.injective he ▸ hu)
  · have hmap := mem_map_of_mem (MulAut.congr (e.subgroupMap U)).toMonoidHom ha
    rw [pCore_map_iso] at hmap
    have heq : V.normalizerMonoidHom g' =
        MulAut.congr (e.subgroupMap U) (U.normalizerMonoidHom g) := by
      ext x
      change (e g) * (x : H) * (e g)⁻¹ =
        e ((g : G) * e.symm x * (g : G)⁻¹)
      simp
    rw [heq]
    exact hmap

/-- A centric intrinsic radical subgroup has no such witness. -/
public theorem not_hasPCoreNormalizerWitness_of_intrinsic_radical
    {G : Type*} [Group G] {p : ℕ} (U : Subgroup G)
    (hcent : centralizer (U : Set G) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore p (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range) :
    ¬ U.HasPCoreNormalizerWitness p := by
  rintro ⟨g, hg, ha⟩
  exact hg (mem_of_normalizerMonoidHom_mem_inner U hcent g
    (hrad ⟨⟨g, rfl⟩, ha⟩))

/-- The normalizer condition supplies a witness whenever the full
 automorphism group of a proper subgroup is a p-group. -/
public theorem hasPCoreNormalizerWitness_of_isPGroup_mulAut
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (U : Subgroup G) (hproper : U ≠ ⊤)
    (ha : IsPGroup p (MulAut U)) : U.HasPCoreNormalizerWitness p := by
  let := hG.isNilpotent
  obtain ⟨g, hgn, hgu⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent U (lt_top_iff_ne_top.mpr hproper))
  refine ⟨⟨g, hgn⟩, hgu, ?_⟩
  have hle : (⊤ : Subgroup (MulAut U)) ≤ pCore p (MulAut U) :=
    le_sSup ⟨inferInstance, ha.to_subgroup ⊤⟩
  exact hle (mem_top _)

end Subgroup

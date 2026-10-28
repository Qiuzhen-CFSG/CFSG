module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.HyperplaneFixer
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryOffender.SectionLinear
/-!
# Small images in the natural symmetric-six action

A nontrivial actor with fixed codimension at most one is the cyclic group
of a transposition. The fixed hyperplane has a one-dimensional perpendicular;
the existing pointwise-fixer theorem identifies its only possible nonidentity
actor. Thus the point-core displacement and fixer calculations apply to any
such small image without a separately supplied transposition witness.

Source application: MS93 (5.7), printed p.919, on the literal natural layer
at the critical endpoint. No claim about an extended X-layer is used.
-/
public section
open Subgroup BinaryPermutation Representation.BinaryOffender
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed
open NaturalGeometry NaturalPairing

/-- Every nontrivial natural image of fixed codimension at most one is generated
by one transposition. -/
theorem small_image_eq_zpowers (A:Subgroup S) (hne:A≠⊥)
    (hsmall:fixedCodim (naturalRepresentation Ω) A≤1) :
    ∃t∈A, t.IsSwap ∧ A=zpowers t := by
  have hc : fixedCodim (naturalRepresentation Ω) A=1 := by
    have hn : fixedCodim (naturalRepresentation Ω) A≠0 := by
      intro hz
      have ht := (fixedCodim_eq_zero_iff _ _).mp hz
      apply hne
      apply bot_unique
      intro g hg
      have he : naturalRepresentation Ω g=1 := by
        ext v : 1
        exact (show v∈fixedSpace (naturalRepresentation Ω) A from ht ▸ Submodule.mem_top) ⟨g,hg⟩
      exact (naturalRepresentation_injective Ω (by decide)) (he.trans (naturalRepresentation Ω).map_one.symm)
    omega
  let F := fixedSpace (naturalRepresentation Ω) A
  have hF : Module.finrank (ZMod 2) F=3 := by
    have hh := fixedCodim_add_finrank (naturalRepresentation Ω) A
    rw [hc,finrank_natural_even Ω (by decide)] at hh
    change 1 + Module.finrank (ZMod 2) F=4 at hh
    omega
  let P := form.orthogonal F
  have hP : Module.finrank (ZMod 2) P=1 := by
    dsimp only [P]
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,hF,
      finrank_natural_even Ω (by decide)]
    rfl
  have hPF : form.orthogonal P=F :=
    LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl F
  obtain ⟨t,ht,hbound⟩ := HyperplaneFixer.exists_swap_bound_line P hP
  have hb (g:S) (hg:g∈A) : g=1 ∨ g=t := by
    apply hbound g
    intro v hv
    rw [hPF] at hv
    exact hv ⟨g,hg⟩
  obtain ⟨g,hg,hgne⟩ := (A.bot_or_exists_ne_one).resolve_left hne
  have hgt : g=t := (hb g hg).resolve_left hgne
  have htA : t∈A := hgt ▸ hg
  refine ⟨t,htA,ht,le_antisymm ?_ (zpowers_le.mpr htA)⟩
  intro g hg
  rcases hb g hg with rfl|rfl
  · exact one_mem _
  · exact mem_zpowers _

/-- The point core moves the fixed space of the supplied small image into
that same image’s moved line. -/
theorem small_image_fixed_displacement_le (u:S) (A:Subgroup S)
    (hA:A≤pointCore.map (MulAut.conj u).toMonoidHom) (hne:A≠⊥)
    (hsmall:fixedCodim (naturalRepresentation Ω) A≤1) :
    subspaceCommutator (naturalRepresentation Ω) (fixedSpace (naturalRepresentation Ω) A)
      (pointCore.map (MulAut.conj u).toMonoidHom) ≤
        subspaceCommutator (naturalRepresentation Ω) ⊤ A := by
  obtain ⟨t,ht,hs,he⟩ := small_image_eq_zpowers A hne hsmall
  rw [he]
  exact fixed_displacement_le u t (hA ht) hs

/-- The pointwise fixer of the small-image fixed space inside the actual
point core is the image itself. -/
theorem small_image_fixes_iff (u:S) (A:Subgroup S)
    (hA:A≤pointCore.map (MulAut.conj u).toMonoidHom) (hne:A≠⊥)
    (hsmall:fixedCodim (naturalRepresentation Ω) A≤1)
    (g:S) (hg:g∈pointCore.map (MulAut.conj u).toMonoidHom) :
    (∀v∈fixedSpace (naturalRepresentation Ω) A,naturalRepresentation Ω g v=v) ↔ g∈A := by
  obtain ⟨t,ht,hs,he⟩ := small_image_eq_zpowers A hne hsmall
  rw [he]
  exact fixes_fixedSpace_iff u t g (hA ht) hs hg
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed

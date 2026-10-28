module
public import Theory.Representation.AlternatingSixPairedCovers.Inputs
public import Theory.Representation.BinaryConjugationSection.DescendedSubrepresentation
public import Theory.Representation.BinaryConjugationSection.FixedIndex
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan

/-!
# Paired A₆ covers inside the original quotient action

The two literal sections descend through the same component map and embed
in the whole binary quotient. Their coordinate images supply the two marked
subrepresentations; the original subgroup permutation supplies the whole
actor's permutation. The commutator preimage is exactly the fixed space, so
the original cover identity proves the required span. Intersections of the
covers and of their central kernels remain unrestricted.

Source: Aschbacher--Smith, 14.6.22--24, printed pp.1038--1041.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace AlternatingSixPairedCovers
variable {G D E V V' : Type*} [Group G] [Group D]
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V'] [Module (ZMod 2) V']

private theorem naturalOrCore_transport
    {J : Type*} [Group J] {σ : Representation (ZMod 2) J V}
    {τ : Representation (ZMod 2) J V'}
    (f : J →* Equiv.Perm (Fin 6)) (e : V ≃ₗ[ZMod 2] V')
    (he : ∀ j v, e (σ j v) = τ j (e v))
    (hm : BinaryPermutation.SixCover.IsNaturalOrCore σ f) :
    BinaryPermutation.SixCover.IsNaturalOrCore τ f := by
  have hi (j : J) (v : V') : e.symm (τ j v) = σ j (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply,he,e.apply_symm_apply]
  rcases hm with ⟨a,ha⟩ | ⟨a,ha⟩
  · exact Or.inl ⟨e.symm.trans a,fun j v => by
      change a (e.symm (τ j v)) = _
      rw [hi,ha]; rfl⟩
  · exact Or.inr ⟨e.symm.trans a,fun j v => by
      change a (e.symm (τ j v)) = _
      rw [hi,ha]; rfl⟩

private theorem imageSpace_sup {H U Z A B : Subgroup G}
    {τ : Representation (ZMod 2) H E} (c : BinaryConjugationSection H U Z τ)
    (hAU : A ≤ U) (hBU : B ≤ U) :
    c.imageSpace (A ⊔ B) = c.imageSpace A ⊔ c.imageSpace B := by
  let o : Subgroup (Multiplicative E) ≃o Submodule (ZMod 2) E :=
    Subgroup.toAddSubgroup'.trans (AddSubgroup.toZModSubmodule 2)
  change o (((A ⊔ B).subgroupOf U).map c.coordinates) =
    o ((A.subgroupOf U).map c.coordinates) ⊔ o ((B.subgroupOf U).map c.coordinates)
  rw [subgroupOf_sup hAU hBU,Subgroup.map_sup,o.map_sup]

/-- Construct the simultaneous paired action from actual group sections,
retaining both support images in the original whole quotient. -/
theorem exists_data_of_sections
    {H K U Z A B : Subgroup G} {ρ : Representation (ZMod 2) D E}
    (π : H →* D) (hπ : Function.Surjective π)
    (κ : alternatingGroup (Fin 6) →* D) (hi : Function.Injective κ)
    (hn : κ.range.Normal) (hz : centralizer (κ.range : Set D) = ⊥)
    (f : K →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (c : BinaryConjugationSection H U Z (ρ.comp π))
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (σ' : Representation (ZMod 2) (alternatingGroup (Fin 6)) V')
    (d : BinaryConjugationSection K A Z (σ.comp f))
    (d' : BinaryConjugationSection K B Z (σ'.comp f))
    (hKH : K ≤ H) (hAU : A ≤ U) (hBU : B ≤ U)
    (hκ : ∀ k : K, π (inclusion hKH k) = κ (f k))
    (hm : BinaryPermutation.SixCover.IsNaturalOrCore σ (alternatingGroup (Fin 6)).subtype)
    (hm' : BinaryPermutation.SixCover.IsNaturalOrCore σ'
      (BinaryAlternatingSix.diagramAut.toMonoidHom.comp (alternatingGroup (Fin 6)).subtype))
    (hUZ : U ≤ normalizer (Z : Set G))
    (hcover : U ≤ A ⊔ B ⊔ commutatorPreimage U H Z)
    (hperm : ∀ x ∈ H,
      (A.map (MulAut.conj x).toMonoidHom = A ∧ B.map (MulAut.conj x).toMonoidHom = B) ∨
      (A.map (MulAut.conj x).toMonoidHom = B ∧ B.map (MulAut.conj x).toMonoidHom = A)) :
    ∃ C : Data ρ, C.component = κ ∧
      C.first.toSubmodule = c.imageSpace A ∧ C.second.toSubmodule = c.imageSpace B := by
  obtain ⟨R,hR,e,he,_⟩ := c.exists_descended_subrepresentation π κ f hf d hKH hAU hκ
  obtain ⟨R',hR',e',he',_⟩ := c.exists_descended_subrepresentation π κ f hf d' hKH hBU hκ
  have hfix : c.imageSpace (commutatorPreimage U H Z) = fixedSpace ρ ⊤ := by
    rw [c.fixed_image_eq H le_rfl hUZ,subgroupOf_self,fixedSpace_comp_map,
      Subgroup.map_top_of_surjective π hπ]
  have hspan : R.toSubmodule ⊔ R'.toSubmodule ⊔ fixedSpace ρ ⊤ = ⊤ := by
    apply top_unique
    rw [hR,hR',←hfix,←imageSpace_sup c hAU hBU,
      ←imageSpace_sup c (sup_le hAU hBU) (commutatorPreimage_le U H Z),←c.imageSpace_self]
    exact c.imageSpace_mono hcover
  have hpres (x : H) (P Q : Subgroup G) (hP : P ≤ U)
      (heq : P.map (MulAut.conj (x:G)).toMonoidHom = Q)
      (v : E) (hv : v ∈ c.imageSpace P) : ρ (π x) v ∈ c.imageSpace Q := by
    rw [←heq]
    change _ ∈ c.imageSpace (P.conjBy (x:G))
    rw [c.imageSpace_conjBy P hP x]
    exact ⟨v,hv,rfl⟩
  let C : Data ρ := {
    component := κ
    injective := hi
    normal := hn
    centralizer := hz
    first := R
    second := R'
    first_model := naturalOrCore_transport _ e he hm
    second_model := naturalOrCore_transport _ e' he' hm'
    span := hspan
    permutes := by
      intro a
      obtain ⟨x,rfl⟩ := hπ a
      change ((∀ v ∈ R.toSubmodule, ρ (π x) v ∈ R.toSubmodule) ∧
        (∀ v ∈ R'.toSubmodule, ρ (π x) v ∈ R'.toSubmodule)) ∨
        ((∀ v ∈ R.toSubmodule, ρ (π x) v ∈ R'.toSubmodule) ∧
        (∀ v ∈ R'.toSubmodule, ρ (π x) v ∈ R.toSubmodule))
      rw [hR,hR']
      rcases hperm x x.property with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact Or.inl ⟨hpres x A A hAU ha,hpres x B B hBU hb⟩
      · exact Or.inr ⟨hpres x A B hAU ha,hpres x B A hBU hb⟩ }
  exact ⟨C,rfl,hR,hR'⟩
end AlternatingSixPairedCovers

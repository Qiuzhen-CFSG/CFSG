module

public import Theory.SpecificGroups.SymmetricSix.ExceptionalAlternatingFive.Natural
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors

/-!
# The actual transitive six-letter alternating five

Transport the trace-determinant embedding through the concrete polar
isomorphism. Its transitive natural action on the fifteen nonzero vectors
is the action on duads, and duad transitivity forces transitivity on letters.
The final range subgroup retains the same SL₂(4) and vector coordinates.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymmetricSix.ExceptionalAlternatingFive
open Representation.SL2FourNatural
open Subgroup
open scoped Matrix

private theorem letters_transitive_of_duads (j : SL →* S6)
    (hd : ∀ d e : Duad, ∃ g : SL, j g • d = e) :
    ∀ i k : Letter, ∃ g : SL, j g i = k := by
  intro i k
  by_cases hik : i = k
  · exact ⟨1, by simp [hik]⟩
  have hthird : ∀ i k : Letter, ∃ l : Letter, l ≠ i ∧ l ≠ k := by decide +kernel
  obtain ⟨l,hli,hlk⟩ := hthird i k
  obtain ⟨d,hdset⟩ := duadSet_complete {i,l} (by simp [hli.symm])
  obtain ⟨e,heset⟩ := duadSet_complete {k,l} (by simp [hlk.symm])
  obtain ⟨g,hg⟩ := hd d e
  have hs := congrArg duadSet hg
  rw [duadSet_smul,hdset,heset] at hs
  have hi : j g i ∈ ({k,l} : Finset Letter) :=
    hs ▸ Finset.mem_image.mpr ⟨i,by simp,rfl⟩
  have hl : j g l ∈ ({k,l} : Finset Letter) :=
    hs ▸ Finset.mem_image.mpr ⟨l,by simp,rfl⟩
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi hl
  rcases hi with hi | hi
  · exact ⟨g,hi⟩
  · have hl' : j g l = k := hl.resolve_right (fun he => hli ((j g).injective (he.trans hi.symm)))
    refine ⟨g * g,?_⟩
    rw [map_mul]
    change j g (j g i) = k
    rw [hi,hl']

/-- The same native SL₂(4) embedding is transitive on all six letters and
its polar action is the literal scalar-restricted natural module. -/
theorem exists_marked_six_embedding :
    ∃ e : V ≃ₗ[ZMod 2] NaturalModule, ∃ j : SL →* S6,
      Function.Injective j ∧
      (∀ g v, (polarRepresentation (j g)).val *ᵥ e v = e (action g v)) ∧
      (∀ i k : Letter, ∃ g : SL, j g i = k) := by
  obtain ⟨e,φ,hφ,he⟩ := exists_marked_symplectic_embedding
  let j : SL →* S6 := SymplecticFour.Binary.symmetricSixEquiv.symm.toMonoidHom.comp φ
  have hj : Function.Injective j :=
    SymplecticFour.Binary.symmetricSixEquiv.symm.injective.comp hφ
  have hφj (g : SL) : polarRepresentation (j g) = φ g := by
    rw [← SymplecticFour.Binary.symmetricSixEquiv_apply]
    exact SymplecticFour.Binary.symmetricSixEquiv.apply_symm_apply _
  have hmark (g : SL) (v : V) :
      (polarRepresentation (j g)).val *ᵥ e v = e (action g v) := by
    rw [hφj]
    exact he g v
  refine ⟨e,j,hj,hmark,letters_transitive_of_duads j ?_⟩
  intro d f
  have hn (a : Duad) : e.symm (polarVector a).val ≠ 0 := by
    intro hh
    have hz := congrArg e hh
    exact (polarVector a).property (by simpa using hz)
  obtain ⟨g,hg⟩ := transitive_nonzero _ _ (hn d) (hn f)
  refine ⟨g,polarVector_injective (Subtype.ext ?_)⟩
  rw [← polarRepresentation_equivariant]
  have hh := hmark g (e.symm (polarVector d).val)
  simpa only [LinearEquiv.apply_symm_apply,hg] using hh

/-- An actual exceptional A₅ subgroup, with the same field-natural marking,
transitive six-letter action, and transitive action on all fifteen nonzero
vectors of the original four-dimensional polar module. -/
theorem exists_marked_exceptional_alternatingFive :
    ∃ H : Subgroup S6, ∃ s : H ≃* alternatingGroup (Fin 5),
      ∃ e : NaturalModule ≃ₗ[ZMod 2] V,
        (∀ i k : Letter, ∃ h : H, (h : S6) i = k) ∧
        (∀ (h : H) v, e ((polarRepresentation h.val).val *ᵥ v) =
          action (alternatingFiveEquiv.symm (s h)) (e v)) ∧
        (∀ v w : NaturalModule, v ≠ 0 → w ≠ 0 →
          ∃ h : H, (polarRepresentation h.val).val *ᵥ v = w) := by
  obtain ⟨e,j,hj,hmark,hletters⟩ := exists_marked_six_embedding
  let H := j.range
  let k : SL ≃* H := MonoidHom.ofInjective hj
  let s : H ≃* alternatingGroup (Fin 5) := k.symm.trans alternatingFiveEquiv
  have hk (g : SL) : (k g : S6) = j g := MonoidHom.ofInjective_apply hj
  refine ⟨H,s,e.symm,?_,?_,?_⟩
  · intro i l
    obtain ⟨g,hg⟩ := hletters i l
    exact ⟨k g,hg⟩
  · intro h v
    obtain ⟨g,rfl⟩ := k.surjective h
    have hh := congrArg e.symm (hmark g (e.symm v))
    simpa [s,hk] using hh
  · intro v w hv hw
    have hn (x : NaturalModule) (hx : x ≠ 0) : e.symm x ≠ 0 := by
      intro he
      exact hx (by simpa using congrArg e he)
    obtain ⟨g,hg⟩ := transitive_nonzero _ _ (hn v hv) (hn w hw)
    refine ⟨k g,?_⟩
    have hh := hmark g (e.symm v)
    simpa only [hk,LinearEquiv.apply_symm_apply,hg] using hh

end Theory.SpecificGroups.SymmetricSix.ExceptionalAlternatingFive

module
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Natural SL₂ coordinates under automorphisms

Every automorphism of SL₂ over a finite binary field is inner times a field
map. Applying that same semilinear map to vectors gives additive coordinates
intertwining the two natural actions. The quotient version descends an
original group automorphism through a characteristic kernel, retaining the
literal quotient map. Upper and lower transvections also generate every
vector by displacements.

The crossed Sp₄ block application uses these results to correct the action
of the original crossing element on L/O₂(L), without assuming that it acts
trivially or that the correction is linear over the larger field.
Source: Aschbacher–Smith, original 4.3.7, printed p.616; the SL₂ automorphism
input is the binary case of GLS4, Chapter4, Lemma3.1(a).
-/

public section
noncomputable section
open Matrix
namespace Representation.SL2NaturalTransport
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The natural additive module realizes every binary SL₂ automorphism. -/
theorem automorphism_coordinates (a : MulAut (SpecialLinearGroup (Fin 2) F)) :
    ∃ e : (Fin 2 → F) ≃+ (Fin 2 → F), ∀ g v,
      e (g.val.mulVec v) = (a g).val.mulVec (e v) := by
  obtain ⟨b,σ,rfl⟩ := Theory.PSL2.sl2_semilinear_coverage a
  let s : (Fin 2 → F) ≃+ (Fin 2 → F) := AddEquiv.piCongrRight (fun _ => σ.toAddEquiv)
  let e := s.trans (Matrix.SpecialLinearGroup.toLin' b).toAddEquiv
  have hs (g : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
      s (g.val.mulVec v) = (Theory.PSL2.sl2FieldAut σ g).val.mulVec (s v) := by
    ext i
    simp [s, mulVec, dotProduct, Fin.sum_univ_two, Theory.PSL2.sl2FieldAut]
  refine ⟨e,fun g v => ?_⟩
  change b.val.mulVec (s (g.val.mulVec v)) =
    (b * Theory.PSL2.sl2FieldAut σ g * b⁻¹).val.mulVec (b.val.mulVec (s v))
  rw [hs]
  simp only [mulVec_mulVec, ←SpecialLinearGroup.coe_mul, inv_mul_cancel_right]

/-- Correct the natural action along an original automorphism and quotient. -/
theorem quotient_automorphism_coordinates
    {X : Type*} [Group X] (p : X →* SpecialLinearGroup (Fin 2) F)
    (hp : Function.Surjective p) [p.ker.Characteristic] (a : MulAut X) :
    ∃ e : (Fin 2 → F) ≃+ (Fin 2 → F), ∀ x v,
      e ((p x).val.mulVec v) = (p (a x)).val.mulVec (e v) := by
  let j := QuotientGroup.quotientKerEquivOfSurjective p hp
  let b := MulAut.congr j (Subgroup.quotientAut p.ker a)
  have hb (x : X) : b (p x) = p (a x) := by
    change j (Subgroup.quotientAut p.ker a (j.symm (j (QuotientGroup.mk' p.ker x)))) = _
    rw [j.symm_apply_apply, Subgroup.quotientAut_apply_mk]
    rfl
  obtain ⟨e,he⟩ := automorphism_coordinates b
  exact ⟨e,fun x v => by rw [←hb]; exact he (p x) v⟩

omit [Finite F] [CharP F 2] in
/-- Upper and lower transvection displacements generate the full natural module. -/
theorem natural_displacements_span (Q : AddSubgroup (Fin 2 → F))
    (hQ : ∀ (g : SpecialLinearGroup (Fin 2) F) v, g.val.mulVec v - v ∈ Q) :
    Q = ⊤ := by
  let u : SpecialLinearGroup (Fin 2) F := ⟨!![1,1;0,1],by simp⟩
  let d : SpecialLinearGroup (Fin 2) F := ⟨!![1,0;1,1],by simp⟩
  apply top_unique
  intro v _
  have h0 := hQ u ![0,v 0]
  have h1 := hQ d ![v 1,0]
  have he : (u.val.mulVec ![0,v 0] - ![0,v 0]) +
      (d.val.mulVec ![v 1,0] - ![v 1,0]) = v := by
    ext i
    simp only [Pi.add_apply,Pi.sub_apply,mulVec,dotProduct,Fin.sum_univ_two]
    fin_cases i <;> simp [u,d]
  exact he ▸ Q.add_mem h0 h1

end Representation.SL2NaturalTransport

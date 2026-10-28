module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointAction
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
/-!
# Point-fixer action for every point of the natural module

Even permutations move the distinguished duad to any nonzero vector.
Conjugating the faithful canonical hyperplane action therefore realizes
all automorphisms of that vector's perpendicular fixing the vector.
All actions remain the original augmentation-quotient representation.

Source: Aschbacher--Smith, §B.3 and 13.5.5, printed pp.83--85 and 916.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointAction
open NaturalGeometry NaturalPairing
noncomputable abbrev Perpendicular (v : V) := form.orthogonal (Submodule.span (ZMod 2) {v})
private theorem mem_perpendicular (v w : V) : w ∈ Perpendicular v ↔ form v w = 0 := by
  constructor
  · intro h
    exact h v (Submodule.subset_span (by simp))
  · intro h x hx
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [h]
noncomputable def perpendicularPoint (v : V) : Multiplicative (Perpendicular v) :=
  Multiplicative.ofAdd ⟨v,by exact (mem_perpendicular v v).mpr (form_alt v)⟩
private theorem map_perpendicular (g : S) (v : V) (hg : naturalRepresentation Ω g (pairVector 4 5) = v) :
    Hyperplane.map (naturalRepresentation Ω g) = Perpendicular v := by
  apply le_antisymm
  · rintro _ ⟨w,hw,rfl⟩
    apply (mem_perpendicular _ _).mpr
    rw [← hg,form_invariant]
    exact (mem_perpendicular _ _).mp hw
  · intro w hw
    refine ⟨naturalRepresentation Ω g⁻¹ w, ?_, ?_⟩
    · apply (mem_perpendicular _ _).mpr
      have hh := form_invariant g (pairVector 4 5) (naturalRepresentation Ω g⁻¹ w)
      simp only [← Module.End.mul_apply, ← map_mul,mul_inv_cancel,map_one,Module.End.one_apply,hg] at hh
      exact hh.symm.trans ((mem_perpendicular _ _).mp hw)
    · simp only [← Module.End.mul_apply, ← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
noncomputable def transport (g : S) (v : V)
    (hg : naturalRepresentation Ω g (pairVector 4 5) = v) :
    Multiplicative Hyperplane ≃* Multiplicative (Perpendicular v) :=
  ((LinearMap.GeneralLinearGroup.toLinearEquiv ((naturalRepresentation Ω).asGroupHom g)).ofSubmodules
    Hyperplane (Perpendicular v) (by exact map_perpendicular g v hg)).toAddEquiv.toMultiplicative
private theorem transport_point (g : S) (v : V) (hg) :
    transport g v hg point = perpendicularPoint v := by
  apply Multiplicative.toAdd.injective
  exact Subtype.ext hg
private theorem transport_apply (g : S) (v : V) (hg) (w : Multiplicative Hyperplane) :
    (transport g v hg w).toAdd.val = naturalRepresentation Ω g w.toAdd.val := rfl
private theorem transport_symm_apply (g : S) (v : V) (hg)
    (w : Multiplicative (Perpendicular v)) :
    ((transport g v hg).symm w).toAdd.val = naturalRepresentation Ω g⁻¹ w.toAdd.val := rfl

theorem exists_even_action (v : V) (hv : v ≠ 0)
    (a : MulAut (Multiplicative (Perpendicular v)))
    (ha : a (perpendicularPoint v) = perpendicularPoint v) :
    ∃g:alternatingGroup Ω, naturalRepresentation Ω g.val v = v ∧
      ∀w:Multiplicative (Perpendicular v), (a w).toAdd.val = naturalRepresentation Ω g.val w.toAdd.val := by
  obtain ⟨g,hg⟩ := NaturalTransport.exists_even_image v hv
  let e := transport g.val v hg
  let b := (MulAut.congr e.symm) a
  have hb : b point = point := by
    apply e.injective
    change e (e.symm (a (e point))) = e point
    rw [e.apply_symm_apply,show e point = perpendicularPoint v from transport_point _ _ _,ha]
  obtain ⟨k,hk⟩ := exists_action b hb
  refine ⟨g * ⟨k.val,by exact k.property.2⟩ * g⁻¹, ?_, ?_⟩
  · rw [← hg]
    have hp := action_fixes_point k
    have hp' : naturalRepresentation Ω k.val (pairVector 4 5) = pairVector 4 5 :=
      congrArg (fun w:Multiplicative Hyperplane => w.toAdd.val) hp
    change naturalRepresentation Ω (g.val * k.val * g.val⁻¹)
      (naturalRepresentation Ω g.val (pairVector 4 5)) = _
    have hi : naturalRepresentation Ω g.val⁻¹
        (naturalRepresentation Ω g.val (pairVector 4 5)) = pairVector 4 5 := by
      rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
    simp only [map_mul,Module.End.mul_apply,hi,hp']
  · intro w
    have he : a w = e (actionHom k (e.symm w)) := by
      rw [hk]
      change a w = e (e.symm (a (e (e.symm w))))
      simp only [e.apply_symm_apply]
    rw [he,transport_apply]
    change naturalRepresentation Ω g.val (naturalRepresentation Ω k.val ((e.symm w).toAdd.val)) = _
    rw [transport_symm_apply]
    change naturalRepresentation Ω g.val (naturalRepresentation Ω k.val
      (naturalRepresentation Ω g.val⁻¹ w.toAdd.val)) =
      naturalRepresentation Ω (g.val * k.val * g.val⁻¹) w.toAdd.val
    rw [map_mul,map_mul]
    rfl
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointAction

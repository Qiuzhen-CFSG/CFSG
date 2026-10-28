module

public import Theory.Representation.SL3FourNaturalDual.GraphSeparation

/-!
# Graph automorphisms cannot extend a repeated natural SL₃(4) action

Two elementary matrices force every natural-to-dual intertwiner to kill
(1,0,0). Applying this to each matrix entry rules out an injective map
between any nonzero family of natural copies and any family of dual copies.
An ambient graph actor, including its GL₃ correction, would give just such
an isomorphism. The module may have arbitrary positive multiplicity.

This is the linear-algebra obstruction needed after the genuine B.5.1
reduction; it assumes neither an FF classification nor a natural-plus-dual
identification. Source: Aschbacher–Smith, B.5.1(1–3), pp.99–103, used in
13.8.20, printed p.955 of the combined 1 March 2004 manuscript.
-/

@[expose] public noncomputable section
namespace Representation.SL3FourNaturalDual
open Matrix

private theorem intertwiner_kills_first (e : W →ₗ[ZMod 2] W)
    (he : ∀ g w, e (natural g w) = dualCoordinates g (e w)) :
    e (![1, 0, 0] : W) = 0 := by
  let v : W := ![0, 1, 1]
  let b : W := ![1, 0, 0]
  have hnr : natural (root 1) v - v = b := by
    have h := congrArg Prod.fst (root_displacement 1 (v, 0))
    simpa [representation, Representation.prod, v, b] using h
  have hns : natural (secondRoot 1) v - v = b := by
    have h := congrArg Prod.fst (secondRoot_displacement 1 (v, 0))
    simpa [representation, Representation.prod, v, b] using h
  have hdr : dualCoordinates (root 1) (e v) - e v = ![0, 0, e v 0] := by
    have h := congrArg Prod.snd (root_displacement 1 (0, e v))
    simpa [representation, Representation.prod] using h
  have hds : dualCoordinates (secondRoot 1) (e v) - e v = ![0, e v 0, 0] := by
    have h := congrArg Prod.snd (secondRoot_displacement 1 (0, e v))
    simpa [representation, Representation.prod] using h
  have hr : e b = ![0, 0, e v 0] := by rw [← hnr, map_sub, he, hdr]
  have hs : e b = ![0, e v 0, 0] := by rw [← hns, map_sub, he, hds]
  have hz : e v 0 = 0 := by
    simpa using congrArg (fun w : W => w 2) (hr.symm.trans hs)
  rw [hr, hz]
  funext i
  fin_cases i <;> rfl

/-- Even with different multiplicities, a nonzero natural family cannot embed in a dual family. -/
theorem no_injective_repeated_natural_dual_intertwiner
    {ι κ : Type*} [Nonempty ι] (e : (ι → W) →ₗ[ZMod 2] (κ → W))
    (hinj : Function.Injective e)
    (he : ∀ g w, e (fun i => natural g (w i)) = fun j => dualCoordinates g (e w j)) :
    False := by
  classical
  let i : ι := Classical.choice inferInstance
  have hzero : e (Pi.single i (![1, 0, 0] : W)) = 0 := by
    funext j
    let f : W →ₗ[ZMod 2] W :=
      (LinearMap.proj j).comp (e.comp (LinearMap.single (ZMod 2) (fun _ : ι => W) i))
    apply intertwiner_kills_first f
    intro g w
    change e (Pi.single i (natural g w)) j = dualCoordinates g (e (Pi.single i w) j)
    have hs : Pi.single i (natural g w) = fun k => natural g ((Pi.single i w : ι → W) k) := by
      funext k
      by_cases hk : k = i <;> simp [hk]
    rw [hs]
    exact congrFun (he g (Pi.single i w)) j
  have hz : Pi.single i (![1, 0, 0] : W) = 0 := hinj (by simpa using hzero)
  have hc := congrArg (fun w : ι → W => w i 0) hz
  simp at hc

variable {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]

/-- No ambient graph actor extends a nonzero repeated natural action. -/
theorem no_graph_extension_of_repeated_natural
    (ρ : Representation (ZMod 2) D U) (a : SL →* D) (t : D)
    {ι : Type*} [Nonempty ι] (e : U ≃ₗ[ZMod 2] (ι → W))
    (c : GeneralLinearGroup (Fin 3) F)
    (he : ∀ g u i, e (ρ (a g) u) i = natural g (e u i))
    (ht : ∀ g, a g * t = t * a (PSL3.OuterSolvable.linearConjSL F c
      (SpecialLinearGroup.inverseTranspose g))) : False := by
  let C : (ι → W) ≃ₗ[ZMod 2] (ι → W) :=
    LinearEquiv.piCongrRight (fun _ => matrixCoordinates c)
  let T : U ≃ₗ[ZMod 2] U :=
    LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t)
  let s : (ι → W) ≃ₗ[ZMod 2] (ι → W) := C.trans (e.symm.trans (T.trans e))
  have hs (w : ι → W) : e.symm (s w) = ρ t (e.symm (C w)) := by
    dsimp only [s, LinearEquiv.trans_apply]
    rw [e.symm_apply_apply]
    rfl
  have he' (g : SL) (w : ι → W) :
      ρ (a g) (e.symm w) = e.symm (fun i => natural g (w i)) := by
    apply e.injective
    funext i
    rw [he, e.apply_symm_apply, e.apply_symm_apply]
  have hi (g : SL) (w : ι → W) :
      (fun i => natural g (s w i)) = s (fun i => dualCoordinates g (w i)) := by
    apply e.symm.injective
    rw [← he', hs, hs]
    change (ρ (a g) * ρ t) (e.symm (C w)) = _
    rw [← map_mul, ht, map_mul]
    change ρ t (ρ (a (PSL3.OuterSolvable.linearConjSL F c
      (SpecialLinearGroup.inverseTranspose g))) (e.symm (C w))) = _
    rw [he']
    apply congrArg (fun v => ρ t (e.symm v))
    funext i
    exact natural_linearConj c (SpecialLinearGroup.inverseTranspose g) (w i)
  apply no_injective_repeated_natural_dual_intertwiner s.symm.toLinearMap s.symm.injective
  intro g w
  apply s.injective
  change s (s.symm (fun i => natural g (w i))) =
    s (fun i => dualCoordinates g (s.symm w i))
  rw [s.apply_symm_apply, ← hi, s.apply_symm_apply]
end Representation.SL3FourNaturalDual

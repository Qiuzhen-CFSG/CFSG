module
public import Theory.Representation.IrreduciblePairCentralizer
public import Theory.Representation.Quotient

/-!
# Normalizers of two inequivalent simple constituents

An invertible operator inducing one automorphism of the actor either
preserves both simple coordinate summands or exchanges them. Schur's
lemma applied to its four blocks proves this directly. The statement
keeps the two original representations and the actual inducing operator;
it does not assume an ambient normalizer classification.
Source application: Aschbacher--Smith H.4 and Table7.2.1, pp.383--385,698.
-/

public noncomputable section
namespace Representation
variable {k H U W : Type*} [Field k] [Group H]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  (ρ : Representation k H U) (σ : Representation k H W)
  [IsIrreducible ρ] [IsIrreducible σ]

/-- A marked normalizing operator permutes the two inequivalent simple axes. -/
theorem irreducible_pair_normalizer_axes
    (hne : ¬ Nonempty (ρ.Equiv σ)) (α : MulAut H)
    (f : (U × W) ≃ₗ[k] (U × W))
    (hf : ∀ h v, f ((ρ.prod σ) h v) = (ρ.prod σ) (α h) (f v)) :
    ((∀ u, (f (u,0)).2 = 0) ∧ (∀ w, (f (0,w)).1 = 0)) ∨
      ((∀ u, (f (u,0)).1 = 0) ∧ (∀ w, (f (0,w)).2 = 0)) := by
  let : IsIrreducible (ρ.comp α.toMonoidHom) :=
    (irreducible_comp_surjective_iff α.toMonoidHom α.surjective ρ).mpr inferInstance
  let : IsIrreducible (σ.comp α.toMonoidHom) :=
    (irreducible_comp_surjective_iff α.toMonoidHom α.surjective σ).mpr inferInstance
  let a : ρ.IntertwiningMap (ρ.comp α.toMonoidHom) := {
    toLinearMap := (LinearMap.fst _ _ _).comp (f.toLinearMap.comp (LinearMap.inl _ _ _))
    isIntertwining' := by
      intro h
      ext v
      simpa using congrArg Prod.fst (hf h (v,0)) }
  let b : ρ.IntertwiningMap (σ.comp α.toMonoidHom) := {
    toLinearMap := (LinearMap.snd _ _ _).comp (f.toLinearMap.comp (LinearMap.inl _ _ _))
    isIntertwining' := by
      intro h
      ext v
      simpa using congrArg Prod.snd (hf h (v,0)) }
  let c : σ.IntertwiningMap (ρ.comp α.toMonoidHom) := {
    toLinearMap := (LinearMap.fst _ _ _).comp (f.toLinearMap.comp (LinearMap.inr _ _ _))
    isIntertwining' := by
      intro h
      ext v
      simpa using congrArg Prod.fst (hf h (0,v)) }
  let d : σ.IntertwiningMap (σ.comp α.toMonoidHom) := {
    toLinearMap := (LinearMap.snd _ _ _).comp (f.toLinearMap.comp (LinearMap.inr _ _ _))
    isIntertwining' := by
      intro h
      ext v
      simpa using congrArg Prod.snd (hf h (0,v)) }
  have hfirst : a ≠ 0 ∨ b ≠ 0 := by
    by_contra! hh
    let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial ρ
    obtain ⟨u,hu⟩ := exists_ne (0 : U)
    have hz : f (u,0) = 0 := Prod.ext
      (congrArg (fun z : ρ.IntertwiningMap (ρ.comp α.toMonoidHom) => z u) hh.1)
      (congrArg (fun z : ρ.IntertwiningMap (σ.comp α.toMonoidHom) => z u) hh.2)
    exact hu (congrArg Prod.fst (f.injective (hz.trans f.map_zero.symm)))
  rcases hfirst with ha | hb
  · have hai := (IsIrreducible.bijective_or_eq_zero a).resolve_right ha
    have hc : c = 0 := (IsIrreducible.bijective_or_eq_zero c).resolve_left (fun hi =>
      hne ⟨((c.ofBijective hi).trans (a.ofBijective hai).symm).symm⟩)
    have hd : d ≠ 0 := by
      intro hd
      let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
      obtain ⟨w,hw⟩ := exists_ne (0 : W)
      have hz : f (0,w) = 0 := Prod.ext
        (congrArg (fun z : σ.IntertwiningMap (ρ.comp α.toMonoidHom) => z w) hc)
        (congrArg (fun z : σ.IntertwiningMap (σ.comp α.toMonoidHom) => z w) hd)
      exact hw (congrArg Prod.snd (f.injective (hz.trans f.map_zero.symm)))
    have hdi := (IsIrreducible.bijective_or_eq_zero d).resolve_right hd
    have hb : b = 0 := (IsIrreducible.bijective_or_eq_zero b).resolve_left (fun hi =>
      hne ⟨(b.ofBijective hi).trans (d.ofBijective hdi).symm⟩)
    exact Or.inl ⟨fun u => congrArg (fun z : ρ.IntertwiningMap
      (σ.comp α.toMonoidHom) => z u) hb, fun w => congrArg (fun z : σ.IntertwiningMap
      (ρ.comp α.toMonoidHom) => z w) hc⟩
  · have hbi := (IsIrreducible.bijective_or_eq_zero b).resolve_right hb
    have hd : d = 0 := (IsIrreducible.bijective_or_eq_zero d).resolve_left (fun hi =>
      hne ⟨(b.ofBijective hbi).trans (d.ofBijective hi).symm⟩)
    have ha : a = 0 := by
      rcases IsIrreducible.bijective_or_eq_zero a with hi | hz
      · have hc : c = 0 := (IsIrreducible.bijective_or_eq_zero c).resolve_left (fun hj =>
          hne ⟨((c.ofBijective hj).trans (a.ofBijective hi).symm).symm⟩)
        let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
        obtain ⟨w,hw⟩ := exists_ne (0 : W)
        have hz : f (0,w) = 0 := Prod.ext
          (congrArg (fun z : σ.IntertwiningMap (ρ.comp α.toMonoidHom) => z w) hc)
          (congrArg (fun z : σ.IntertwiningMap (σ.comp α.toMonoidHom) => z w) hd)
        exact (hw (congrArg Prod.snd (f.injective (hz.trans f.map_zero.symm)))).elim
      · exact hz
    exact Or.inr ⟨fun u => congrArg (fun z : ρ.IntertwiningMap
      (ρ.comp α.toMonoidHom) => z u) ha, fun w => congrArg (fun z : σ.IntertwiningMap
      (σ.comp α.toMonoidHom) => z w) hd⟩

end Representation

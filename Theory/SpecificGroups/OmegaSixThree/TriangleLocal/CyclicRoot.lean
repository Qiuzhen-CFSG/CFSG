module
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.LocalCompatibility
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.Marks

/-!
# A cyclic-four mark removes the local central twist

In the literal `D₈ × S₄` vertex intersection, the first factor is
characteristic: it is detected by centralizing all elements of cube order.
The only remaining discrepancy that can mix the factors is the central sign
twist. A cyclic-four element centralizing the marked independent `S₄` and
whose square is the marked noncentral reflection excludes that twist. The
result supplies exactly the second-factor condition required by
`compatible_local_equiv`.

The source F.5.5 cyclic subgroup `R₀` is responsible for discharging the
commuting-root premise in the final source consumer. No source normalizer or
automorphism classification is asserted here.

Source: Aschbacher--Smith F.5.5 and F.5.7, printed pp.301--303.
-/

@[expose] public noncomputable section
namespace OmegaSixThree.TriangleLocal.LocalCompatibility
open OmegaSixThree.TriangleLocal

private theorem square_cube : ∀ d : square, d ^ 3 = 1 → d = 1 := by
  decide +kernel

private theorem cube_centralizer : ∀ s : Four,
    (∀ t : Four, t ^ 3 = 1 → s * t = t * s) → s = 1 := by
  decide +kernel

private theorem square_center : ∀ d : square,
    (∀ e : square, d * e = e * d) → d = 1 ∨ d.val = delta := by
  decide +kernel

private theorem square_square_central : ∀ d e : square, d ^ 2 * e = e * d ^ 2 := by
  decide +kernel

private theorem first_factor_characteristic (a : MulAut (square × Four)) (d : square) :
    (a (d,1)).2 = 1 := by
  apply cube_centralizer
  intro s hs
  obtain ⟨p,hp⟩ := a.surjective (1,s)
  have hp3 : p ^ 3 = 1 := by
    apply a.injective
    rw [map_pow,hp,map_one]
    exact Prod.ext (one_pow _) hs
  have hp1 : p.1 = 1 := square_cube p.1 (congrArg Prod.fst hp3)
  have hc : (d,1) * p = p * (d,1) := by
    apply Prod.ext <;> simp [hp1]
  have hh := congrArg (fun q : square × Four => (a q).2) hc
  simpa only [map_mul,Prod.snd_mul,hp] using hh

private theorem first_factor_surjective (a : MulAut (square × Four)) :
    Function.Surjective (fun d : square => (a (d,1)).1) := by
  intro d
  refine ⟨(a.symm (d,1)).1,?_⟩
  have h := a.apply_symm_apply (d,1)
  have hp : a.symm (d,1) = ((a.symm (d,1)).1,1) := by
    apply Prod.ext
    · rfl
    · exact first_factor_characteristic a.symm d
  rw [hp] at h
  exact congrArg Prod.fst h

private theorem second_first_central (a : MulAut (square × Four)) (s : Four) (d : square) :
    (a (1,s)).1 * d = d * (a (1,s)).1 := by
  obtain ⟨e,rfl⟩ := first_factor_surjective a d
  have hc : (1,s) * (e,1) = (e,1) * (1,s) := by simp
  simpa only [map_mul,Prod.fst_mul] using congrArg (fun q : square × Four => (a q).1) hc

private theorem image_reflection_not_central (a : MulAut (square × Four)) :
    ¬ ∀ d : square, (a (reflection,1)).1 * d = d * (a (reflection,1)).1 := by
  intro h
  have hh : a (reflection,1) * a (turn,1) = a (turn,1) * a (reflection,1) := by
    apply Prod.ext
    · exact h _
    · simp only [Prod.snd_mul,first_factor_characteristic,one_mul]
  rw [←map_mul,←map_mul] at hh
  have hf := congrArg Prod.fst (a.injective hh)
  exact (show reflection * turn ≠ turn * reflection by decide +kernel) hf

/-- A cyclic-four root centralizing the image of the independent factor forces
the discrepancy to preserve that factor. -/
theorem second_factor_of_commuting_square_root (a : MulAut (square × Four))
    (r : Four × Four)
    (hsq : r ^ 2 = ((a (reflection,1)).1.val,(a (reflection,1)).2))
    (hc : ∀ s : Four, r * ((a (1,s)).1.val,(a (1,s)).2) =
      ((a (1,s)).1.val,(a (1,s)).2) * r) :
    ∀ p, (a p).1 = 1 ↔ p.1 = 1 := by
  have hs (s : Four) : (a (1,s)).1 = 1 := by
    rcases square_center (a (1,s)).1 (second_first_central a s) with h | h
    · exact h
    · have hr : r.1 ∈ square := by
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        have hh := congrArg Prod.fst (hc s)
        change r.1 * (a (1,s)).1.val = (a (1,s)).1.val * r.1 at hh
        rwa [h] at hh
      have hsq' : (⟨r.1,hr⟩ : square) ^ 2 = (a (reflection,1)).1 :=
        Subtype.ext (congrArg Prod.fst hsq)
      exact False.elim (image_reflection_not_central a (by
        intro d
        rw [←hsq']
        exact square_square_central _ _))
  rintro ⟨d,s⟩
  have hsplit : (d,s) = (d,1) * (1,s) := by simp
  have hfirst : (a (d,s)).1 = (a (d,1)).1 := by
    rw [hsplit,map_mul]
    change (a (d,1)).1 * (a (1,s)).1 = _
    rw [hs,mul_one]
  rw [hfirst]
  constructor
  · intro h
    have hh : a (d,1) = a 1 := by
      rw [map_one]
      exact Prod.ext h (first_factor_characteristic a d)
    exact congrArg Prod.fst (a.injective hh)
  · intro h
    change d = 1 at h
    rw [h]
    exact hs 1

private theorem coordinates (g : vertexLocal) :
    ((vertexProductEquiv g).1.val,(vertexProductEquiv g).2) = productEquiv g.val :=
  Prod.ext (vertexProductEquiv_first g) (vertexProductEquiv_second g)

theorem marked_reflection_eq_graph :
    (vertexProductEquiv.symm (reflection,1)).val = graphElement := by
  apply productEquiv.injective
  rw [←coordinates,vertexProductEquiv.apply_symm_apply,graphElement_image]
  rfl

/-- Transport the cyclic-root condition through the actual marked vertex
coordinates, obtaining preservation of the independent complement. -/
theorem complement_of_commuting_root (a : MulAut vertexLocal) (r : H)
    (hsq : r ^ 2 = (a (vertexProductEquiv.symm (reflection,1))).val)
    (hc : ∀ g : vertexLocal, g.val ∈ complementFactor →
      r * (a g).val = (a g).val * r) :
    ∀ g : vertexLocal, (a g).val ∈ complementFactor ↔ g.val ∈ complementFactor := by
  let b := (vertexProductEquiv.symm.trans a).trans vertexProductEquiv
  have hb (p : square × Four) :
      ((b p).1.val,(b p).2) = productEquiv (a (vertexProductEquiv.symm p)).val :=
    coordinates _
  have hs : (productEquiv r) ^ 2 = ((b (reflection,1)).1.val,(b (reflection,1)).2) := by
    rw [hb,←map_pow,hsq]
  have hh (s : Four) :
      productEquiv r * ((b (1,s)).1.val,(b (1,s)).2) =
      ((b (1,s)).1.val,(b (1,s)).2) * productEquiv r := by
    rw [hb,←map_mul,←map_mul]
    apply congrArg productEquiv
    apply hc
    rw [complement_iff,vertexProductEquiv.apply_symm_apply]
  have hsecond := second_factor_of_commuting_square_root b (productEquiv r) hs hh
  intro g
  rw [complement_iff,complement_iff]
  simpa only [b,MulEquiv.trans_apply,vertexProductEquiv.symm_apply_apply] using
    hsecond (vertexProductEquiv g)

private theorem square_even : ∀ r : Four, Equiv.Perm.sign (r ^ 2) = 1 := by
  decide +kernel

/-- The cyclic-root criterion supplies the missing complement premise to the
marked local extension. -/
theorem extend_vertex_of_commuting_root (a : MulAut vertexLocal) (r : H)
    (hsq : r ^ 2 = (a (vertexProductEquiv.symm (reflection,1))).val)
    (hc : ∀ g : vertexLocal, g.val ∈ complementFactor →
      r * (a g).val = (a g).val * r) :
    ∃ e : MulAut H, ∀ g : vertexLocal, e g.val = (a g).val := by
  apply extend_vertex_automorphism a (complement_of_commuting_root a r hsq hc)
  rw [←hsq,map_pow]
  exact square_even (productEquiv r).1

/-- Correct the actual preliminary local map using a cyclic root in its
target. Both the root equation and centralization use the supplied vertex
restriction, so no complement preservation premise remains. -/
theorem compatible_local_equiv_of_commuting_root {K : Type*} [Group K]
    (L : Subgroup K) (rho : H ≃* K)
    (hrho : ∀ g : H, rho g ∈ L ↔ g ∈ vertexLocal)
    (s : vertexLocal ≃* L) (r : K)
    (hsq : r ^ 2 = (s (vertexProductEquiv.symm (reflection,1))).val)
    (hc : ∀ g : vertexLocal, g.val ∈ complementFactor →
      r * (s g).val = (s g).val * r) :
    ∃ e : H ≃* K,
      (∀ g : vertexLocal, e g.val = (s g).val) ∧
      (∀ g : H, e g ∈ L ↔ g ∈ vertexLocal) := by
  let a := s.trans (restrictVertexEquiv L rho hrho).symm
  have hs : (rho.symm r)^2 = (a (vertexProductEquiv.symm (reflection,1))).val := by
    rw [←map_pow,hsq]
    rfl
  have hh (g : vertexLocal) (hg : g.val ∈ complementFactor) :
      rho.symm r * (a g).val = (a g).val * rho.symm r := by
    change rho.symm r * rho.symm (s g).val = rho.symm (s g).val * rho.symm r
    rw [←map_mul,←map_mul,hc g hg]
  apply compatible_local_equiv L rho hrho s
  · exact complement_of_commuting_root a (rho.symm r) hs hh
  · change Equiv.Perm.sign (productEquiv (a
      (vertexProductEquiv.symm (reflection,1))).val).1 = 1
    rw [←hs,map_pow]
    exact square_even (productEquiv (rho.symm r)).1

end OmegaSixThree.TriangleLocal.LocalCompatibility

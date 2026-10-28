module
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.Vertex
public import Mathlib.Tactic.Group

/-!
# Extending a marked local vertex comparison

The literal vertex intersection in the F.5 triangle group is `D₈ × S₄`,
embedded in `S₄ × S₄`. An automorphism preserving the independent second
factor splits into two factor automorphisms because `S₄` has trivial center.
If its first factor preserves the normal four-group, the dihedral
automorphism is inner and therefore extends to the first `S₄`.

The final adapter corrects a supplied local comparison to agree with a
supplied vertex restriction and preserves the vertex membership relation.
It retains the actual subgroup inclusions. The complement marking remains
an explicit hypothesis: preserving only the normal four-groups does not
exclude a central sign twist.

Source: the marked-map adjustment in Aschbacher--Smith F.5.7(2), printed p.303.
-/

@[expose] public noncomputable section
namespace OmegaSixThree.TriangleLocal.LocalCompatibility
open OmegaSixThree.TriangleLocal

/-- A rotation in the literal square centralizer of `(01)(23)`. -/
def turn : square :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 2 * Equiv.swap 1 3, by decide +kernel⟩

/-- The normal-four-group reflection `(03)(12)`. -/
def reflection : square :=
  ⟨Equiv.swap 0 3 * Equiv.swap 1 2, by decide +kernel⟩

private theorem generator_words : ∀ x : square, ∃ n : Fin 4,
    x = turn ^ n.val ∨ x = reflection * turn ^ n.val := by
  decide +kernel

private theorem generator_images : ∀ a b : square,
    a ^ 4 = 1 ∧ a ^ 2 ≠ 1 ∧ Equiv.Perm.sign b.val = 1 ∧
    b ≠ 1 ∧ b ≠ a ^ 2 → ∃ g : square,
    g * turn * g⁻¹ = a ∧ g * reflection * g⁻¹ = b := by
  decide +kernel

/-- Preserving one noncentral normal-four-group involution makes a square
automorphism inner. -/
theorem square_marked_inner (f : MulAut square)
    (hf : Equiv.Perm.sign (f reflection).val = 1) :
    ∃ g : square, f = MulAut.conj g := by
  have h4 : f turn ^ 4 = 1 := by
    rw [← map_pow, show turn ^ 4 = 1 by decide +kernel, map_one]
  have h2 : f turn ^ 2 ≠ 1 := by
    intro h
    have hh : f (turn ^ 2) = f 1 := by rw [map_pow,map_one]; exact h
    exact (show turn ^ 2 ≠ 1 by decide +kernel) (f.injective hh)
  have hb1 : f reflection ≠ 1 := by
    intro h
    exact (show reflection ≠ 1 by decide +kernel)
      (f.injective (h.trans f.map_one.symm))
  have hba : f reflection ≠ f turn ^ 2 := by
    intro h
    exact (show reflection ≠ turn ^ 2 by decide +kernel)
      (f.injective (h.trans (map_pow f turn 2).symm))
  obtain ⟨g,hga,hgb⟩ := generator_images _ _ ⟨h4,h2,hf,hb1,hba⟩
  refine ⟨g, MulEquiv.ext fun x => ?_⟩
  obtain ⟨n,rfl | rfl⟩ := generator_words x
  · rw [map_pow,map_pow]
    exact congrArg (fun a : square => a ^ n.val) hga.symm
  · rw [map_mul,map_mul,map_pow,map_pow]
    change f reflection * f turn ^ n.val =
      (g * reflection * g⁻¹) * (g * turn * g⁻¹) ^ n.val
    rw [hga,hgb]

private theorem four_centerless : ∀ s : Four,
    (∀ t : Four, s * t = t * s) → s = 1 := by
  decide +kernel

private theorem first_factor_preserved (a : MulAut (square × Four))
    (hsecond : ∀ p, (a p).1 = 1 ↔ p.1 = 1) (d : square) :
    (a (d,1)).2 = 1 := by
  apply four_centerless
  intro t
  obtain ⟨p,hp⟩ := a.surjective (1,t)
  have hp1 : p.1 = 1 := (hsecond p).mp (by rw [hp])
  have hc : (d,1) * p = p * (d,1) := by
    apply Prod.ext <;> simp [hp1]
  have hh := congrArg (fun q : square × Four => (a q).2) hc
  simpa only [map_mul,Prod.snd_mul,hp] using hh

private def firstHom (a : MulAut (square × Four)) : square →* square :=
  (MonoidHom.fst _ _).comp (a.toMonoidHom.comp (MonoidHom.inl _ _))

private def secondHom (a : MulAut (square × Four)) : Four →* Four :=
  (MonoidHom.snd _ _).comp (a.toMonoidHom.comp (MonoidHom.inr _ _))

private theorem firstHom_bijective (a : MulAut (square × Four))
    (hsecond : ∀ p, (a p).1 = 1 ↔ p.1 = 1) :
    Function.Bijective (firstHom a) := by
  constructor
  · intro d e h
    have hh : a (d,1) = a (e,1) := by
      apply Prod.ext
      · exact h
      · rw [first_factor_preserved a hsecond,first_factor_preserved a hsecond]
    exact congrArg Prod.fst (a.injective hh)
  · intro d
    obtain ⟨p,hp⟩ := a.surjective (d,1)
    refine ⟨p.1,?_⟩
    have hsplit : p = (p.1,1) * (1,p.2) := by simp
    have hh := congrArg Prod.fst hp
    rw [hsplit,map_mul] at hh
    change (a (p.1,1)).1 * (a (1,p.2)).1 = d at hh
    rw [(hsecond (1,p.2)).mpr rfl,mul_one] at hh
    exact hh

private theorem secondHom_bijective (a : MulAut (square × Four))
    (hsecond : ∀ p, (a p).1 = 1 ↔ p.1 = 1) :
    Function.Bijective (secondHom a) := by
  constructor
  · intro d e h
    have hh : a (1,d) = a (1,e) := by
      apply Prod.ext
      · rw [(hsecond (1,d)).mpr rfl,(hsecond (1,e)).mpr rfl]
      · exact h
    exact congrArg Prod.snd (a.injective hh)
  · intro d
    obtain ⟨p,hp⟩ := a.surjective (1,d)
    have hp1 : p.1 = 1 := (hsecond p).mp (by rw [hp])
    refine ⟨p.2,?_⟩
    change (a (1,p.2)).2 = d
    simpa only [← hp1] using congrArg Prod.snd hp

/-- Extend the marked product automorphism through the literal first-factor
inclusion `square → S₄`. -/
theorem product_extension (a : MulAut (square × Four))
    (hsecond : ∀ p, (a p).1 = 1 ↔ p.1 = 1)
    (hmark : Equiv.Perm.sign (a (reflection,1)).1.val = 1) :
    ∃ e : MulAut (Four × Four),
      ∀ p : square × Four, e (p.1.val,p.2) = ((a p).1.val,(a p).2) := by
  let f := MulEquiv.ofBijective (firstHom a) (firstHom_bijective a hsecond)
  let k := MulEquiv.ofBijective (secondHom a) (secondHom_bijective a hsecond)
  obtain ⟨g,hg⟩ := square_marked_inner f hmark
  refine ⟨MulEquiv.prodCongr (MulAut.conj g.val) k,?_⟩
  rintro ⟨d,s⟩
  have hsplit : (d,s) = (d,1) * (1,s) := by simp
  have hfirst : (a (d,s)).1 = f d := by
    rw [hsplit,map_mul]
    change (a (d,1)).1 * (a (1,s)).1 = f d
    rw [(hsecond (1,s)).mpr rfl,mul_one]
    rfl
  have hlast : (a (d,s)).2 = k s := by
    rw [hsplit,map_mul]
    change (a (d,1)).2 * (a (1,s)).2 = k s
    rw [first_factor_preserved a hsecond,one_mul]
    rfl
  apply Prod.ext
  · change g.val * d.val * g.val⁻¹ = (a (d,s)).1.val
    rw [hfirst,hg]
    rfl
  · exact hlast.symm

/-- The actual second-factor subgroup in the literal vertex coordinates. -/
theorem complement_iff (g : vertexLocal) :
    g.val ∈ complementFactor ↔ (vertexProductEquiv g).1 = 1 := by
  change (toProduct g.val).1 ∈ (⊥ : Subgroup Four) ∧
    (toProduct g.val).2 ∈ (⊤ : Subgroup Four) ↔ _
  simp only [Subgroup.mem_bot,Subgroup.mem_top,and_true]
  change (productEquiv g.val).1 = 1 ↔ _
  rw [← vertexProductEquiv_first]
  change (vertexProductEquiv g).1.val = (1 : square).val ↔ _
  exact Subtype.coe_inj

/-- An automorphism of the literal vertex intersection extends to its triangle
group when it preserves the independent second factor and the first normal
four-group. The complement hypothesis is essential: a central sign twist
fixes the normal four-groups but does not extend. -/
theorem extend_vertex_automorphism (a : MulAut vertexLocal)
    (hsecond : ∀ g : vertexLocal, (a g).val ∈ complementFactor ↔
      g.val ∈ complementFactor)
    (hmark : Equiv.Perm.sign (productEquiv
      (a (vertexProductEquiv.symm (reflection,1))).val).1 = 1) :
    ∃ e : MulAut H, ∀ g : vertexLocal, e g.val = (a g).val := by
  let b := (vertexProductEquiv.symm.trans a).trans vertexProductEquiv
  have hbsecond : ∀ p, (b p).1 = 1 ↔ p.1 = 1 := by
    intro p
    change (vertexProductEquiv (a (vertexProductEquiv.symm p))).1 = 1 ↔ _
    rw [← complement_iff,hsecond,complement_iff,vertexProductEquiv.apply_symm_apply]
  have hbmark : Equiv.Perm.sign (b (reflection,1)).1.val = 1 := by
    change Equiv.Perm.sign
      (vertexProductEquiv (a (vertexProductEquiv.symm (reflection,1)))).1.val = 1
    rwa [vertexProductEquiv_first]
  obtain ⟨e,he⟩ := product_extension b hbsecond hbmark
  refine ⟨(productEquiv.trans e).trans productEquiv.symm,?_⟩
  intro g
  apply productEquiv.injective
  change productEquiv (productEquiv.symm (e (productEquiv g.val))) = _
  rw [productEquiv.apply_symm_apply]
  have hg : productEquiv g.val = ((vertexProductEquiv g).1.val,
      (vertexProductEquiv g).2) := by
    apply Prod.ext
    · exact (vertexProductEquiv_first g).symm
    · exact (vertexProductEquiv_second g).symm
  rw [hg,he]
  change ((vertexProductEquiv (a (vertexProductEquiv.symm (vertexProductEquiv g)))).1.val,
      (vertexProductEquiv (a (vertexProductEquiv.symm (vertexProductEquiv g)))).2) = _
  rw [vertexProductEquiv.symm_apply_apply]
  apply Prod.ext
  · exact vertexProductEquiv_first (a g)
  · exact vertexProductEquiv_second (a g)

/-- Restriction of a preliminary local comparison, retaining both subgroup
inclusions. -/
def restrictVertexEquiv {K : Type*} [Group K] (L : Subgroup K)
    (r : H ≃* K) (hr : ∀ g : H, r g ∈ L ↔ g ∈ vertexLocal) :
    vertexLocal ≃* L where
  toFun g := ⟨r g.val,(hr g.val).mpr g.property⟩
  invFun g := ⟨r.symm g.val,(hr (r.symm g.val)).mp (by
    rw [r.apply_symm_apply]
    exact g.property)⟩
  left_inv g := Subtype.ext (r.symm_apply_apply g.val)
  right_inv g := Subtype.ext (r.apply_symm_apply g.val)
  map_mul' g h := Subtype.ext (r.map_mul g.val h.val)

/-- Correct a preliminary local comparison to extend a specified vertex map.
The complement and four-group hypotheses concern the actual discrepancy of
the two given maps; they are not assumptions about an arbitrary unmarked
dihedral product. The conclusion supplies agreement and local-vertex
membership for the uniqueness-system similarity. -/
theorem compatible_local_equiv {K : Type*} [Group K] (L : Subgroup K)
    (r : H ≃* K) (hr : ∀ g : H, r g ∈ L ↔ g ∈ vertexLocal)
    (s : vertexLocal ≃* L)
    (hsecond : ∀ g : vertexLocal,
      ((restrictVertexEquiv L r hr).symm (s g)).val ∈ complementFactor ↔
      g.val ∈ complementFactor)
    (hmark : Equiv.Perm.sign (productEquiv
      ((restrictVertexEquiv L r hr).symm
        (s (vertexProductEquiv.symm (reflection,1)))).val).1 = 1) :
    ∃ e : H ≃* K,
      (∀ g : vertexLocal, e g.val = (s g).val) ∧
      (∀ g : H, e g ∈ L ↔ g ∈ vertexLocal) := by
  let a := s.trans (restrictVertexEquiv L r hr).symm
  obtain ⟨e,he⟩ := extend_vertex_automorphism a hsecond hmark
  let q := e.trans r
  have hq (g : vertexLocal) : q g.val = (s g).val := by
    change r (e g.val) = _
    rw [he]
    change r (r.symm (s g).val) = _
    exact r.apply_symm_apply (s g).val
  refine ⟨q,hq,?_⟩
  intro g
  constructor
  · intro hg
    obtain ⟨v,hv⟩ := s.surjective ⟨q g,hg⟩
    have hv' : q v.val = q g := (hq v).trans (congrArg Subtype.val hv)
    exact q.injective hv' ▸ v.property
  · intro hg
    rw [hq ⟨g,hg⟩]
    exact (s ⟨g,hg⟩).property

end OmegaSixThree.TriangleLocal.LocalCompatibility

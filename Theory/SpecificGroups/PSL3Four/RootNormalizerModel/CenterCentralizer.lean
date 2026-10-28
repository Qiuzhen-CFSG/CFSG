module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.CubicGeometry.Centralizer
public import Theory.SpecificGroups.HeisenbergFour.CubicExtension

/-!
# The center centralizer in the explicit root normalizer

The actors fixing every central root coordinate are exactly diagonal(u,u⁻¹).
The actor normal form is supplied by `CubicGeometry.Centralizer`. Evaluating
at the central coordinate 1 forces the product of the diagonal scalars to be
1; the nontrivial field automorphism excludes the graph–field coset.

Consequently the full centralizer has arbitrary root coordinates and precisely
these balanced diagonal actors. We embed the actual Heisenberg cubic extension
by the identity on its three field coordinates and by u ↦ diagonal(u,u⁻¹) on
its unit coordinate. Compatibility with the literal actions proves this is a
homomorphism; identifying its image gives the multiplicative equivalence.
The coordinate and inclusion equations retain the embedding in the normalizer.

This is the intrinsic finite-model calculation behind C_G(E) = RX in
Aschbacher, *Sporadic Groups* (1994), 46.3, 46.14 and the proof of 47.6(1),
printed pp.251, 257–258, 264. Ambient normalizer recognition is a separate input.
-/

@[expose] public section
open Subgroup
namespace Matrix.PSL3Four.RootNormalizerModel.CenterCentralizer
open Cubic
noncomputable section

/-- The actors fixing the root center pointwise are precisely the balanced diagonals. -/
theorem fixes_center_iff (s : actor) :
    (∀ c : F, (s : MulAut Root) ⟨0, 0, c⟩ = ⟨0, 0, c⟩) ↔
      ∃ u : Fˣ, s = torus (u, u⁻¹) := by
  constructor
  · intro h
    obtain ⟨a, ha | ha⟩ := actor_normal_form s
    · have hab : (a.1 : F) * a.2 = 1 := by
        simpa [ha, diagonalHom, diagonal] using congrArg SylowModel.U.c (h 1)
      have hab' : a.1 * a.2 = 1 := Units.ext hab
      have hb : a.2 = a.1⁻¹ := eq_inv_of_mul_eq_one_right hab'
      refine ⟨a.1, Subtype.ext ?_⟩
      change (s : MulAut Root) = diagonalHom (a.1, a.1⁻¹)
      rw [show a = (a.1, a.1⁻¹) from Prod.ext rfl hb] at ha
      exact ha
    · have hab : (a.1 : F) * a.2 = 1 := by
        simpa [ha, diagonalHom, diagonal, graphField, graph, SylowModel.frob] using
          congrArg SylowModel.U.c (h 1)
      obtain ⟨c, hc⟩ := exists_fieldFrobenius_ne
      have hh := congrArg SylowModel.U.c (h c)
      have he : fieldFrobenius c = c := by
        simpa [ha, diagonalHom, diagonal, graphField, graph, SylowModel.frob,
          hab, CharTwo.neg_eq] using hh
      exact (hc he).elim
  · rintro ⟨u, rfl⟩ c
    apply SylowModel.U.ext <;> simp [torus, diagonalHom, diagonal]

/-- Membership in the full center centralizer retains all root coordinates and
requires exactly a balanced diagonal actor. -/
theorem mem_centerCentralizer_iff (g : Model) :
    g ∈ centralizer ((center root).map root.subtype : Set Model) ↔
      ∃ u : Fˣ, g.right = torus (u, u⁻¹) := by
  rw [E_center, ← fixes_center_iff]
  constructor
  · intro hg c
    have hh := (commute_inl_iff g ⟨0, 0, c⟩).mp
      ((hg (eHom (Multiplicative.ofAdd c)) ⟨_, rfl⟩).symm)
    apply mul_left_cancel (a := g.left)
    exact hh.trans ((SylowModel.commute_iff _ _).mpr (by simp)).symm
  · intro hg
    rintro z ⟨c, rfl⟩
    apply Eq.symm
    apply (commute_inl_iff g _).mpr
    change g.left * (g.right : MulAut Root) ⟨0, 0, c.toAdd⟩ = _
    rw [hg]
    exact (SylowModel.commute_iff _ _).mpr (by simp)

/-- The literal identification of the two root-coordinate carriers. -/
def rootCoordinates : HeisenbergFour.Heisenberg HeisenbergFour.Field ≃* Root where
  toFun q := ⟨q.a, q.b, q.c⟩
  invFun q := ⟨q.x, q.y, q.c⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The unit u is the actual actor diagonal(u,u⁻¹). -/
def balancedTorus : Fˣ →* actor := torus.comp
  { toFun := fun u => (u, u⁻¹)
    map_one' := by simp
    map_mul' := fun u v => by simp [mul_comm] }

theorem balancedTorus_injective : Function.Injective balancedTorus := by
  intro u v h
  exact congrArg Prod.fst (diagonalHom_injective (congrArg Subtype.val h))

/-- Compatibility with the exact semidirect action, including the fixed central coordinate. -/
theorem rootCoordinates_action (u : Fˣ)
    (q : HeisenbergFour.Heisenberg HeisenbergFour.Field) :
    rootCoordinates (HeisenbergFour.Heisenberg.action u q) =
      (balancedTorus u : MulAut Root) (rootCoordinates q) := by
  apply SylowModel.U.ext
  · rfl
  · rfl
  · change q.c = ((u : F) * ↑u⁻¹) * q.c
    simp

/-- Embed the Heisenberg cubic extension in the given normalizer model. -/
def inclusion : HeisenbergFour.Model →* Model :=
  SemidirectProduct.map rootCoordinates.toMonoidHom balancedTorus (fun u => by
    apply MonoidHom.ext
    intro q
    exact rootCoordinates_action u q)

@[simp] theorem inclusion_left (q : HeisenbergFour.Model) :
    (inclusion q).left = rootCoordinates q.left := rfl

@[simp] theorem inclusion_right (q : HeisenbergFour.Model) :
    (inclusion q).right = torus (q.right, q.right⁻¹) := rfl

theorem inclusion_injective : Function.Injective inclusion := by
  intro q r h
  apply SemidirectProduct.ext
  · exact rootCoordinates.injective (congrArg SemidirectProduct.left h)
  · exact balancedTorus_injective (congrArg SemidirectProduct.right h)

/-- The embedded Heisenberg extension is the full centralizer, with its literal inclusion. -/
theorem inclusion_range : inclusion.range =
    centralizer ((center root).map root.subtype : Set Model) := by
  ext g
  rw [mem_centerCentralizer_iff]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.right, rfl⟩
  · rintro ⟨u, hu⟩
    refine ⟨⟨rootCoordinates.symm g.left, u⟩, ?_⟩
    exact SemidirectProduct.ext (rootCoordinates.apply_symm_apply _) hu.symm

/-- The center centralizer is multiplicatively the Heisenberg cubic extension. -/
def equivalence : centralizer ((center root).map root.subtype : Set Model) ≃*
    HeisenbergFour.Model :=
  ((MonoidHom.ofInjective inclusion_injective).trans
    (MulEquiv.subgroupCongr inclusion_range)).symm

/-- The inverse equivalence is the previously specified embedding in the ambient model. -/
theorem equivalence_symm_coe (q : HeisenbergFour.Model) :
    (equivalence.symm q : Model) = inclusion q := rfl

/-- The equivalence recovers each original ambient centralizer element. -/
theorem inclusion_equivalence (g : centralizer ((center root).map root.subtype : Set Model)) :
    inclusion (equivalence g) = (g : Model) :=
  congrArg Subtype.val (equivalence.symm_apply_apply g)

/-- The equivalence retains the original three root coordinates. -/
theorem equivalence_left
    (g : centralizer ((center root).map root.subtype : Set Model)) :
    rootCoordinates (equivalence g).left = g.val.left :=
  congrArg SemidirectProduct.left (inclusion_equivalence g)

/-- Its unit coordinate gives exactly the original ambient actor. -/
theorem equivalence_right
    (g : centralizer ((center root).map root.subtype : Set Model)) :
    torus ((equivalence g).right, (equivalence g).right⁻¹) = g.val.right :=
  congrArg SemidirectProduct.right (inclusion_equivalence g)

end
end Matrix.PSL3Four.RootNormalizerModel.CenterCentralizer

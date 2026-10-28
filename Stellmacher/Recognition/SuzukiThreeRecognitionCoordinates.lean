module

public import Stellmacher.Recognition.SuzukiThreeCoordinateData
public import Stellmacher.Recognition.PSU3ThreeProjective
public import Theory.SpecificGroups.UnitaryThree.HermitianMatrices
public import Stellmacher.Recognition.SuzukiThreeSwapCoordinates
public import Stellmacher.Recognition.SuzukiThreeMatrixIdentification
import Mathlib.Tactic.Group

/-!
# Assembly of Hermitian coordinates for Suzuki's degree-28 action

A root-group isomorphism identifies the action domain with the 28 concrete
Hermitian coordinates. An equivariant torus isomorphism supplies the Borel
coordinates. Once a swapping element acts by reciprocal coordinates, Bruhat
decomposition proves that the entire permutation image equals the concrete
unitary permutation model. Faithfulness then gives a group isomorphism.

The swapping-coordinate theorem supplies these coordinates from
`SuzukiThreeLocalStructure`. The matrix-identification theorem identifies the
full concrete permutation model with `PGU3Three`, using an explicit change
from the anti-diagonal Hermitian form to the identity form and coefficient
transport to `GaloisField 3 2`. Composing these identifications proves
`nonempty_equiv_pgu3Three_of_local_structure`.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Sections IV–VI, together with the Bruhat decomposition in Lemma 1.
-/

public section

open MulAction
namespace Stellmacher.Recognition
namespace SuzukiThreeHypotheses
variable {G Ω : Type*} [Group G] [MulAction G Ω]
  {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
  (h : SuzukiThreeHypotheses G Ω a Q)

include h

/-- The small cell has root-torus coordinates. -/
theorem exists_smallCell (b : Ω) (hb : b ≠ a) (x : stabilizer G a) :
    ∃ (u : Q) (k : stabilizer (stabilizer G a) b),
      (x : G) = ((u : stabilizer G a) : G) * ((k : stabilizer G a) : G) := by
  obtain ⟨u, hu, _⟩ :=
    (Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp (h.root_complement b hb)) x
  refine ⟨u, ⟨u.val⁻¹ * x, hu⟩, ?_⟩
  change (x : G) = _ * (_⁻¹ * (x : G))
  group

/-- The roots, torus and any swapping element generate the whole group. -/
theorem eq_top_of_root_torus_swap (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a) (P : Subgroup G)
    (hQ : ∀ q : Q, ((q : stabilizer G a) : G) ∈ P)
    (hK : ∀ k : stabilizer (stabilizer G a) b, ((k : stabilizer G a) : G) ∈ P)
    (ht : t ∈ P) : P = ⊤ := by
  apply top_unique
  intro x _
  by_cases hx : x ∈ stabilizer G a
  · obtain ⟨q, k, he⟩ := h.exists_smallCell b hb ⟨x, hx⟩
    change x = _ at he
    rw [he]
    exact P.mul_mem (hQ q) (hK k)
  · obtain ⟨u, k, v, rfl⟩ := h.exists_bruhat b hb t hta htb x hx
    exact P.mul_mem (P.mul_mem (P.mul_mem (hQ u) (hK k)) ht) (hQ v)

end SuzukiThreeHypotheses

namespace SuzukiThreeCoordinates
variable {G Ω : Type*} [Group G] [MulAction G Ω]
  {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
  {h : SuzukiThreeHypotheses G Ω a Q} {b : Ω} {hb : b ≠ a}
  (c : SuzukiThreeCoordinates h b hb)

/-- The original faithful action transported to the concrete 28 points. -/
noncomputable def permutationHom : G →* Equiv.Perm UnitaryThree.Point :=
  ((h.pointCoordinates b hb c.rootEquiv).permCongrHom.toMonoidHom).comp
    (MulAction.toPermHom G Ω)

private theorem permutationHom_eq (g : G) (s : Equiv.Perm UnitaryThree.Point)
    (hs : ∀ x : Ω, h.pointCoordinates b hb c.rootEquiv (g • x) =
      s (h.pointCoordinates b hb c.rootEquiv x)) : c.permutationHom g = s := by
  apply Equiv.ext
  intro x
  change h.pointCoordinates b hb c.rootEquiv
    (g • (h.pointCoordinates b hb c.rootEquiv).symm x) = s x
  rw [hs, Equiv.apply_symm_apply]

theorem permutationHom_root (q : Q) :
    c.permutationHom ((q : stabilizer G a) : G) = UnitaryThree.rootPerm (c.rootEquiv q) :=
  c.permutationHom_eq _ _ (h.pointCoordinates_root_smul b hb c.rootEquiv q)

theorem permutationHom_torus (k : stabilizer (stabilizer G a) b) :
    c.permutationHom ((k : stabilizer G a) : G) = UnitaryThree.torusPerm (c.torusEquiv k) :=
  c.permutationHom_eq _ _ (c.torus_smul k)

theorem permutationHom_swap : c.permutationHom c.swap = UnitaryThree.swapPerm :=
  c.permutationHom_eq _ _ c.swap_smul

theorem swap_base : c.swap • a = b := by
  apply (h.pointCoordinates b hb c.rootEquiv).injective
  rw [c.swap_smul, h.pointCoordinates_base, h.pointCoordinates_other]
  rfl

theorem swap_other : c.swap • b = a := by
  apply (h.pointCoordinates b hb c.rootEquiv).injective
  rw [c.swap_smul, h.pointCoordinates_other, h.pointCoordinates_base]
  change UnitaryThree.swapFun (some 1) = none
  simp [UnitaryThree.swapFun]

/-- The image is exactly the generated model: both Bruhat cells are covered. -/
theorem permutationHom_range : c.permutationHom.range = UnitaryThree.Model := by
  have hroot (q : UnitaryThree.Root) : UnitaryThree.rootPerm q ∈ UnitaryThree.Model :=
    Subgroup.subset_closure (Or.inl (Or.inl ⟨q, rfl⟩))
  have htorus (r : FiniteField.Nineˣ) : UnitaryThree.torusPerm r ∈ UnitaryThree.Model :=
    Subgroup.subset_closure (Or.inl (Or.inr ⟨r, rfl⟩))
  have hswap : UnitaryThree.swapPerm ∈ UnitaryThree.Model :=
    Subgroup.subset_closure (Or.inr rfl)
  apply le_antisymm
  · have htop : UnitaryThree.Model.comap c.permutationHom = ⊤ := by
      apply h.eq_top_of_root_torus_swap b hb c.swap c.swap_base c.swap_other
      · intro q
        change c.permutationHom ((q : stabilizer G a) : G) ∈ UnitaryThree.Model
        rw [c.permutationHom_root]
        exact hroot _
      · intro k
        change c.permutationHom ((k : stabilizer G a) : G) ∈ UnitaryThree.Model
        rw [c.permutationHom_torus]
        exact htorus _
      · change c.permutationHom c.swap ∈ UnitaryThree.Model
        rw [c.permutationHom_swap]
        exact hswap
    rintro _ ⟨g, rfl⟩
    exact show g ∈ UnitaryThree.Model.comap c.permutationHom from
      htop.symm ▸ Subgroup.mem_top g
  · apply (Subgroup.closure_le _).mpr
    rintro s ((⟨q, rfl⟩ | ⟨r, rfl⟩) | hs)
    · obtain ⟨q, rfl⟩ := c.rootEquiv.surjective q
      exact ⟨((q : stabilizer G a) : G), c.permutationHom_root q⟩
    · obtain ⟨k, rfl⟩ := c.torusEquiv.surjective r
      exact ⟨((k : stabilizer G a) : G), c.permutationHom_torus k⟩
    · have he : s = UnitaryThree.swapPerm := hs
      exact ⟨c.swap, c.permutationHom_swap.trans he.symm⟩

/-- Full coordinate compatibility identifies the entire faithful group. -/
noncomputable def equivModel [FaithfulSMul G Ω] : G ≃* UnitaryThree.Model :=
  (MonoidHom.ofInjective (show Function.Injective c.permutationHom from
    (h.pointCoordinates b hb c.rootEquiv).permCongrHom.injective.comp
      MulAction.toPerm_injective)).trans (MulEquiv.subgroupCongr c.permutationHom_range)

/-- The matrix realization is the final independent input to recognition. -/
noncomputable def equivPGU [FaithfulSMul G Ω]
    (e : UnitaryThree.Model ≃* PGU3Three) : G ≃* PGU3Three :=
  c.equivModel.trans e

end SuzukiThreeCoordinates

namespace SuzukiThreeHypotheses

/-- Suzuki's local structure identifies the entire faithful degree-28 group
with the projective unitary group for the standard identity Hermitian form. -/
theorem nonempty_equiv_pgu3Three_of_local_structure
    {G Ω : Type*} [Group G] [MulAction G Ω] [FaithfulSMul G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q) (b : Ω) (hb : b ≠ a)
    (hlocal : SuzukiThreeLocalStructure G Ω a b Q) :
    Nonempty (G ≃* PGU3Three) := by
  obtain ⟨c⟩ := h.nonempty_coordinates b hb hlocal
  exact ⟨c.equivPGU SuzukiThreeMatrix.modelEquivPGU⟩

end SuzukiThreeHypotheses
end Stellmacher.Recognition

end

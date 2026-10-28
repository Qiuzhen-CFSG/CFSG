module

public import Theory.SpecificGroups.PSp4Three.ReducibleSubgroups.LinearAction
public import Theory.SpecificGroups.PSp4Three.ReducibleSubgroups.SmallFactors
public import Theory.SpecificGroups.PSp4Three.SectionReduction
public import Theory.SpecificGroups.PSp4Three.Transvections
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Reducible subgroups of the concrete PSp₄(3)

Every subgroup whose full inverse image in Sp₄(3) preserves a nonzero proper
subspace of its natural four-dimensional module is solvable.

For a plane W, restriction to W and passage to V/W have solvable images in
GL₂(3), and their common kernel is abelian. This treats both isotropic and
nondegenerate planes. A line W lies in its invariant orthogonal hyperplane;
the resulting flag has factors of dimensions 1, 2, 1, and the same kernel
argument applies twice. A hyperplane gives an invariant line by taking its
orthogonal complement. Finally the projective subgroup is an actual
surjective image of its solvable symplectic inverse image.

No proper-K hypothesis or assumed parabolic classification enters the proof.
This is an intrinsic ingredient for the condition K verification in
Aschbacher–Smith, Theorem 0.1.2(4), `refs/quasithin.pdf`, printed pp.4 and 482;
it does not assert the remaining irreducible-subgroup classification.
-/

noncomputable section
namespace Matrix.PSp4Three
open ReducibleLinear

private abbrev F := ZMod 3
private abbrev V := Vector 2 F

private theorem finrank_vector : Module.finrank F V = 4 := by
  simp [V, Vector, Index]

private def subgroupAction (H : Subgroup (Sp 2 F)) : H →* (V ≃ₗ[F] V) :=
  toLinear.comp H.subtype

private theorem subgroupAction_injective (H : Subgroup (Sp 2 F)) :
    Function.Injective (subgroupAction H) := by
  intro g h he
  apply Subtype.ext
  apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
  intro v
  exact LinearEquiv.congr_fun he v

private theorem invariant_orthogonal (H : Subgroup (Sp 2 F)) (W : Submodule F V)
    (hW : ∀ g : H, ∀ v ∈ W, subgroupAction H g v ∈ W) :
    ∀ g : H, ∀ v ∈ form.orthogonal W, subgroupAction H g v ∈ form.orthogonal W := by
  intro g v hv w hw
  have hi : subgroupAction H g⁻¹ w ∈ W := hW g⁻¹ w hw
  have he := preserves g.val (subgroupAction H g⁻¹ w) v
  change form (subgroupAction H g (subgroupAction H g⁻¹ w))
    (subgroupAction H g v) = form (subgroupAction H g⁻¹ w) v at he
  rw [hv _ hi] at he
  simpa [← LinearEquiv.mul_apply, ← map_mul] using he

private theorem line_le_orthogonal (W : Submodule F V) (hdim : Module.finrank F W = 1) :
    W ≤ form.orthogonal W := by
  obtain ⟨u, hu, hall⟩ := finrank_eq_one_iff'.mp hdim
  intro x hx y hy
  obtain ⟨a, ha⟩ := hall ⟨x, hx⟩
  obtain ⟨b, hb⟩ := hall ⟨y, hy⟩
  have hxa : x = a • u.val := (congrArg Subtype.val ha).symm
  have hyb : y = b • u.val := (congrArg Subtype.val hb).symm
  rw [hxa, hyb]
  simp [map_smul, form_self]

/-- A two-space and its quotient both have solvable general linear group.
This applies to isotropic and nondegenerate planes alike. -/
private theorem isSolvable_plane (H : Subgroup (Sp 2 F)) (W : Submodule F V)
    (hW : ∀ g : H, ∀ v ∈ W, subgroupAction H g v ∈ W)
    (hdim : Module.finrank F W = 2) : Group.IsSolvable H := by
  have hQ : Module.finrank F (V ⧸ W) = 2 := by
    have := W.finrank_quotient_add_finrank
    rw [finrank_vector, hdim] at this
    omega
  let := linearEquiv_isSolvable_finrank_two hdim
  let := linearEquiv_isSolvable_finrank_two hQ
  exact isSolvable_of_subspace (subgroupAction H) W hW (subgroupAction_injective H)

/-- The invariant flag W ≤ W⊥ has successive dimensions 1, 2, 1.
Restriction first to W⊥, then to W inside it, supplies two abelian kernels. -/
private theorem isSolvable_line (H : Subgroup (Sp 2 F)) (W : Submodule F V)
    (hW : ∀ g : H, ∀ v ∈ W, subgroupAction H g v ∈ W)
    (hdim : Module.finrank F W = 1) : Group.IsSolvable H := by
  let P : Submodule F V := form.orthogonal W
  have hP := invariant_orthogonal H W hW
  have hWP : W ≤ P := line_le_orthogonal W hdim
  have hdP : Module.finrank F P = 3 := by
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      finrank_vector, hdim]
  let L : Submodule F P := W.comap P.subtype
  have hdL : Module.finrank F L = 1 := by
    rw [(Submodule.comapSubtypeEquivOfLe hWP).finrank_eq, hdim]
  have hdPL : Module.finrank F (P ⧸ L) = 2 := by
    have := L.finrank_quotient_add_finrank
    rw [hdP, hdL] at this
    omega
  have hdVP : Module.finrank F (V ⧸ P) = 1 := by
    have := P.finrank_quotient_add_finrank
    rw [finrank_vector, hdP] at this
    omega
  let r := restriction (subgroupAction H) P hP
  have hL : ∀ g : r.range, ∀ v ∈ L, g.val v ∈ L := by
    rintro ⟨g, k, rfl⟩ v hv
    exact hW k v.val hv
  let : Group.IsSolvable (L ≃ₗ[F] L) := linearEquiv_isSolvable_finrank_one hdL
  let : Group.IsSolvable ((P ⧸ L) ≃ₗ[F] (P ⧸ L)) :=
    linearEquiv_isSolvable_finrank_two hdPL
  let : Group.IsSolvable r.range :=
    isSolvable_of_subspace r.range.subtype L hL r.range.subtype_injective
  let : Group.IsSolvable ((V ⧸ P) ≃ₗ[F] (V ⧸ P)) :=
    linearEquiv_isSolvable_finrank_one hdVP
  exact isSolvable_of_factors (subgroupAction H) P hP (subgroupAction_injective H)

private theorem subgroup_isSolvable_of_invariantSubspace (H : Subgroup (Sp 2 F))
    (W : Submodule F V) (h0 : W ≠ ⊥) (htop : W ≠ ⊤)
    (hW : ∀ g : H, ∀ v ∈ W, subgroupAction H g v ∈ W) : Group.IsSolvable H := by
  have hpos : 0 < Module.finrank F W := by
    exact Nat.pos_of_ne_zero (fun h => h0 (Submodule.finrank_eq_zero.mp h))
  have hlt : Module.finrank F W < 4 := by
    simpa only [finrank_vector] using Submodule.finrank_lt htop
  have hd : Module.finrank F W = 1 ∨ Module.finrank F W = 2 ∨
      Module.finrank F W = 3 := by omega
  rcases hd with hd | hd | hd
  · exact isSolvable_line H W hW hd
  · exact isSolvable_plane H W hW hd
  · apply isSolvable_line H (form.orthogonal W) (invariant_orthogonal H W hW)
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate, finrank_vector, hd]

/-- Every subgroup whose full symplectic inverse image preserves a proper
nonzero subspace of the natural four-space is solvable. -/
public theorem isSolvable_of_hasInvariantSubspace (U : Subgroup (PSp 2 (ZMod 3)))
    (hU : HasInvariantSubspace U) : Group.IsSolvable U := by
  obtain ⟨W, h0, htop, hW⟩ := hU
  let H : Subgroup (Sp 2 F) := U.comap projection
  let := subgroup_isSolvable_of_invariantSubspace H W h0 htop
    (fun g v hv => hW g.val g.property v hv)
  let p : H →* U :=
    { toFun := fun g => ⟨projection g.val, g.property⟩
      map_one' := by ext; exact map_one projection
      map_mul' := fun g h => by ext; exact map_mul projection g.val h.val }
  apply Group.isSolvable_of_surjective (f := p)
  intro u
  obtain ⟨g, hg⟩ := projection_surjective u.val
  exact ⟨⟨g, by change projection g ∈ U; rw [hg]; exact u.property⟩,
    Subtype.ext hg⟩

end Matrix.PSp4Three

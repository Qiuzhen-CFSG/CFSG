module

public import Theory.Representation.G2OrthogonalCover.SylowFlag

/-!
# The third natural flag space for G₂ in characteristic two

The third space consists of the first three nonscalar octonion coordinates.
Its intrinsic description is the displacement space modulo the marked plane.
Fixed-vector theory in successive quotients then proves uniqueness. This works
over every finite field of characteristic two, retaining the actual derived
actors and the original octonion quotient, not only the binary model.

Source: Aschbacher--Smith, opening §11.1, printed pp.760--761.
-/

@[expose] public noncomputable section
namespace Atlas.G2.Natural.OrthogonalCover.SylowFlag
open Subgroup Representation Representation.OneCohomology
open Atlas.G2.Restricted.NaturalCoordinates
variable (F : Type*) [Field F] [CharP F 2]

/-- The literal first three nonscalar coordinates in the octonion quotient. -/
def naturalThreeSpace : Submodule F (Natural.Space F) where
  carrier := {x | coord F x 3 = 0 ∧ coord F x 4 = 0 ∧ coord F x 5 = 0}
  zero_mem' := by simp
  add_mem' := by rintro x y ⟨h3,h4,h5⟩ ⟨j3,j4,j5⟩; simp only [Set.mem_ofPred_eq, map_add, Pi.add_apply, h3,h4,h5,j3,j4,j5, add_zero, and_self]
  smul_mem' := by rintro a x ⟨h3,h4,h5⟩; simp only [Set.mem_ofPred_eq, map_smul, Pi.smul_apply, h3,h4,h5, smul_zero, and_self]

@[simp] theorem mem_naturalThreeSpace (x : Natural.Space F) :
    x ∈ naturalThreeSpace F ↔ coord F x 3 = 0 ∧ coord F x 4 = 0 ∧ coord F x 5 = 0 := Iff.rfl

/-- Coordinates identify the third space with the field three-space. -/
def naturalThreeSpaceEquiv : naturalThreeSpace F ≃ₗ[F] (Fin 3 → F) where
  toFun x := ![coord F x.val 0, coord F x.val 1, coord F x.val 2]
  invFun a := ⟨(coord F).symm ![a 0,a 1,a 2,0,0,0], by simp⟩
  left_inv x := by
    apply Subtype.ext
    apply (coord F).injective
    obtain ⟨h3,h4,h5⟩ := x.property
    ext i
    fin_cases i <;> simp [h3,h4,h5]
  right_inv a := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' a x := by ext i; fin_cases i <;> simp

theorem naturalThreeSpace_finrank : Module.finrank F (naturalThreeSpace F) = 3 := by
  rw [(naturalThreeSpaceEquiv F).finrank_eq]
  simp

theorem naturalPlane_le_naturalThreeSpace : naturalPlane F ≤ naturalThreeSpace F := by
  intro x hx
  obtain ⟨a,b,he⟩ := (mem_naturalPlane F x).mp hx
  simp [mem_naturalThreeSpace,he]

private theorem unipotent_three (t : Fin 6 → F) (a b c : F) :
    Restricted.NaturalCoordinates.action F (unipotentProduct t) ![a,b,c,0,0,0] =
      ![a + t 5 * b + t 3 * c, b + t 4 * c,c,0,0,0] := by
  simp only [unipotentProduct,map_mul,Module.End.mul_apply]
  rw [action_rootF]
  simp only [Matrix.cons_val, mul_zero, add_zero]
  rw [action_rootE]
  simp only [Matrix.cons_val, mul_zero, add_zero]
  rw [action_rootD]
  simp only [Matrix.cons_val, mul_zero, add_zero]
  rw [action_rootC]
  simp only [Matrix.cons_val, mul_zero, add_zero]
  rw [action_rootB]
  simp only [Matrix.cons_val, mul_zero, add_zero]
  rw [action_rootA]
  simp only [Matrix.cons_val, mul_zero, add_zero]

/-- All positive roots move the third space only into the marked plane. -/
theorem unipotent_displacement_mem_plane (g : Model F) (hg : g ∈ unipotent)
    (x : Natural.Space F) (hx : x ∈ naturalThreeSpace F) :
    Natural.action F g x - x ∈ naturalPlane F := by
  rw [unipotent_eq_range] at hg
  obtain ⟨t,rfl⟩ := hg
  obtain ⟨h3,h4,h5⟩ := hx
  have hxcoord : coord F x = ![coord F x 0,coord F x 1,coord F x 2,0,0,0] := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact h3
    · exact h4
    · exact h5
  apply (mem_naturalPlane F _).mpr
  refine ⟨t 5 * coord F x 1 + t 3 * coord F x 2,t 4 * coord F x 2,?_⟩
  rw [map_sub]
  have hc : coord F (Natural.action F (unipotentProduct t) x) =
      Restricted.NaturalCoordinates.action F (unipotentProduct t) (coord F x) :=
    LinearMap.congr_fun ((repEquiv F).isIntertwining' (unipotentProduct t)) x
  rw [hc]
  conv_lhs => rw [hxcoord,unipotent_three]
  ext i
  fin_cases i <;> simp
  ring

/-- Displacements modulo the plane intrinsically characterize the third space. -/
theorem displacement_mem_plane_iff (x : Natural.Space F) :
    (∀ g : U F, derivedAction F g.val x - x ∈ naturalPlane F) ↔
      x ∈ naturalThreeSpace F := by
  constructor
  · intro hx
    obtain ⟨a,b,he⟩ := (mem_naturalPlane F _).mp (hx (actorE F))
    obtain ⟨c,d,hh⟩ := (mem_naturalPlane F _).mp (hx (actorH F))
    rw [displacementE] at he
    rw [displacementH] at hh
    have h4 : coord F x 4 = 0 := congrFun he 3
    have h5 : coord F x 5 = 0 := congrFun hh 4
    have h3 : coord F x 3 = 0 := by simpa [h5] using congrFun hh 2
    exact ⟨h3,h4,h5⟩
  · intro hx g
    exact unipotent_displacement_mem_plane F g.val.val g.property x hx

theorem naturalThreeSpace_invariant (g : U F) :
    naturalThreeSpace F ≤ (naturalThreeSpace F).comap (derivedAction F g.val) := by
  intro x hx
  change derivedAction F g.val x ∈ naturalThreeSpace F
  have hd := naturalPlane_le_naturalThreeSpace F
    ((displacement_mem_plane_iff F x).mpr hx g)
  simpa only [sub_add_cancel] using (naturalThreeSpace F).add_mem hd hx

private theorem fixed_vector {J W : Type*} [Group J] [Finite J]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] [Nontrivial W]
    (hp : IsPGroup 2 J) (ρ : Representation F J W) :
    ∃ w : W, w ≠ 0 ∧ ∀ j : J, ρ j w = w := by
  exact pGroup_fix_nonzero_vector (by rw [ringChar.eq F 2]; decide)
    (by simpa only [ringChar.eq F 2] using hp) ρ

/-- Every invariant space of dimension at least two contains the marked plane. -/
theorem naturalPlane_le_of_invariant [Finite F] (W : Submodule F (Natural.Space F))
    (hW : ∀ g : U F, W ≤ W.comap (derivedAction F g.val))
    (hdim : 2 ≤ Module.finrank F W) : naturalPlane F ≤ W := by
  have hNW : N1 F ≤ W := N1_le_of_invariant F W hW (by
    intro he
    rw [he,finrank_bot] at hdim
    omega)
  let σ := Representation.subrepresentation ((derivedAction F).comp (U F).subtype) W hW
  let N : Submodule F W := (N1 F).comap W.subtype
  have hN (g : U F) : N ≤ N.comap (σ g) := fun x hx => N1_invariant F g hx
  have hdN : Module.finrank F N = 1 :=
    (Submodule.comapSubtypeEquivOfLe hNW).finrank_eq.trans (N1_finrank F)
  have hdQ : 0 < Module.finrank F (W ⧸ N) := by
    have hh := N.finrank_quotient_add_finrank
    omega
  let : Nontrivial (W ⧸ N) := Module.nontrivial_of_finrank_pos hdQ
  obtain ⟨q,hq,hqfixed⟩ := fixed_vector F (U_isTwoGroup F) (Representation.quotient σ N hN)
  obtain ⟨x,rfl⟩ := N.mkQ_surjective q
  have hxN : x.val ∉ N1 F := by
    intro hx
    exact hq ((Submodule.Quotient.mk_eq_zero N).mpr hx)
  have hxP : x.val ∈ naturalPlane F := by
    apply (displacement_mem_N1_iff F x.val).mp
    intro g
    have hh := hqfixed g
    change N.mkQ (σ g x) = N.mkQ x at hh
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hh
    exact hh
  have hNB : N1 F ≤ W ⊓ naturalPlane F := le_inf hNW (N1_le_naturalPlane F)
  have hlt : N1 F < W ⊓ naturalPlane F := lt_of_le_of_ne hNB (by
    intro he
    apply hxN
    rw [he]
    exact ⟨x.property,hxP⟩)
  have hdB : Module.finrank F (W ⊓ naturalPlane F : Submodule F (Natural.Space F)) = 2 := by
    have hl := Submodule.finrank_lt_finrank_of_lt hlt
    have hh := Submodule.finrank_mono (show W ⊓ naturalPlane F ≤ naturalPlane F from inf_le_right)
    rw [N1_finrank] at hl
    rw [naturalPlane_finrank] at hh
    omega
  have he : W ⊓ naturalPlane F = naturalPlane F := Submodule.eq_of_le_of_finrank_eq inf_le_right
    (hdB.trans (naturalPlane_finrank F).symm)
  exact he ▸ (show W ⊓ naturalPlane F ≤ W from inf_le_left)

private theorem one_dimensional_trivial {J W : Type*} [Group J] [Finite J]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (hp : IsPGroup 2 J) (ρ : Representation F J W) (hdim : Module.finrank F W = 1) :
    ∀ j w, ρ j w = w := by
  let : Nontrivial W := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank F W)
  obtain ⟨x,hx,hfix⟩ := fixed_vector F hp ρ
  intro j w
  obtain ⟨a,rfl⟩ := (finrank_eq_one_iff_of_nonzero' x hx).mp hdim w
  rw [map_smul,hfix]

/-- The actual derived positive-root Sylow has a unique invariant three-space,
uniformly over finite fields of characteristic two. -/
theorem invariant_three_unique [Finite F] (W : Submodule F (Natural.Space F))
    (hW : ∀ g : U F, W ≤ W.comap (derivedAction F g.val))
    (hdim : Module.finrank F W = 3) : W = naturalThreeSpace F := by
  have hPW : naturalPlane F ≤ W := naturalPlane_le_of_invariant F W hW (by omega)
  let σ := Representation.subrepresentation ((derivedAction F).comp (U F).subtype) W hW
  let P : Submodule F W := (naturalPlane F).comap W.subtype
  have hP (g : U F) : P ≤ P.comap (σ g) := fun x hx => naturalPlane_invariant F g hx
  have hdP : Module.finrank F P = 2 :=
    (Submodule.comapSubtypeEquivOfLe hPW).finrank_eq.trans (naturalPlane_finrank F)
  have hdQ : Module.finrank F (W ⧸ P) = 1 := by
    have hh := P.finrank_quotient_add_finrank
    omega
  have htriv := one_dimensional_trivial F (U_isTwoGroup F) (Representation.quotient σ P hP) hdQ
  apply Submodule.eq_of_le_of_finrank_eq _ (hdim.trans (naturalThreeSpace_finrank F).symm)
  intro x hx
  apply (displacement_mem_plane_iff F x).mp
  intro g
  have hh := htriv g (P.mkQ ⟨x,hx⟩)
  change P.mkQ (σ g ⟨x,hx⟩) = P.mkQ ⟨x,hx⟩ at hh
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hh
  exact hh

end Atlas.G2.Natural.OrthogonalCover.SylowFlag

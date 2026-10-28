module
public import Theory.Representation.FirstCohomologyDuality.Indecomposable
public import Theory.Representation.SL2NaturalFirstCohomology
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual

/-!
# The universal binary central cover of the natural SL₂(4) module

The dual of the F₄-valued cocycle space gives a three-dimensional F₄-cover
of the natural plane. Restriction of scalars preserves commutator generation.
The natural binary module is self-dual and has first-cohomology dimension two,
so this cover has the full binary universal-cover dimension. Comparing the
surjections from the abstract universal cover proves its universal property,
including compatibility with the original projection.

In particular every indecomposable central extension of the natural module
is a quotient of this specific F₄-linear cover, and its fixed kernel has binary
dimension at most two. No six-dimensional structure theorem for a different
group section is assumed or asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Remark I.1.5,
Lemma I.1.6(2), and Remark 14.7.64, printed pp.408 and 1069. The actor here is
K* = SL₂(4); extending its action to H* and the orthogonal four-space are
separate constructions.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourCentralCover
open Representation.OneCohomology SL2FourNatural

private theorem commutator_restrict_eq_top
    {k E D W : Type*} [Field k] [Field E] [Algebra k E] [Group D]
    [AddCommGroup W] [Module E W] [Module k W] [IsScalarTower k E W]
    (ρ : Representation E D W) (hρ : Coinvariants.ker ρ = ⊤) :
    Coinvariants.ker (restrictScalars (k := k) ρ) = ⊤ := by
  let C := Coinvariants.ker (restrictScalars (k := k) ρ)
  have hs (a : E) (w : W) (hw : w ∈ C) : a • w ∈ C := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨g, v⟩, rfl⟩ := hw
      change a • (ρ g v - v) ∈ C
      rw [smul_sub, ← map_smul]
      exact Coinvariants.sub_mem_ker (ρ := restrictScalars (k := k) ρ) g (a • v)
    | zero => simp only [smul_zero]; exact C.zero_mem
    | add x y _ _ hx hy => simpa only [smul_add] using C.add_mem hx hy
    | smul r x _ hx => simpa only [smul_comm a r] using C.smul_mem r hx
  let CE : Submodule E W := {
    carrier := C
    zero_mem' := C.zero_mem
    add_mem' := C.add_mem
    smul_mem' := hs }
  have hCE : Coinvariants.ker ρ ≤ CE := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := restrictScalars (k := k) ρ) g v
  apply top_unique
  intro w _
  exact hCE (hρ ▸ Submodule.mem_top)

/-- The determinant pairing over F₄. -/
def fieldPairing : V →ₗ[F] Module.Dual F V where
  toFun v := {
    toFun w := wedge v w
    map_add' w x := by simp only [wedge, Pi.add_apply]; ring
    map_smul' c w := by simp only [wedge, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_add' v w := by
    apply LinearMap.ext
    intro x
    change wedge (v + w) x = wedge v x + wedge w x
    simp only [wedge, Pi.add_apply]; ring
  map_smul' c v := by
    apply LinearMap.ext
    intro w
    change wedge (c • v) w = c * wedge v w
    simp only [wedge, Pi.smul_apply, smul_eq_mul]; ring

theorem fieldPairing_injective : Function.Injective fieldPairing := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  have h0 := congrArg (fun f : Module.Dual F V => f ![0, 1]) hv
  have h1 := congrArg (fun f : Module.Dual F V => f ![1, 0]) hv
  change v = 0
  funext i
  fin_cases i
  · simpa [fieldPairing, wedge] using h0
  · simpa [fieldPairing, wedge] using h1

/-- The determinant form identifies the F₄-linear dual with the natural plane. -/
def fieldSelfDual : V ≃ₗ[F] Module.Dual F V :=
  LinearEquiv.ofBijective fieldPairing ⟨fieldPairing_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := F) (V := V)).symm).mp fieldPairing_injective⟩

abbrev natural : Representation F SL V := specialLinearNatural 2

/-- The same group element is retained by the self-duality. -/
theorem fieldSelfDual_equivariant (g : SL) (v : V) :
    fieldSelfDual (natural g v) = natural.dual g (fieldSelfDual v) := by
  apply LinearMap.ext
  intro w
  change wedge (action g v) w = wedge v (action g⁻¹ w)
  have h := wedge_action g v (action g⁻¹ w)
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
  exact h

private theorem natural_fixed : fixed natural = ⊥ := by
  apply bot_unique
  intro v hv
  exact natural_fixed_eq_zero v hv

/-- The covering space carries a genuine F₄-vector space structure. -/
abbrev Space := Module.Dual F (cocycles natural)

/-- The three-dimensional F₄ covering action. -/
abbrev fieldAction : Representation F SL Space := (universalAction natural).dual

/-- Its projection onto the original natural plane, using determinant self-duality. -/
def fieldProjection : fieldAction.IntertwiningMap natural :=
  (fieldSelfDual.symm.toLinearMap.comp (universalDualProjection natural).toLinearMap)
    |>.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g w
      apply fieldSelfDual.injective
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        fieldSelfDual_equivariant]
      exact LinearMap.congr_fun ((universalDualProjection natural).isIntertwining' g) w)

/-- The field-linear covering has fixed kernel and is generated by commutators. -/
theorem fieldProjection_isCover : IsCover fieldProjection := by
  have h := universalDualProjection_isCover natural natural_fixed
  refine ⟨fieldSelfDual.symm.surjective.comp h.1, ?_, h.2.2⟩
  intro v hv
  apply h.2.1
  change fieldSelfDual.symm (universalDualProjection natural v) = 0 at hv
  exact fieldSelfDual.symm.injective (hv.trans (map_zero _).symm)

/-- This cover has dimension three over F₄. -/
theorem field_finrank : Module.finrank F Space = 3 := by
  have h := (universalDualProjection natural).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
    (universalDualProjection_isCover natural natural_fixed).1,
    finrank_top, Subspace.dual_finrank_eq,
    finrank_ker_universalDualProjection, SL2NaturalH1.finrank_eq_one] at h
  · simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using h.symm
  · rw [Nat.card_eq_fintype_card, card_field]; decide

/-- Restriction to the binary ground field. -/
abbrev binaryAction : Representation (ZMod 2) SL Space := restrictScalars fieldAction

/-- The binary cover projection uses exactly the same natural action as Ru2. -/
def projection : binaryAction.IntertwiningMap naturalRepresentation :=
  (fieldProjection.toLinearMap.restrictScalars (ZMod 2))
    |>.intertwiningMap_of_isIntertwiningMap _ _ (fun g v =>
      LinearMap.congr_fun (fieldProjection.isIntertwining' g) v)

/-- Scalar restriction preserves the covering property. -/
theorem projection_isCover : IsCover projection :=
  ⟨fieldProjection_isCover.1, fieldProjection_isCover.2.1,
    commutator_restrict_eq_top fieldAction fieldProjection_isCover.2.2⟩

/-- The universal covering space has binary dimension six. -/
theorem binary_finrank : Module.finrank (ZMod 2) Space = 6 := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F Space, field_finrank,
    SL2NaturalH1.field_finrank 2 (by rw [Nat.card_eq_fintype_card, card_field]; rfl)]

/-- The contragredient natural binary module has first-cohomology dimension two. -/
theorem natural_dual_H1_finrank :
    Module.finrank (ZMod 2) (H1 naturalRepresentation.dual) = 2 := by
  let e := H1Congr naturalRepresentation naturalRepresentation.dual (MulEquiv.refl SL)
    selfDual (fun g v => selfDual_equivariant g v)
  rw [← e.finrank_eq]
  have he : naturalRepresentation = restrictScalars (k := ZMod 2) natural := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    rfl
  rw [he]
  exact SL2NaturalH1.finrank_restrict_eq 2 (by decide)
    (by rw [Nat.card_eq_fintype_card, card_field]; rfl)

private theorem natural_generated : Coinvariants.ker naturalRepresentation = ⊤ := by
  apply (fixed_dual_eq_bot_iff naturalRepresentation).mp
  apply bot_unique
  intro v hv
  obtain ⟨w, rfl⟩ := selfDual.surjective v
  have hw : w = 0 := natural_fixed_eq_zero w (by
    intro g
    apply selfDual.injective
    exact (selfDual_equivariant g w).trans (hv g))
  simp [hw]

/-- Every indecomposable central extension of the natural module is a cover. -/
theorem isCover_of_natural_indecomposable
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) SL W}
    (p : σ.IntertwiningMap naturalRepresentation) (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed σ)
    (hi : ∀ A B : Submodule (ZMod 2) W,
      (∀ g v, v ∈ A → σ g v ∈ A) →
      (∀ g v, v ∈ B → σ g v ∈ B) → IsCompl A B → A = ⊥ ∨ B = ⊥) :
    IsCover p := isCover_of_indecomposable p hp hk natural_generated hi

/-- Every finite-dimensional binary cover is a quotient of this F₄-linear cover,
compatibly with its actual projection onto the natural plane. -/
theorem exists_quotient
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) SL W}
    (p : σ.IntertwiningMap naturalRepresentation) (hp : IsCover p) :
    ∃ q : binaryAction.IntertwiningMap σ, Function.Surjective q ∧
      ∀ w, p (q w) = projection w := by
  let : FiniteDimensional (ZMod 2) (Module.Dual (ZMod 2)
      (cocycles naturalRepresentation.dual)) := Subspace.instModuleDualFiniteDimensional
  obtain ⟨b, hb, hbp⟩ := exists_universalCover_quotient projection projection_isCover
  obtain ⟨c, hc, hcp⟩ := exists_universalCover_quotient p hp
  have hdim := (universalCoverProjection naturalRepresentation).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
    (universalCoverProjection_isCover naturalRepresentation natural_generated).1,
    finrank_top, finrank_ker_universalCoverProjection,
    natural_dual_H1_finrank, finrank_vector] at hdim
  have hd : Module.finrank (ZMod 2) (Module.Dual (ZMod 2)
      (cocycles naturalRepresentation.dual)) = Module.finrank (ZMod 2) Space :=
    hdim.symm.trans binary_finrank.symm
  let B := LinearEquiv.ofBijective b.toLinearMap
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hb, hb⟩
  let q := c.toLinearMap.comp B.symm.toLinearMap
  have hq : ∀ g w, q (binaryAction g w) = σ g (q w) := by
    intro g w
    have he : B.symm (binaryAction g w) =
        (universalAction naturalRepresentation.dual).dual g (B.symm w) := by
      apply B.injective
      rw [B.apply_symm_apply]
      change binaryAction g w = b ((universalAction naturalRepresentation.dual).dual g (B.symm w))
      rw [b.isIntertwining]
      exact congrArg (binaryAction g) (B.apply_symm_apply w).symm
    change c (B.symm (binaryAction g w)) = σ g (c (B.symm w))
    rw [he, c.isIntertwining]
  refine ⟨q.intertwiningMap_of_isIntertwiningMap _ _ hq, hc.comp B.symm.surjective, ?_⟩
  intro w
  change p (c (B.symm w)) = projection w
  rw [hcp, ← hbp]
  exact congrArg projection (B.apply_symm_apply w)

/-- The fixed kernel is the whole invariant space of any such extension. -/
theorem invariants_eq_kernel
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) SL W}
    (p : σ.IntertwiningMap naturalRepresentation)
    (hk : p.toLinearMap.ker ≤ fixed σ) :
    σ.invariants = p.toLinearMap.ker := by
  apply le_antisymm
  · intro w hw
    apply natural_fixed_eq_zero
    intro g
    change naturalRepresentation g (p w) = p w
    rw [← p.isIntertwining, hw]
  · exact hk

/-- The dimension bound on the central kernel used in 14.7.69--70. -/
theorem kernel_finrank_le_two
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) SL W}
    (p : σ.IntertwiningMap naturalRepresentation) (hp : IsCover p) :
    Module.finrank (ZMod 2) p.toLinearMap.ker ≤ 2 := by
  simpa only [natural_dual_H1_finrank] using finrank_ker_le_H1_of_cover p hp

/-- The natural module and its perfect central covers have dimensions four through six. -/
theorem finrank_bounds
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) SL W}
    (p : σ.IntertwiningMap naturalRepresentation) (hp : IsCover p) :
    4 ≤ Module.finrank (ZMod 2) W ∧ Module.finrank (ZMod 2) W ≤ 6 := by
  have h := p.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hp.1, finrank_top, finrank_vector] at h
  have hk := kernel_finrank_le_two p hp
  omega

end Representation.SL2FourCentralCover

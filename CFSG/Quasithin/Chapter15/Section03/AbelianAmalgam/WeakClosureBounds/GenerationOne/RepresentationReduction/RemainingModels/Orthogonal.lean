module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.RemainingModels.Matrix
public import Theory.Representation.OrthogonalNatural

/-!
# The Ω₄⁺ Borel on the split quadratic module

Work directly with Q(x,y)=x₀y₀+x₁y₁ and the Siegel-generated Omega carrier.
The two opposite roots along (e₀,f₁) and (e₁,f₀) give a Weyl word; the product
of two such words is diag(a,a⁻¹,a⁻¹,a). Thus the torus membership is proved in
the genuine Omega group, without a higher-rank identification. This element
stabilizes the singular line Fe₀ and plane Fe₀+Fe₁, and a≠1 eliminates every
fixed coordinate. Central-quotient transport does not require a split extension.

Source: Aschbacher–Smith, 15.3.65(iii), printed p.1152 and F.9.18(5),
printed pp.325–326. The form and Siegel construction come from OrthogonalNatural.
-/

public noncomputable section
open ClassicalOrthogonal Theory.AlgebraicGroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.RemainingModels

variable {F : Type*} [Field F]

private def omegaRoot (i j : Fin 2) (hij : i ≠ j) (a : F) : OmegaPlus 2 F :=
  ⟨siegelElement (formD 2 F) (e i) (a • f j)
    (by simp [ClassicalOrthogonal.e, formD_apply, Pi.single_apply])
    (by simp [-QuadraticMap.polarBilin_apply_apply, polarD_f, ClassicalOrthogonal.e, hij]),
    siegelElement_mem _ _ _ _ _⟩

private theorem omegaRoot_apply (i j : Fin 2) (hij : i ≠ j) (a : F) (v : VectorD 2 F) :
    (omegaRoot i j hij a).val.val v =
      v + (a * v (.inl j)) • e i - v (.inr i) • (a • f j) := by
  change Quadratic.siegel (formD 2 F) (e i) (a • f j) v = _
  have hQ : formD 2 F (a • f j) = 0 := by
    simp [ClassicalOrthogonal.f, formD_apply, Pi.single_apply]
  simp only [Quadratic.siegel, hQ, map_smul, polarD_e, polarD_f,
    zero_mul, zero_smul, sub_zero, smul_eq_mul]

private def omegaWeylWord (a : F) : OmegaPlus 2 F :=
  omegaRoot 0 1 (by decide) a * omegaRoot 1 0 (by decide) (-a⁻¹) *
    omegaRoot 0 1 (by decide) a

def omegaTorus (a : Fˣ) : OmegaPlus 2 F :=
  omegaWeylWord (a : F) * omegaWeylWord (-1)

private theorem omegaWeylWord_apply (a : F) (ha : a ≠ 0) (v : VectorD 2 F) :
    (omegaWeylWord a).val.val v =
      Sum.elim ![a * v (.inl 1), -a⁻¹ * v (.inl 0)]
        ![a⁻¹ * v (.inr 1), -a * v (.inr 0)] := by
  change (omegaRoot 0 1 (by decide) a).val.val
    ((omegaRoot 1 0 (by decide) (-a⁻¹)).val.val
      ((omegaRoot 0 1 (by decide) a).val.val v)) = _
  simp only [omegaRoot_apply]
  ext k
  rcases k with k | k <;> fin_cases k <;>
    simp [ClassicalOrthogonal.e, ClassicalOrthogonal.f,
      smul_eq_mul] <;> field_simp <;> ring

theorem omegaTorus_apply (a : Fˣ) (v : VectorD 2 F) :
    (omegaTorus a).val.val v =
      Sum.elim ![(a : F) * v (.inl 0), (a : F)⁻¹ * v (.inl 1)]
        ![(a : F)⁻¹ * v (.inr 0), (a : F) * v (.inr 1)] := by
  change (omegaWeylWord (a : F)).val.val ((omegaWeylWord (-1 : F)).val.val v) = _
  rw [omegaWeylWord_apply _ a.ne_zero, omegaWeylWord_apply _ (neg_ne_zero.mpr one_ne_zero)]
  ext k
  rcases k with k | k <;> fin_cases k <;> simp

/-- The first singular line in the ordered hyperbolic coordinates. -/
@[expose] def omegaLine : Submodule F (VectorD 2 F) :=
  (LinearMap.proj (.inl 1)).ker ⊓
    ((LinearMap.proj (.inr 0)).ker ⊓ (LinearMap.proj (.inr 1)).ker)

/-- The maximal singular plane spanned by the first two hyperbolic vectors. -/
@[expose] def omegaPlane : Submodule F (VectorD 2 F) :=
  (LinearMap.proj (.inr 0)).ker ⊓ (LinearMap.proj (.inr 1)).ker

variable [Algebra (ZMod 2) F]

/-- Restriction of the defining quadratic-isometry action, with binary scalars. -/
@[expose] def omegaNatural := restrictScalars (k := ZMod 2) (subgroupNatural (OmegaPlus 2 F))

/-- The stabilizer in Ω₄⁺ of the standard singular line–plane flag. -/
@[expose] def omegaBorel : Subgroup (OmegaPlus 2 F) :=
  subspaceStabilizer omegaNatural ((omegaLine (F := F)).restrictScalars (ZMod 2)) ⊓
    subspaceStabilizer omegaNatural ((omegaPlane (F := F)).restrictScalars (ZMod 2))

theorem omegaTorus_mem_borel (a : Fˣ) : omegaTorus a ∈ omegaBorel := by
  constructor
  · intro v
    change (omegaTorus a).val.val v ∈ omegaLine ↔ v ∈ omegaLine
    rw [omegaTorus_apply]
    simp [omegaLine, a.ne_zero]
  · intro v
    change (omegaTorus a).val.val v ∈ omegaPlane ↔ v ∈ omegaPlane
    rw [omegaTorus_apply]
    simp [omegaPlane, a.ne_zero]

/-- A torus word in genuine Siegel generators has no eigenvalue one. -/
theorem omega_borel_fixedSpace_eq_bot [Finite F] (hF : 2 < Nat.card F) :
    fixedSpace (omegaNatural (F := F)) omegaBorel = ⊥ := by
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hc
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have ha1 : (a : F) ≠ 1 := fun h => ha (Units.ext h)
  have hi1 := inv_ne_one.mpr ha1
  apply bot_unique
  intro v hv
  have he := hv ⟨omegaTorus a, omegaTorus_mem_borel a⟩
  change (omegaTorus a).val.val v = v at he
  rw [omegaTorus_apply] at he
  have h0 : v (.inl 0) = 0 := zero_of_scalar_fixed ha1 (congrFun he (.inl 0))
  have h1 : v (.inl 1) = 0 := zero_of_scalar_fixed hi1 (congrFun he (.inl 1))
  have h2 : v (.inr 0) = 0 := zero_of_scalar_fixed hi1 (congrFun he (.inr 0))
  have h3 : v (.inr 1) = 0 := zero_of_scalar_fixed ha1 (congrFun he (.inr 1))
  ext i
  rcases i with i | i <;> fin_cases i <;> assumption

/-- Transport to I/C_I(K) using the displayed group map, Borel image and
actual equivariant linear identification. The extension I need not split. -/
theorem omega_centralQuotient_fixed [Finite F] (hF : 2 < Nat.card F)
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K B : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (φ : K →* OmegaPlus 2 F)
    (e : centralQuotient ρ K I ≃ₗ[ZMod 2] (VectorD 2 F))
    (he : ∀ g v, e (centralQuotientRepresentation ρ K I hI g v) =
      (omegaNatural) (φ g) (e v))
    (hB : (B.subgroupOf K).map φ = omegaBorel) :
    I ⊓ fixedSpace ρ B ≤ fixedSpace ρ K := by
  apply inf_fixedSpace_le_of_centralQuotient ρ K B I hI
  exact fixedSpace_eq_bot_of_equivariant _ (omegaNatural) φ e he _ _ hB
    (omega_borel_fixedSpace_eq_bot hF)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.RemainingModels

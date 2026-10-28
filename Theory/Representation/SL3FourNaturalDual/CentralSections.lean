module

public import Theory.Representation.BinaryOffender.CentralSectionSplitting
public import Theory.Representation.SL3FourNaturalDual.GraphSum

/-!
# Lifting a natural SL₃(4) central section

The scalar matrix ωI is central in the actual SL₃(F₄) model and has norm
1+ω+ω²=0 on its natural module. Transport this polynomial through natural
coordinates on I/C_I(K). On an Irr⁺ member I=[I,K], the central norm argument
removes C_I(K), giving natural coordinates on I itself.

The intertwiner is retained over F₂, with the specified concrete F₄ natural
representation. This result does not select an Irr⁺ member or classify any
representation; those are separate uses of B.4.5 and F.9.18.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.20, printed p.955, and F.9.18(4), printed p.325.
-/

@[expose] public noncomputable section
namespace Representation.SL3FourNaturalDual
open Matrix BinaryOffender Subgroup

/-- A nontrivial central scalar in the actual special linear group. -/
def centralScalar : SL := ⟨Matrix.diagonal (fun _ => omega), by
  rw [det_diagonal]
  change omega * (omega * (omega * 1)) = 1
  decide +kernel⟩

lemma centralScalar_commute (g : SL) : centralScalar * g = g * centralScalar := by
  apply Subtype.ext
  exact (Matrix.scalar_commute omega (Commute.all omega) g.val).eq

lemma centralScalar_natural (w : W) : natural centralScalar w = omega • w := by
  change (Matrix.diagonal (fun _ => omega)).mulVec w = omega • w
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.smul_apply, smul_eq_mul]

lemma centralScalar_norm (w : W) :
    natural centralScalar (natural centralScalar w) + natural centralScalar w + w = 0 := by
  rw [centralScalar_natural, centralScalar_natural, smul_smul]
  calc
    (omega * omega) • w + omega • w + w = (omega * omega + omega + 1) • w := by
      rw [add_smul, add_smul, one_smul]
    _ = 0 := by rw [show omega * omega + omega + 1 = 0 by decide +kernel, zero_smul]

variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) G U)

/-- Natural coordinates on the literal central quotient, with the component marking. -/
structure NaturalCentralSection (K : Subgroup G) (eK : K ≃* SL)
    (I : Submodule (ZMod 2) U) where
  stable : K ≤ subspaceStabilizer ρ I
  coordinates : centralQuotient ρ K I ≃ₗ[ZMod 2] W
  equivariant : ∀ k v, coordinates (centralQuotientRepresentation ρ K I stable k v) =
    natural (eK k) (coordinates v)

variable {ρ} {K : Subgroup G} {eK : K ≃* SL} {I : Submodule (ZMod 2) U}

/-- Naturality is needed only on I/C_I(K); its fixed vectors are then eliminated. -/
theorem NaturalCentralSection.disjoint_fixedSpace (d : NaturalCentralSection ρ K eK I)
    (hI : subspaceCommutator ρ I K = I) : Disjoint I (fixedSpace ρ K) := by
  let z : K := eK.symm centralScalar
  have hz : ∀ k ∈ K, (z : G) * k = k * z := by
    intro k hk
    have he : z * (⟨k, hk⟩ : K) = (⟨k, hk⟩ : K) * z := by
      apply eK.injective
      simpa only [map_mul, z, eK.apply_symm_apply] using centralScalar_commute (eK ⟨k, hk⟩)
    exact congrArg Subtype.val he
  apply disjoint_fixedSpace_of_centralCubicNorm ρ K I hI z z.property hz
  intro v hv
  let w : I := ⟨v, hv⟩
  let q := ((fixedSpace ρ K).comap I.subtype).mkQ
  let σ := centralQuotientRepresentation ρ K I d.stable
  have hq : σ z (σ z (q w)) + σ z (q w) + q w = 0 := by
    apply d.coordinates.injective
    simp only [map_add, map_zero, σ, d.equivariant, z, eK.apply_symm_apply]
    exact centralScalar_norm (d.coordinates (q w))
  have hm : centralCubicNorm ρ (z : G) v ∈ I := by
    rw [centralCubicNorm_apply]
    exact I.add_mem (I.add_mem ((d.stable z.property _).2 ((d.stable z.property _).2 hv))
      ((d.stable z.property _).2 hv)) hv
  exact (Submodule.Quotient.mk_eq_zero ((fixedSpace ρ K).comap I.subtype)).mp
    (show q (⟨centralCubicNorm ρ (z : G) v, hm⟩ : I) = 0 from hq)

/-- The coordinates on I use the actual projection I → I/C_I(K). -/
def NaturalCentralSection.lift (d : NaturalCentralSection ρ K eK I)
    (hI : subspaceCommutator ρ I K = I) : I ≃ₗ[ZMod 2] W :=
  (centralSectionEquiv ρ K I (d.disjoint_fixedSpace hI)).trans d.coordinates

lemma NaturalCentralSection.lift_equivariant (d : NaturalCentralSection ρ K eK I)
    (hI : subspaceCommutator ρ I K = I) (k : K) (v : I) :
    d.lift hI ((invariantSubspace ρ K I d.stable).toRepresentation k v) =
      natural (eK k) (d.lift hI v) :=
  d.equivariant k (Submodule.Quotient.mk v)

lemma NaturalCentralSection.lift_symm_equivariant (d : NaturalCentralSection ρ K eK I)
    (hI : subspaceCommutator ρ I K = I) (g : SL) (w : W) :
    ρ (eK.symm g : G) ((d.lift hI).symm w : U) =
      ((d.lift hI).symm (natural g w) : U) := by
  have he := d.lift_equivariant hI (eK.symm g) ((d.lift hI).symm w)
  rw [eK.apply_symm_apply, LinearEquiv.apply_symm_apply] at he
  have hv := congrArg (d.lift hI).symm he
  exact congrArg Subtype.val (((d.lift hI).symm_apply_apply _).symm.trans hv)

end Representation.SL3FourNaturalDual

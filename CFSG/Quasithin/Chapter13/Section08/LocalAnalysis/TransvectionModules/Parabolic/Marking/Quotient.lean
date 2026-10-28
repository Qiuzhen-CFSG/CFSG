module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.ResidualTransport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.QuotientTransport
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Parabolic surjections from the source residual and Sylow subgroup

The two-residual transport identifies K₂ with the residual of C_H(V₂/V₁).
An ambient Sylow subgroup contained in this quotient centralizer supplements
that residual. Thus their join is the full quotient centralizer, not merely
a subgroup of its normalizer. A marking identifies its image with the duad
parabolic in A₆ or S₆. Restriction constructs a surjection, and faithfulness
on H/O₂(H) proves its kernel is a two-group. The explicit coordinate change
(04)(15) sends the duad {4,5} used by BinaryFlags to {0,1} used by the
existing quotient maps. Applying those maps gives the actual S₃ quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.6(1),
printed p.948. The marking of the quotient centralizer remains an explicit
premise here; it is not a source-theorem conclusion proved by this module.
-/

@[expose] public section

open Subgroup Theory.SpecificGroups.SymmetricSix
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking

/-- Switch the marked duad {4,5} to the quotient model's duad {0,1}. -/
def duadChange : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * Equiv.swap 1 5

private theorem duadChange_pair : pair 0 1 = duadChange • pair 4 5 := by decide

/-- Conjugation, retaining the two different coordinate conventions. -/
def flagDuadEquiv : BinaryFlags.H1 ≃* duadStabilizer :=
  MulAction.stabilizerEquivStabilizer (g := duadChange) (by exact duadChange_pair)

@[simp] theorem flagDuadEquiv_apply (x : BinaryFlags.H1) :
    (flagDuadEquiv x : Equiv.Perm (Fin 6)) = duadChange * x.val * duadChange⁻¹ :=
  MulAction.stabilizerEquivStabilizer_apply duadChange_pair x

/-- The same coordinate change on the actual alternating parabolic. -/
def flagA6DuadEquiv : BinaryFlags.L1 ≃* a6DuadStabilizer where
  toFun x := ⟨⟨flagDuadEquiv ⟨x.val, x.property.1⟩, by
    change Equiv.Perm.sign (flagDuadEquiv ⟨x.val, x.property.1⟩).val = 1
    rw [flagDuadEquiv_apply]
    have hx : Equiv.Perm.sign x.val = 1 := x.property.2
    simp [hx]⟩, (flagDuadEquiv ⟨x.val, x.property.1⟩).property⟩
  invFun x := ⟨flagDuadEquiv.symm ⟨x.val.val, x.property⟩,
    (flagDuadEquiv.symm ⟨x.val.val, x.property⟩).property, by
      change Equiv.Perm.sign (flagDuadEquiv.symm ⟨x.val.val, x.property⟩).val = 1
      have he := MulAction.stabilizerEquivStabilizer_symm_apply duadChange_pair
        (⟨x.val.val, x.property⟩ : duadStabilizer)
      change (flagDuadEquiv.symm ⟨x.val.val, x.property⟩).val =
        duadChange⁻¹ * x.val.val * (duadChange⁻¹)⁻¹ at he
      rw [he]
      have hx : Equiv.Perm.sign x.val.val = 1 := x.val.property
      simp [hx]⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg (fun z : BinaryFlags.H1 => z.val) (flagDuadEquiv.symm_apply_apply ⟨x.val, x.property.1⟩)
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : duadStabilizer => z.val) (flagDuadEquiv.apply_symm_apply ⟨x.val.val, x.property⟩)
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : duadStabilizer => z.val) (map_mul flagDuadEquiv
      (⟨x.val, x.property.1⟩ : BinaryFlags.H1) ⟨y.val, y.property.1⟩)

variable {G : Type*} [Group G] [Finite G]

/-- The literal K₂ and the standing Sylow subgroup generate the full quotient
centralizer. The Sylow containment is in C_H(V₂/V₁), not C_H(V₂). -/
theorem K2_sup_sylow (T : Sylow 2 G) (H V₂ V₁ : Subgroup G)
    [IsElementaryAbelian 2 V₁] (hHZ : H ≤ centralizer (V₁ : Set G))
    (hTA : (T : Subgroup G) ≤ commutatorPreimage H V₂ V₁) :
    Source.K2 H V₂ ⊔ (T : Subgroup G) = commutatorPreimage H V₂ V₁ := by
  rw [centralizer_residual_eq_preimage H V₂ V₁ hHZ]
  have hs := congrArg (fun J : Subgroup (commutatorPreimage H V₂ V₁) =>
    J.map (commutatorPreimage H V₂ V₁).subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hTA))
  rwa [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTA,
    ← MonoidHom.range_eq_map, range_subtype] at hs

variable {A : Type*} [Group A]

/-- Restrict a coordinate action onto its proved image, retaining the kernel. -/
noncomputable def imageSurjection (H P : Subgroup G) (hPH : P ≤ H)
    (φ : H →* A) (J : Subgroup A) (hJ : (P.subgroupOf H).map φ = J) : P →* J :=
  (φ.comp (inclusion hPH)).codRestrict J (by
    intro p
    rw [← hJ]
    exact ⟨⟨p.val, hPH p.property⟩, p.property, rfl⟩)

omit [Finite G] in
theorem imageSurjection_surjective (H P : Subgroup G) (hPH : P ≤ H)
    (φ : H →* A) (J : Subgroup A) (hJ : (P.subgroupOf H).map φ = J) :
    Function.Surjective (imageSurjection H P hPH φ J hJ) := by
  intro j
  have hj : j.val ∈ (P.subgroupOf H).map φ := hJ.symm ▸ j.property
  obtain ⟨h, hh, he⟩ := hj
  exact ⟨⟨h.val, hh⟩, Subtype.ext he⟩

omit [Finite G] in
theorem imageSurjection_kernel (H P : Subgroup G) (hPH : P ≤ H)
    (φ : H →* A) (J : Subgroup A) (hJ : (P.subgroupOf H).map φ = J)
    (hk : IsPGroup 2 φ.ker) : IsPGroup 2 (imageSurjection H P hPH φ J hJ).ker := by
  have he : (imageSurjection H P hPH φ J hJ).ker = φ.ker.comap (inclusion hPH) := by
    ext p
    exact Subtype.ext_iff
  rw [he]
  exact hk.comap_of_injective (inclusion hPH) (inclusion_injective hPH)

/-- The marked symmetric parabolic gives the literal source S₃ quotient. -/
noncomputable def sourceDuadQuotient (H V₂ T : Subgroup G) (hTH : T ≤ H)
    (φ : H →* Equiv.Perm (Fin 6)) (hk : IsPGroup 2 φ.ker)
    (himage : ((Source.K2 H V₂ ⊔ T).subgroupOf H).map φ = BinaryFlags.H1) :
    (Source.K2 H V₂ ⊔ T : Subgroup G) ⧸ pCore 2 (Source.K2 H V₂ ⊔ T : Subgroup G) ≃*
      Equiv.Perm (Fin 3) := by
  let hPH := sup_le (Source.K2_le H V₂) hTH
  let f := imageSurjection H (Source.K2 H V₂ ⊔ T) hPH φ BinaryFlags.H1 himage
  let g := flagDuadEquiv.toMonoidHom.comp f
  have hs : Function.Surjective g := flagDuadEquiv.surjective.comp
    (imageSurjection_surjective H _ hPH φ _ himage)
  have hker : g.ker = f.ker := by
    ext x
    exact flagDuadEquiv.map_eq_one_iff
  exact duadQuotientOfTwoKernel g hs (hker ▸ imageSurjection_kernel H _ hPH φ _ himage hk)

/-- The marked alternating parabolic gives the same literal source quotient. -/
noncomputable def sourceA6DuadQuotient (H V₂ T : Subgroup G) (hTH : T ≤ H)
    (φ : H →* Equiv.Perm (Fin 6)) (hk : IsPGroup 2 φ.ker)
    (himage : ((Source.K2 H V₂ ⊔ T).subgroupOf H).map φ = BinaryFlags.L1) :
    (Source.K2 H V₂ ⊔ T : Subgroup G) ⧸ pCore 2 (Source.K2 H V₂ ⊔ T : Subgroup G) ≃*
      Equiv.Perm (Fin 3) := by
  let hPH := sup_le (Source.K2_le H V₂) hTH
  let f := imageSurjection H (Source.K2 H V₂ ⊔ T) hPH φ BinaryFlags.L1 himage
  let g := flagA6DuadEquiv.toMonoidHom.comp f
  have hs : Function.Surjective g := flagA6DuadEquiv.surjective.comp
    (imageSurjection_surjective H _ hPH φ _ himage)
  have hker : g.ker = f.ker := by
    ext x
    exact flagA6DuadEquiv.map_eq_one_iff
  exact a6DuadQuotientOfTwoKernel g hs (hker ▸ imageSurjection_kernel H _ hPH φ _ himage hk)

omit [Finite G] in
/-- Faithful coordinates on the actual H/O₂(H) have exactly the source two-core
as kernel when pulled back to H. -/
theorem source_coordinate_kernel (H : Subgroup G)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 6)) (hφ : Function.Injective φ) :
    (φ.comp (QuotientGroup.mk' (pCore 2 H))).ker = pCore 2 H := by
  rw [MonoidHom.ker_comp_of_injective _ _ hφ, QuotientGroup.ker_mk']

/-- Assemble the residual and quotient calculations from a marking of the
quotient centralizer. The source point/plane marking is an independent premise;
the full centralizer image and a two-kernel parabolic map are not assumed. -/
theorem residual_and_quotient_of_marked_preimage (T : Sylow 2 G)
    (H V₂ V₁ : Subgroup G) [IsElementaryAbelian 2 V₁]
    (hHZ : H ≤ centralizer (V₁ : Set G))
    (hTA : (T : Subgroup G) ≤ commutatorPreimage H V₂ V₁)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 6)) (hφ : Function.Injective φ)
    (himage : ((commutatorPreimage H V₂ V₁).subgroupOf H).map
        (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.H1 ∨
      ((commutatorPreimage H V₂ V₁).subgroupOf H).map
        (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.L1) :
    ((Source.K2 H V₂).subgroupOf H).map
        (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.K ∧
      Nonempty (((Source.K2 H V₂ ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Source.K2 H V₂ ⊔ (T : Subgroup G) : Subgroup G)) ≃*
          Equiv.Perm (Fin 3)) := by
  let ψ := φ.comp (QuotientGroup.mk' (pCore 2 H))
  have hk : IsPGroup 2 ψ.ker := by
    rw [source_coordinate_kernel H φ hφ]
    exact pCore_isPGroup
  have hTH : (T : Subgroup G) ≤ H := hTA.trans (commutatorPreimage_le H V₂ V₁)
  have hj := K2_sup_sylow T H V₂ V₁ hHZ hTA
  rcases himage with himage | himage
  · refine ⟨K2_image H V₂ V₁ hHZ ψ ?_ ?_, ?_⟩
    · exact himage.symm ▸ BinaryFlags.K_le_H1
    · exact himage.le
    · exact ⟨sourceDuadQuotient H V₂ T hTH ψ hk (by rw [hj]; exact himage)⟩
  · refine ⟨K2_image H V₂ V₁ hHZ ψ ?_ ?_, ?_⟩
    · exact himage.symm ▸ BinaryFlags.K_le_L1
    · exact himage.le.trans inf_le_left
    · exact ⟨sourceA6DuadQuotient H V₂ T hTH ψ hk (by rw [hj]; exact himage)⟩

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking

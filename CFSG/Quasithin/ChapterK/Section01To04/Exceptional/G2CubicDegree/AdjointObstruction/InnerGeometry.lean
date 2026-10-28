module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointObstruction.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointObstruction.RootDisplacement
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointObstruction.InnerGeometry.RootKernels
public import Theory.AtlasPort.LinearGroups.G2.TorusNormalization
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.RootElements
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.InvolutionConjugacy

/-!
# Root geometry for the G₂ adjoint involution calculation

The short-root curve C moves six field dimensions, as does the long-root
curve A by `RootDisplacement`. Wilson A and B are both long roots; the
short-root calculation here is separate. Conjugation and the split torus
transport the exact displacement and the pointwise-kernel bound to every
root element in the literal octonion model.

The final theorem constructs `InnerCalculations` from the field cardinality.
The exhaustive conjugacy theorem for the actual finite octonion model
discharges the two-root-class premise. Thus every nonidentity involution
has fixed codimension exactly `6*r`, and its pointwise kernel inside its
centralizer has order at most `2^r`. These local calculations also hold at
q = 2; the source obstruction uses them at r ≥ 2.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 8.2,
manuscript pp.53–54. The root kernel calculation replaces the pointwise-action
step in the source's parabolic argument with explicit checked coordinates.
-/

public section
open Atlas.G2 Atlas.SplitOctonion
open Atlas.G2.Restricted.Adjoint.Coordinates
open Representation Representation.BinaryOffender Subgroup
open CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree
attribute [local instance] ZMod.algebra
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction.InnerGeometry
variable {F : Type*} [Field F] [CharP F 2]
private theorem kernel_conj_mem {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (t c g : G)
    (hg : g ∈ involutionFixedKernel ρ t) :
    c * g * c⁻¹ ∈ involutionFixedKernel ρ (c * t * c⁻¹) := by
  refine ⟨mem_centralizer_singleton_iff.mpr ?_, ?_⟩
  · have h := mem_centralizer_singleton_iff.mp hg.1
    simpa only [mul_assoc, inv_mul_cancel_left] using congrArg (fun x => c*x*c⁻¹) h
  · intro v hv
    have hw : ρ c⁻¹ v ∈ fixedSpace ρ (zpowers t) := by
      rw [mem_fixedSpace_zpowers_iff] at hv ⊢
      have h := congrArg (ρ c⁻¹) hv
      simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc,
        inv_mul_cancel_left] using h
    have hfix := hg.2 _ hw
    simp only [map_mul, Module.End.mul_apply, hfix]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]

/-- Conjugation transports the literal pointwise kernel inside the corresponding
involution centralizer. -/
theorem fixedKernel_card_conj {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (t c : G) :
    Nat.card (involutionFixedKernel ρ (c * t * c⁻¹)) =
      Nat.card (involutionFixedKernel ρ t) := by
  have hle (t c : G) : Nat.card (involutionFixedKernel ρ t) ≤
      Nat.card (involutionFixedKernel ρ (c * t * c⁻¹)) := by
    let f : involutionFixedKernel ρ t → involutionFixedKernel ρ (c*t*c⁻¹) :=
      fun g => ⟨c*g*c⁻¹, kernel_conj_mem ρ t c g g.property⟩
    apply Nat.card_le_card_of_injective f
    intro g h he
    apply Subtype.ext
    have hh : MulAut.conj c (g : G) = MulAut.conj c (h : G) := congrArg Subtype.val he
    exact (MulAut.conj c).injective hh
  apply le_antisymm _ (hle t c)
  simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using
    hle (c*t*c⁻¹) c⁻¹
private def rootCImage : (Fin 6 → F) →ₗ[F] Space F where
  toFun w := ![w 0,w 1,w 2,0,w 3,0,w 4,w 5,0,0,0,w 5,w 3,0]
  map_add' := by intros; ext i; fin_cases i <;> simp
  map_smul' := by intros; ext i; fin_cases i <;> simp

omit [CharP F 2] in
private theorem rootCImage_injective : Function.Injective (rootCImage (F := F)) := by
  intro v w h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h4 := congrFun h 4
  have h6 := congrFun h 6
  have h7 := congrFun h 7
  funext i
  fin_cases i <;> simpa [rootCImage] using (by assumption)

private theorem rootC_one_range :
    LinearMap.range ((Representation.restrictScalars (k := ZMod 2) (action F)) (rootC 1) -
      LinearMap.id) = ((rootCImage (F := F)).restrictScalars (ZMod 2)).range := by
  ext w
  constructor
  · rintro ⟨v,rfl⟩
    refine ⟨![v 4+v 9+v 12,v 7+v 8+v 11,v 10+v 13,v 9,v 10,v 8],?_⟩
    change rootCImage _ = action F (rootC 1) v - v
    rw [action_rootC]
    ext i
    fin_cases i <;> simp [rootCImage, sub_eq_add_neg, CharTwo.neg_eq] <;>
      ring_nf <;> simp [CharTwo.ofNat_eq_mod]
  · rintro ⟨v,rfl⟩
    refine ⟨![0,0,0,0,v 0+v 3,0,0,v 1+v 5,v 5,v 3,v 4,0,0,v 2+v 4],?_⟩
    change action F (rootC 1) _ - _ = rootCImage v
    rw [action_rootC]
    ext i
    fin_cases i <;> simp [rootCImage, sub_eq_add_neg, CharTwo.neg_eq] <;>
      ring_nf <;> simp [CharTwo.ofNat_eq_mod]

/-- The actual short-root representative moves six field dimensions. -/
theorem rootC_one_fixedCodim [Finite F] {r : ℕ} (hF : Nat.card F = 2^r) :
    fixedCodim (adjointBinary F) (zpowers (rootC 1)) = 6*r := by
  let : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  let : Module.Finite (ZMod 2) (Space F) := Module.Finite.of_finite
  have hd : Module.finrank (ZMod 2) F = r := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) F = 2 ^ r
    rw [← hF]
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)).symm
  let τ := Representation.restrictScalars (k := ZMod 2) (action F)
  have he : fixedCodim (adjointBinary F) (zpowers (rootC 1)) =
      fixedCodim τ (zpowers (rootC 1)) := by
    have h := fixedCodim_map_equivariant (adjointBinary F) τ
      (MonoidHom.id (Model F)) ((equiv F).restrictScalars (ZMod 2))
      (fun g v => by
        change equiv F (Restricted.Adjoint.action F g v) = action F g (equiv F v)
        exact (repEquiv F).isIntertwining g v) (zpowers (rootC 1))
    simpa only [Subgroup.map_id] using h
  rw [he, fixedCodim_zpowers_eq_displacement_rank, rootC_one_range,
    LinearMap.finrank_range_of_inj (show Function.Injective
      ((rootCImage (F := F)).restrictScalars (ZMod 2)) from rootCImage_injective)]
  simp [Module.finrank_pi_fintype, hd]
variable [Finite F]

/-- All nonidentity values of the actual short-root curve have the same
six-dimensional displacement after scalar restriction. -/
theorem rootC_fixedCodim {r : ℕ} (hF : Nat.card F = 2^r) (a : F) (ha : a ≠ 0) :
    fixedCodim (adjointBinary F) (zpowers (rootC a)) = 6*r := by
  let : Finite (Restricted.Adjoint.Space F) :=
    Finite.of_injective (equiv F) (equiv F).injective
  let : Module.Finite (ZMod 2) (Restricted.Adjoint.Space F) := Module.Finite.of_finite
  have hc : torus (Units.mk0 a ha) 1 * rootC 1 * (torus (Units.mk0 a ha) 1)⁻¹ =
      rootC a := by simpa using torus_rootC (Units.mk0 a ha) 1 (1 : F)
  rw [← hc, fixedCodim_zpowers_conj]
  exact rootC_one_fixedCodim hF

/-- The long-root kernel bound holds at every nonzero field parameter. -/
theorem rootA_fixedKernel_card (a : F) (ha : a ≠ 0) :
    Nat.card (involutionFixedKernel (adjointBinary F) (rootA a)) ≤ Nat.card F := by
  have hc : torus (Units.mk0 a ha) 1 * rootA 1 * (torus (Units.mk0 a ha) 1)⁻¹ =
      rootA a := by simpa using torus_rootA (Units.mk0 a ha) 1 (1 : F)
  rw [← hc, fixedKernel_card_conj]
  exact rootA_one_fixedKernel_card

/-- The short-root kernel bound holds at every nonzero field parameter. -/
theorem rootC_fixedKernel_card (a : F) (ha : a ≠ 0) :
    Nat.card (involutionFixedKernel (adjointBinary F) (rootC a)) ≤ Nat.card F := by
  have hc : torus (Units.mk0 a ha) 1 * rootC 1 * (torus (Units.mk0 a ha) 1)⁻¹ =
      rootC a := by simpa using torus_rootC (Units.mk0 a ha) 1 (1 : F)
  rw [← hc, fixedKernel_card_conj]
  exact rootC_one_fixedKernel_card

/-- The two genuine root classes satisfy the precise displacement equality. -/
theorem fixedCodim_of_isRootElement {r : ℕ} (hF : Nat.card F = 2^r)
    (t : Model F) (ht : EvenInvolutionGeometry.IsRootElement t) :
    fixedCodim (adjointBinary F) (zpowers t) = 6*r := by
  let : Finite (Restricted.Adjoint.Space F) :=
    Finite.of_injective (equiv F) (equiv F).injective
  let : Module.Finite (ZMod 2) (Restricted.Adjoint.Space F) := Module.Finite.of_finite
  rcases ht with ⟨c,a,ha,rfl⟩ | ⟨c,a,ha,rfl⟩
  · change fixedCodim (adjointBinary F) (zpowers (c*rootA a*c⁻¹)) = _
    rw [fixedCodim_zpowers_conj]
    exact AdjointObstruction.rootA_fixedCodim F hF a ha
  · change fixedCodim (adjointBinary F) (zpowers (c*rootC a*c⁻¹)) = _
    rw [fixedCodim_zpowers_conj]
    exact rootC_fixedCodim hF a ha

/-- The kernel bound is transported by actual conjugation in the octonion model. -/
theorem fixedKernel_card_of_isRootElement (t : Model F)
    (ht : EvenInvolutionGeometry.IsRootElement t) :
    Nat.card (involutionFixedKernel (adjointBinary F) t) ≤ Nat.card F := by
  rcases ht with ⟨c,a,ha,rfl⟩ | ⟨c,a,ha,rfl⟩
  · change Nat.card (involutionFixedKernel (adjointBinary F) (c*rootA a*c⁻¹)) ≤ _
    rw [fixedKernel_card_conj]
    exact rootA_fixedKernel_card a ha
  · change Nat.card (involutionFixedKernel (adjointBinary F) (c*rootC a*c⁻¹)) ≤ _
    rw [fixedKernel_card_conj]
    exact rootC_fixedKernel_card a ha

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction.InnerGeometry

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction
open InnerGeometry
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- Conditional assembly of root displacement and the actual fixed kernels,
retained for clients supplying exhaustive involution conjugacy separately. -/
theorem innerCalculations_of_root_conjugacy {r : ℕ} (hF : Nat.card F = 2^r)
    (hroot : ∀ t : Model F, t ≠ 1 → t^2 = 1 → EvenInvolutionGeometry.IsRootElement t) :
    InnerCalculations F r where
  involution_codim t ht hs := (fixedCodim_of_isRootElement hF t (hroot t ht hs)).ge
  fixed_kernel_card t ht hs _ := by
    rw [← hF]
    exact fixedKernel_card_of_isRootElement t (hroot t ht hs)

/-- The actual G₂ adjoint involution calculations. Exhaustive root conjugacy
discharges both local premises needed by the common-fixed-space obstruction
in GM04 Proposition 8.2, without an offender or kernel-bound hypothesis. -/
theorem innerCalculations {r : ℕ} (hF : Nat.card F = 2^r) :
    InnerCalculations F r :=
  innerCalculations_of_root_conjugacy F hF
    (fun _ ht hs => EvenInvolutionGeometry.involution_isRoot hs ht)

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction

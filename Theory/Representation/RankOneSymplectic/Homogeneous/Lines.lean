module
public import Theory.Representation.RankOneSymplectic.Homogeneous.Components

/-!
# Dual partners of normal line components

A nonzero invariant pairing between lines identifies each with the dual of
the other. Therefore a line can have only one nonorthogonal isotypic line
component. A rank-one involutory isometry moving a line pairs it nontrivially
with its image: otherwise their invariant span is isotropic and fixed pointwise.

This supplies the line case in homogeneous normal restriction after
Aschbacher--Smith G.4.6, printed pp.339--340.
-/

public noncomputable section
open Subgroup Module
open scoped MonoidAlgebra
namespace Representation.RankOneSymplectic.Homogeneous
open CubicClifford.Inertia
variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

omit [FiniteDimensional F V] in
theorem line_isotropic (B : LinearMap.BilinForm F V) (halt : B.IsAlt)
    (U : Submodule F V) (hdim : finrank F U=1) :
    ∀ u∈U, ∀ v∈U, B u v=0 := by
  intro u hu v hv
  by_cases hz : u=0
  · simp [hz]
  obtain ⟨c,hc⟩ := exists_smul_eq_of_finrank_eq_one hdim
    (show (⟨u,hu⟩ : U)≠0 from fun h => hz (congrArg Subtype.val h)) (⟨v,hv⟩ : U)
  have he : c • u=v := congrArg Subtype.val hc
  rw [←he]
  simp only [map_smul,halt u,smul_zero]

omit [FiniteDimensional F V] in
theorem conjugate_finrank (ρ : Representation F G V) (N : Subgroup G) [N.Normal]
    (A : Subrepresentation (ρ.comp N.subtype)) (g : G) :
    finrank F (conjugateSubrepresentationOrderIso ρ N g A).toSubmodule=
      finrank F A.toSubmodule := by
  rw [conjugateSubrepresentationOrderIso_toSubmodule]
  exact (Submodule.equivMapOfInjective (ρ g) (ρ.apply_bijective g).injective A.toSubmodule).finrank_eq.symm

theorem pairing_line_equiv (σ : Representation F G V) (B : LinearMap.BilinForm F V)
    (hp : ∀ g x y, B (σ g x) (σ g y)=B x y)
    (A J : Subrepresentation σ) [A.toRepresentation.IsIrreducible]
    (hA : finrank F A.toSubmodule=1) (hJ : finrank F J.toSubmodule=1)
    (hne : pairing σ B hp A J≠0) :
    Nonempty (A.toRepresentation ≃ₗ J.toRepresentation.dual) := by
  have hi := (IsIrreducible.injective_or_eq_zero (pairing σ B hp A J)).resolve_right hne
  have hd : finrank F A.toSubmodule=finrank F (Module.Dual F J.toSubmodule) := by
    rw [Subspace.dual_finrank_eq,hA,hJ]
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi
  let e := (pairing σ B hp A J).ofBijective ⟨hi,hs⟩
  exact ⟨⟨e.toLinearEquiv,e.isIntertwining'⟩⟩

theorem unique_paired_line_component (σ : Representation F G V)
    (B : LinearMap.BilinForm F V) (hp : ∀ g x y, B (σ g x) (σ g y)=B x y)
    (J A C : Subrepresentation σ) [A.toRepresentation.IsIrreducible]
    [C.toRepresentation.IsIrreducible]
    (hJ : finrank F J.toSubmodule=1) (hA : finrank F A.toSubmodule=1) (hC : finrank F C.toSubmodule=1)
    (hcA : component σ A=A) (hcC : component σ C=C)
    (hAJ : pairing σ B hp A J≠0) (hCJ : pairing σ B hp C J≠0) : A=C := by
  obtain ⟨eA⟩ := pairing_line_equiv σ B hp A J hA hJ hAJ
  obtain ⟨eC⟩ := pairing_line_equiv σ B hp C J hC hJ hCJ
  have he := component_eq_of_equiv σ (eA.trans eC.symm)
  simpa only [hcA,hcC] using he

omit [FiniteDimensional F V] in
theorem moved_line_pairing_ne_zero (ρ : Representation F G V)
    (N : Subgroup G) [N.Normal]
    (B : LinearMap.BilinForm F V) (halt : B.IsAlt) (hB : B.Nondegenerate)
    (hp : ∀ g x y, B (ρ g x) (ρ g y)=B x y)
    (A : Subrepresentation (ρ.comp N.subtype)) (hA : finrank F A.toSubmodule=1)
    (t : G) (ht : t*t=1)
    (hr : finrank F (LinearMap.range (ρ t-LinearMap.id))=1)
    (hne : conjugateSubrepresentationOrderIso ρ N t A≠A) :
    pairing (ρ.comp N.subtype) B (fun n => hp n) (conjugateSubrepresentationOrderIso ρ N t A) A≠0 := by
  intro hz
  let C := conjugateSubrepresentationOrderIso ρ N t A
  have hC : finrank F C.toSubmodule=1 := (conjugate_finrank ρ N A t).trans hA
  have hCA : ∀ u∈C, ∀ v∈A, B u v=0 := by
    intro u hu v hv
    have he := congrArg (fun f : IntertwiningMap C.toRepresentation A.toRepresentation.dual =>
      f ⟨u,hu⟩ ⟨v,hv⟩) hz
    change pairing (ρ.comp N.subtype) B (fun n => hp n) C A ⟨u,hu⟩ ⟨v,hv⟩ = 0 at he
    exact (pairing_apply (ρ.comp N.subtype) B (fun n => hp n) C A ⟨u,hu⟩ ⟨v,hv⟩).symm.trans he
  have hAC : ∀ u∈A, ∀ v∈C, B u v=0 := fun u hu v hv => halt.isRefl _ _ (hCA v hv u hu)
  let U := A.toSubmodule⊔C.toSubmodule
  have hcmap : C.toSubmodule=A.toSubmodule.map (ρ t) := conjugateSubrepresentationOrderIso_toSubmodule ρ N t A
  have hstable : ∀ u∈U, ρ t u∈U := by
    intro u hu
    obtain ⟨v,hv,w,hw,rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    apply Submodule.add_mem
    · exact (show C.toSubmodule≤U from le_sup_right) (show ρ t v∈C.toSubmodule from hcmap ▸ ⟨v,hv,rfl⟩)
    · rw [hcmap] at hw
      obtain ⟨x,hx,rfl⟩ := hw
      have he : ρ t (ρ t x)=x := by rw [←Module.End.mul_apply,←map_mul,ht,map_one,Module.End.one_apply]
      rw [he]
      exact (show A.toSubmodule≤U from le_sup_left) hx
  have hiso : ∀ u∈U, ∀ v∈U, B u v=0 := by
    intro u hu v hv
    obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨z,hz,w,hw,rfl⟩ := Submodule.mem_sup.mp hv
    simp only [map_add,LinearMap.add_apply,line_isotropic B halt A.toSubmodule hA x hx z hz,
      line_isotropic B halt C.toSubmodule hC y hy w hw,hCA y hy z hz,hAC x hx w hw,add_zero]
  have hfix := fixes_isotropic B hB (ρ t) (hp t) hr U hstable hiso
  apply hne
  apply Subrepresentation.toSubmodule_injective
  rw [conjugateSubrepresentationOrderIso_toSubmodule]
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    rw [hfix v ((show A.toSubmodule≤U from le_sup_left) hv)]
    exact hv
  · intro hx
    exact ⟨x,hx,hfix x ((show A.toSubmodule≤U from le_sup_left) hx)⟩

end Representation.RankOneSymplectic.Homogeneous

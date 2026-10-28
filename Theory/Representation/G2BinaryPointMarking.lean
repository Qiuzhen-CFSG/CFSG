module
public import Theory.Representation.G2BinaryPointImage
public import Theory.Representation.G2NaturalTransitivity

/-!
# Compatible coordinates for a binary G₂ point parabolic

Derived G₂ is transitive on nonzero natural vectors. Conjugate the actor
embedding and the natural projection by the same element to place the
specified vector on the first coordinate. The actual point stabilizer then
maps onto the parabolic intersected with the actor image; relative
normality places the elementary actor in its unipotent two-core.

Source: Aschbacher–Smith B.4.6 and 13.8.27, printed p.963.
The concrete model retains the attribution in LICENSES/ATLAS.txt.
-/

public section

open Subgroup Representation
namespace Atlas.G2.Natural.BinaryPointFlag
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

/-- Mark the actual point by changing both compatible coordinates together. -/
theorem exists_compatible_point_marking
    (ρ : Representation (ZMod 2) D W)
    (f : D →* Model F) (hf : Function.Injective f)
    (hrange : commutator (Model F) ≤ f.range)
    (p : W →ₗ[F] Natural.Space F) (hp : Function.Surjective p)
    (he : ∀ a v, p (ρ a v) = Natural.action F (f a) (p v))
    (C A : Subgroup D) (hAC : A ≤ C)
    (hn : C ≤ normalizer (A : Set D)) [IsElementaryAbelian 2 A]
    (v : W) (hv : p v ≠ 0)
    (hC : ∀ a, a ∈ C ↔ Natural.action F (f a) (p v) = p v) :
    ∃ (f' : D →* Model F) (p' : W →ₗ[F] Natural.Space F),
      Function.Injective f' ∧ Function.Surjective p' ∧
      (∀ a w, p' (ρ a w) = Natural.action F (f' a) (p' w)) ∧
      C.map f' = BinaryCore.secondParabolic ⊓ f'.range ∧
      A.map f' ≤ unipotent ∧
      BinaryParabolicPair.derivedSecondAmbient ≤ normalizer (A.map f' : Set _) := by
  let E := Restricted.NaturalCoordinates.equiv F
  let z : Natural.Space F := E.symm (Pi.single 0 1)
  have hz : z ≠ 0 := by
    intro h
    have hh := congrArg E h
    have hh' : (Pi.single 0 1 : Fin 6 → F) = 0 := by
      simpa only [z,E.apply_symm_apply,map_zero] using hh
    have heq := congrFun hh' 0
    simp at heq
  obtain ⟨g,hg⟩ := Natural.derivedAction_transitive F (p v) z hv hz
  let f' := (MulAut.conj (g : Model F)).toMonoidHom.comp f
  let p' := (Natural.action F (g : Model F)).comp p
  have hp' : Function.Surjective p' := by
    intro w
    obtain ⟨u,hu⟩ := hp (Natural.action F (g : Model F)⁻¹ w)
    refine ⟨u, ?_⟩
    change Natural.action F (g : Model F) (p u) = w
    rw [hu,← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one]
    rfl
  have he' (a) (w) : p' (ρ a w) = Natural.action F (f' a) (p' w) := by
    change Natural.action F (g : Model F) (p (ρ a w)) =
      Natural.action F ((g : Model F)*f a*(g : Model F)⁻¹)
        (Natural.action F (g : Model F) (p w))
    rw [he]
    simp only [← Module.End.mul_apply,← map_mul]
    congr 2
    group
  have hrange' : commutator (Model F) ≤ f'.range := by
    intro b hb
    let b' : Model F := (g : Model F)⁻¹*b*(g : Model F)
    have hb' : b' ∈ commutator (Model F) := by
      have hh := (inferInstance : (commutator (Model F)).Normal).conj_mem b hb (g : Model F)⁻¹
      simpa only [inv_inv] using hh
    obtain ⟨a,ha⟩ := hrange hb'
    refine ⟨a,?_⟩
    change (g : Model F)*f a*(g : Model F)⁻¹=b
    rw [ha]
    dsimp only [b']
    group
  have hpv : E (p' v) = Pi.single 0 1 := by
    change E (Natural.derivedAction F g (p v)) = _
    rw [hg]
    exact E.apply_symm_apply _
  have hC' (a) : a ∈ C ↔
      Restricted.NaturalCoordinates.action F (f' a) (Pi.single 0 1) = Pi.single 0 1 := by
    rw [hC,← hpv]
    have hcoord := LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' (f' a)) (p' v)
    change E (Natural.action F (f' a) (p' v)) =
      Restricted.NaturalCoordinates.action F (f' a) (E (p' v)) at hcoord
    rw [← hcoord, E.injective.eq_iff,← he']
    change Natural.action F (f a) (p v) = p v ↔
      Natural.action F (g : Model F) (p (ρ a v)) = Natural.action F (g : Model F) (p v)
    rw [he]
    have hi : Function.Injective (Natural.action F (g : Model F)) := by
      apply Function.HasLeftInverse.injective
      refine ⟨Natural.action F (g : Model F)⁻¹,?_⟩
      intro w
      simp only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
    exact hi.eq_iff.symm
  obtain ⟨hu,hn'⟩ := marked_point_actor_bounds f' hrange' C A hAC hn hC'
  exact ⟨f',p',(MulAut.conj (g : Model F)).injective.comp hf,hp',he',marked_point_image f' C hC',hu,hn'⟩

end Atlas.G2.Natural.BinaryPointFlag

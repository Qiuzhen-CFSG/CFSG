module
public import Theory.Representation.BinaryAlternatingFiveExtension.MarkedAlternating
public import Theory.Representation.BinaryAlternatingFiveExtension.BorelAutomorphisms
/-!
# The literal affine Borel embedding and its central twist

The natural A₄ semidirect product embeds in the natural A₅ extension by
including its point stabilizer. Its image is exactly the centralizer of
the marked weight-four vector. Outside the height kernel, the Borel twist
is multiplication by this same marked vector. These identities retain the
literal maps needed to compare the unitary point and plane endpoints.

Source: the overlap adjustment for Aschbacher--Smith 13.5.17, printed p.922.
-/

@[expose] public section
open Subgroup
namespace BinaryPermutation.AlternatingFiveExtension
open AlternatingFiveFlag AlternatingFiveBorel FiveCentralizerGeometry

/-- The literal inclusion of the A₄ overlap in the affine A₅ plane. -/
def borelEmbedding : BorelModel →* AlternatingModel :=
  SemidirectProduct.map (MonoidHom.id V) B.subtype (fun _ => rfl)

@[simp] theorem borelEmbedding_left (x : BorelModel) : (borelEmbedding x).left=x.left := rfl
@[simp] theorem borelEmbedding_right (x : BorelModel) : (borelEmbedding x).right=x.right.val := rfl

@[simp] theorem borelEmbedding_inl (x : V) :
    borelEmbedding (SemidirectProduct.inl x)=SemidirectProduct.inl x := by rfl

theorem borelEmbedding_injective : Function.Injective borelEmbedding := by
  intro x y he
  apply SemidirectProduct.ext
  · exact congrArg (fun t : AlternatingModel => t.left) he
  · exact Subtype.ext (congrArg (fun t : AlternatingModel => t.right) he)

theorem borelEmbedding_range : borelEmbedding.range =
    centralizer ({SemidirectProduct.inl (Multiplicative.ofAdd z)} : Set AlternatingModel) := by
  have hc (x : AlternatingModel) : x∈centralizer
      ({SemidirectProduct.inl (Multiplicative.ofAdd z)} : Set AlternatingModel) ↔ x.right∈B := by
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      have hh := congrArg SemidirectProduct.left h
      change x.left*(coreAction x.right.val) (Multiplicative.ofAdd z) =
        (Multiplicative.ofAdd z)*x.left at hh
      rw [mul_comm (Multiplicative.ofAdd z) x.left] at hh
      exact (fixes_z_iff x.right.val).mp
        (congrArg Multiplicative.toAdd (mul_left_cancel hh))
    · intro h
      apply SemidirectProduct.ext
      · change x.left*(coreAction x.right.val) (Multiplicative.ofAdd z) =
          (Multiplicative.ofAdd z)*x.left
        have hh : (coreAction x.right.val) (Multiplicative.ofAdd z)=Multiplicative.ofAdd z :=
          congrArg Multiplicative.ofAdd ((fixes_z_iff x.right.val).mpr h)
        rw [hh,mul_comm]
      · simp
  ext x
  rw [hc]
  constructor
  · rintro ⟨x,rfl⟩
    exact x.right.property
  · intro hx
    exact ⟨⟨x.left,⟨x.right,hx⟩⟩,rfl⟩

/-- Outside the height kernel, the affine twist multiplies by the marked root. -/
theorem Overlap.borelTwist_outside_residual (x : BorelModel)
    (hx : x∉pResidual 2 BorelModel) :
    Overlap.borelTwist x=x*SemidirectProduct.inl (Multiplicative.ofAdd z) := by
  have h0 : x.left.toAdd.val 4≠0 := by
    intro h
    apply hx
    rw [residualModel_eq]
    exact h
  have h1 : x.left.toAdd.val 4=1 := (show x.left.toAdd.val 4=0 ∨ x.left.toAdd.val 4=1 from (by decide : ∀ a : ZMod 2, a=0 ∨ a=1) _).resolve_left h0
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd (x.left.toAdd+x.left.toAdd.val 4 • z)=
      x.left*(coreAction x.right.val.val) (Multiplicative.ofAdd z)
    have hz : (coreAction x.right.val.val) (Multiplicative.ofAdd z)=Multiplicative.ofAdd z :=
      congrArg Multiplicative.ofAdd ((fixes_z_iff x.right.val.val).mpr x.right.property)
    rw [h1,one_smul,hz]
    rfl
  · simp [Overlap.borelTwist_right]
end BinaryPermutation.AlternatingFiveExtension

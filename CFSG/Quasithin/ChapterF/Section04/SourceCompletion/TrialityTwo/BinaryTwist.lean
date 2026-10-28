module
public import Theory.SpecificGroups.Triality.BinaryReflectionOrbits
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.CartanInvolutions
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.Comparison

/-!
# Recognition except for one binary twist

A simultaneous fixed-unipotent Borel conjugation removes three of the four
remaining reflection parameters. Both commuting squares identify its images,
so involutivity, escape from the Borel, and actual product order six survive
on the same endpoint maps. The fixed field has two elements. Its zero branch
satisfies the matching native relation and hence gives the marked ambient
isomorphism. The sole remaining branch is the arms reflection multiplied by
the highest long-root involution, paired with the central reflection.

The twisted relation is not excluded here. In particular this is not an
unconditional recognition of a small completion.
Source: Aschbacher--Smith F.4.15--17, pp.281--283 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.BinaryTorusEndpoints
variable {G : Type*} [Group G] (c : Completion G)

/-- A common Borel conjugation reduces the same marked order-six pair to a
single binary twist of the arms reflection. -/
theorem reduce_to_binary_twist (p q b j : fixedField parameters)
    (hs : (endpointWord .arms ![p,p,q] 0 1)^2=1)
    (ht : (endpointWord .central (Pi.single 0 b) ![b,j,(1+b)*j] 1)^2=1)
    (hsout : c.left (endpointWord .arms ![p,p,q] 0 1)∉c.middle.range)
    (htout : c.right (endpointWord .central (Pi.single 0 b) ![b,j,(1+b)*j] 1)∉c.middle.range)
    (hpow : (c.left (endpointWord .arms ![p,p,q] 0 1)*
      c.right (endpointWord .central (Pi.single 0 b) ![b,j,(1+b)*j] 1))^6=1)
    (ho : orderOf (c.left (endpointWord .arms ![p,p,q] 0 1)*
      c.right (endpointWord .central (Pi.single 0 b) ![b,j,(1+b)*j] 1))=6) :
    ∃ k : fixedField parameters, (k=0 ∨ k=1) ∧
      let s := endpointWord .arms ![0,0,k] 0 1
      let t := simpleEndpoint .central
      s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
        (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 := by
  let u := fixedBorel ![b,p+b,j+p+b]
  let A := MulAut.conj (c.middle u)
  let sa := MulAut.conj (amalgam.left u)
  let ta := MulAut.conj (amalgam.right u)
  let s := endpointWord .arms ![0,0,p+q+b] 0 1
  let t := simpleEndpoint .central
  have he : sa s=endpointWord .arms ![p,p,q] 0 1 :=
    (four_coordinate_conjugation p q b j).1
  have hf : ta t=endpointWord .central (Pi.single 0 b) ![b,j,(1+b)*j] 1 :=
    (four_coordinate_conjugation p q b j).2
  have hmL (x : parabolic parameters .arms) : c.left (sa x)=A (c.left x) := by
    simp only [sa,A,MulAut.conj_apply,map_mul,map_inv]
    rfl
  have hmR (x : parabolic parameters .central) : c.right (ta x)=A (c.right x) := by
    have hu : c.right (amalgam.right u)=c.middle u :=
      (DFunLike.congr_fun c.compatible u).symm
    simp only [ta,A,MulAut.conj_apply,map_mul,map_inv,hu]
  have hse : A (c.left s)=c.left (endpointWord .arms ![p,p,q] 0 1) := by
    rw [←hmL,he]
  have hte : A (c.right t)=c.right (endpointWord .central (Pi.single 0 b) ![b,j,(1+b)*j] 1) := by
    rw [←hmR,hf]
  refine ⟨p+q+b,fixed_eq_zero_or_one _,?_,?_,?_,?_,?_,?_⟩
  · apply sa.injective
    rw [map_pow,he,hs,map_one]
  · apply ta.injective
    rw [map_pow,hf,ht,map_one]
  · intro hh
    apply hsout
    rw [←hse]
    exact (mem_normalizer_iff.mp (c.middle.range.le_normalizer ⟨u,rfl⟩) (c.left s)).mp hh
  · intro hh
    apply htout
    rw [←hte]
    exact (mem_normalizer_iff.mp (c.middle.range.le_normalizer ⟨u,rfl⟩) (c.right t)).mp hh
  · apply A.injective
    rw [map_pow,map_mul,hse,hte,hpow,map_one]
  · calc
      _ = orderOf (A (c.left s*c.right t)) := (A.orderOf_eq _).symm
      _ = 6 := by rw [map_mul,hse,hte]; exact ho

variable [Finite G]

/-- The small completion is recognized on both full endpoint maps unless the
single central-root-twisted pair satisfies the actual hexagon equation. -/
theorem recognition_or_twisted_relation (horder : Nat.card G≤Nat.card Model) :
    (∃ f : G ≃* Model, (∀ x, f (c.left x)=modelCompletion.left x) ∧
      (∀ x, f (c.right x)=modelCompletion.right x)) ∨
    (let s := endpointWord .arms ![0,0,1] 0 1
     let t := simpleEndpoint .central
     s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
       (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6) := by
  obtain ⟨p,q,b,j,hs,ht,hsout,htout,hpow,ho⟩ :=
    c.exists_four_coordinate_involutions_of_order_bound horder
  obtain ⟨k,hk,hs,ht,hsout,htout,hpow,ho⟩ :=
    c.reduce_to_binary_twist p q b j hs ht hsout htout hpow ho
  rcases hk with rfl | rfl
  · left
    exact c.exists_mulEquiv_of_matching_involutions modelCompletion _ _
      hs ht hsout htout hpow canonical_product_six
  · exact Or.inr ⟨hs,ht,hsout,htout,hpow,ho⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion

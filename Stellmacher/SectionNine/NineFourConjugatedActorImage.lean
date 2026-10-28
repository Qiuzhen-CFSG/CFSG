module
public import Stellmacher.SectionNine.NineFourReduction
public import Stellmacher.SectionNine.NineResidualImageOddCore

/-!
# The conjugated actor remains in the selected factor

For the original local actor and residual-commutator conjugator in (9.4),
a surjective quotient map with the local two-core as kernel places the
conjugated actor image in its canonical odd-core commutator factor. If the
actor image is an involution, so is the conjugated image. This image also
belongs to the image of the literal initial-core conjugate closure T.
These fields supply the nontrivial support actor in source (5).

The local residual maps into the odd core. Mapping the original commutator
membership therefore puts the conjugator image in the canonical factor;
that factor already contains the actor image and hence its conjugate.
Conjugation preserves the two involution properties. Finally the conjugated
actor is a seed of T, so its image lies in Tbar. This extracts the exact
quotient calculation already used by the auxiliary factor-image theorem.

Source: Stellmacher (9.4)(1), printed p.51/PDF p.41, choosing the first
factor containing the residual commutator, in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_conjugated_actor_image
    {G K : Type u} [Group G] [Finite G] [Group K] [Finite K]
    {T A B : Subgroup G} (ctx : SectionNineLocalContext G T A B)
    (actor : G) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (conjugator : G)
    (hconjugator : conjugator ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep,
      Subgroup.zpowers actor⁆)
    (f : GAt ctx.Γ ctx.criticalPath.firstStep →* K) (hsurj : Function.Surjective f)
    (hkernel : f.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hinvolution : _root_.IsInvolution (f ⟨actor,hactor⟩)) :
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let t : P := ⟨actor,hactor⟩
    let x : P := ⟨conjugator,nine_four_conjugator_mem_stabilizer ctx.Γ
      ctx.criticalPath.firstStep actor conjugator hactor hconjugator⟩
    let u := f (x⁻¹*t*x)
    let D := ⁅SectionOne.oddCore K,Subgroup.zpowers (f t)⁆ ⊔ Subgroup.zpowers (f t)
    let T0 := conjugateClosure (Subgroup.zpowers (conjugator⁻¹*actor*conjugator))
      (QAt ctx.Γ ctx.criticalPath.a)
    u ∈ D ∧ _root_.IsInvolution u ∧ u ∈ (T0.subgroupOf P).map f := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let t : P := ⟨actor,hactor⟩
  let x : P := ⟨conjugator,nine_four_conjugator_mem_stabilizer Γ cp.firstStep
    actor conjugator hactor hconjugator⟩
  let u : P := x⁻¹*t*x
  let D := ⁅SectionOne.oddCore K,Subgroup.zpowers (f t)⁆ ⊔ Subgroup.zpowers (f t)
  let T0 := conjugateClosure (Subgroup.zpowers (conjugator⁻¹*actor*conjugator))
    (QAt Γ cp.a)
  have hEP : EAt Γ cp.firstStep ≤ P := by
    change Γ.twoResidualAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have htP : Subgroup.zpowers actor ≤ P := Subgroup.zpowers_le.mpr hactor
  have hnative : (⁅EAt Γ cp.firstStep,Subgroup.zpowers actor⁆).subgroupOf P =
      ⁅(EAt Γ cp.firstStep).subgroupOf P,Subgroup.zpowers t⁆ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup _ _).trans
      (sup_le hEP htP)),Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hEP,
      MonoidHom.map_zpowers]
    rfl
  have hxnative : x ∈ ⁅(EAt Γ cp.firstStep).subgroupOf P,Subgroup.zpowers t⁆ := by
    rw [← hnative]
    exact hconjugator
  have hodd := nine_local_residual_image_le_oddCore ctx cp.firstStep cp.a
    (Γ.adjacent_symm cp.firstStep_adj) f hsurj hkernel.symm.le
  have hxD : f x ∈ D := by
    apply (le_sup_left : ⁅SectionOne.oddCore K,Subgroup.zpowers (f t)⁆ ≤ D)
    have hmap := Subgroup.mem_map_of_mem f hxnative
    rw [Subgroup.map_commutator,MonoidHom.map_zpowers] at hmap
    exact Subgroup.commutator_mono hodd le_rfl hmap
  have htD : f t ∈ D := (le_sup_right : Subgroup.zpowers (f t) ≤ D)
    (Subgroup.mem_zpowers (f t))
  have huD : f u ∈ D := by
    change f (x⁻¹*t*x) ∈ D
    rw [map_mul,map_mul,map_inv]
    exact D.mul_mem (D.mul_mem (D.inv_mem hxD) htD) hxD
  have huInv : _root_.IsInvolution (f u) := by
    refine ⟨?_,?_⟩
    · intro hone
      have heq : f t = 1 := by
        have hh := congrArg (fun z : K => f x * z * (f x)⁻¹) hone
        simpa only [u,map_mul,map_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,
          mul_one,mul_inv_cancel] using hh
      exact hinvolution.1 heq
    · have heq := congrArg (fun z : K => (f x)⁻¹ * z * f x) hinvolution.2
      simpa only [u,map_mul,map_inv,pow_two,mul_assoc,mul_inv_cancel_left,
        mul_one,inv_mul_cancel] using heq
  refine ⟨huD,huInv,?_⟩
  apply Subgroup.mem_map_of_mem f
  change (u:G) ∈ T0
  apply Subgroup.subset_closure
  exact ⟨1,⟨conjugator⁻¹*actor*conjugator,Subgroup.mem_zpowers _⟩,by simp [u,x,t]⟩

end Stellmacher.SectionNine

module
public import Theory.Representation.SymplecticFourOrthogonalCover.DisplacementLifting

/-!
# Full-cover fixed kernels determined by commutators

Symplectic duality identifies the fixed space with the perpendicular of the
natural displacement space. The original cover projection lifts every
natural displacement and every fixed vector, so inclusion of the literal
commutator subgroups reverses inclusion of the full fixed kernels. All
central attachments remain present; no splitting is assumed.

The source application is the equal-root kernel comparison in
NonbinarySymplectic.CriticalReduction.EqualRootKernels, MS93 (5.7), p.919.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement
namespace Representation.SymplecticFourOrthogonalCover
variable {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
  {σ : Representation (ZMod 2) (L (K := F)) W}

/-- Smaller commutators give larger fixed kernels on the entire central cover. -/
theorem embedded_fixed_antitone_of_commutator_le
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (A B : Subgroup G) (α : A →* L (K := F)) (β : B →* L (K := F))
    (hA : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (α a) w)) =
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hB : ∀ (b : B) (w : W), j (Multiplicative.ofAdd (σ (β b) w)) =
      b.val*j (Multiplicative.ofAdd w)*b.val⁻¹)
    (hle : ⁅A,j.range⁆ ≤ ⁅B,j.range⁆) :
    j.range ⊓ centralizer (B : Set G) ≤ j.range ⊓ centralizer (A : Set G) := by
  let α' := (commutator (Sp F)).subtype.comp α
  let β' := (commutator (Sp F)).subtype.comp β
  let D := displacementSpace β'.range
  let P := ((D.restrictScalars (ZMod 2)).comap p.toLinearMap).toAddSubgroup.toSubgroup.map j
  have hBP : ⁅B,j.range⁆ ≤ P := by
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨w,rfl⟩ := hu
    refine ⟨Multiplicative.ofAdd (σ (β ⟨b,hb⟩) w.toAdd-w.toAdd),?_,?_⟩
    · change p (σ (β ⟨b,hb⟩) w.toAdd-w.toAdd) ∈ D
      rw [map_sub,p.isIntertwining]
      exact Coinvariants.sub_mem_ker
        (ρ := (symplecticNatural 2).comp β'.range.subtype) ⟨β' ⟨b,hb⟩,⟨_,rfl⟩⟩ _
    · rw [ofAdd_sub,map_div,div_eq_mul_inv,hB]
      rfl
  have hD : displacementSpace α'.range ≤ D := by
    intro v hv
    obtain ⟨w,hw,hm⟩ := natural_displacement_lifts j.range A j rfl α σ hA p hp.1 v hv
    obtain ⟨u,hu,he⟩ := hBP (hle hm)
    have he' : u=Multiplicative.ofAdd w := hj he
    change p u.toAdd ∈ D at hu
    rw [he'] at hu
    change p w ∈ D at hu
    rwa [hw] at hu
  intro x hx
  obtain ⟨w,rfl⟩ := hx.1
  have hfix : p w.toAdd ∈ TwoLocalCover.fixedSpace β'.range := by
    intro b hb
    obtain ⟨b,rfl⟩ := hb
    have he : σ (β b) w.toAdd=w.toAdd := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hB]
      change b.val*j w*b.val⁻¹=j w
      rw [hx.2 b.val b.property,mul_inv_cancel_right]
    exact (LinearMap.congr_fun (p.isIntertwining' (β b)) w.toAdd).symm.trans (congrArg p he)
  have hfixA : p w.toAdd ∈ TwoLocalCover.fixedSpace α'.range := by
    rw [←orthogonal_displacementSpace] at hfix ⊢
    exact fun v hv => hfix v (hD hv)
  refine ⟨⟨w,rfl⟩,fun a ha => ?_⟩
  have he := cover_fixed_of_projection_fixed p hp (α ⟨a,ha⟩) w.toAdd
    (hfixA (α' ⟨a,ha⟩) ⟨_,rfl⟩)
  have hh := congrArg (fun w => j (Multiplicative.ofAdd w)) he
  rw [hA,mul_inv_eq_iff_eq_mul] at hh
  exact hh
end Representation.SymplecticFourOrthogonalCover

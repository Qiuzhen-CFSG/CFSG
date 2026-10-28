module
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Theory.Representation.PlaneRootNormalizer
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Geometry

/-!
# Two-group normalizers fix covered root displacements

A two-group preserving a one-dimensional space over a characteristic-two
field fixes it pointwise. Apply this to the natural displacement of a
normalized actor. Fixed-vector lifting through a symplectic central cover
then fixes the entire preimage, including the complete covering kernel.
The embedded version centralizes the literal subgroup commutator.

This supplies the original radical action in the proper replacement branch
of MS93 (3.7), printed pp.872--876. It does not identify the replacement
with that radical or impose a field-degree restriction.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Algebra (ZMod 2) F] in
private theorem two_normalizer_fixes_displacement
    (A P : Subgroup (Sp F)) (hP : IsPGroup 2 P)
    (hn : P ≤ normalizer (A : Set (Sp F)))
    (hd : Module.finrank F (displacementSpace A) ≤ 1)
    (x : P) (v : Vector F) (hv : v ∈ displacementSpace A) : x.val • v = v := by
  let ρ : Representation F P (Vector F) := (symplecticNatural 2).comp P.subtype
  let D : Subrepresentation ρ := {
    toSubmodule := displacementSpace A
    apply_mem_toSubmodule := by
      intro y w hw
      have he := PointRadicalAction.displacement_conjugate A y.val
      have hA : A.map (MulAut.conj y.val).toMonoidHom=A :=
        mem_normalizer_iff_map_conj_eq.mp (hn y.property)
      rw [hA] at he
      change y.val • w ∈ displacementSpace A
      rw [he]
      exact Submodule.mem_map_of_mem hw }
  exact congrArg Subtype.val (PlaneRootNormalizer.apply_eq_of_finrank_le_one
    D.toRepresentation hP hd x ⟨v,hv⟩)

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) (L (K := F)) W}

/-- A two-group normalizing an actor with natural displacement a line fixes
the entire displacement preimage in a symplectic central cover. -/
theorem cover_two_normalizer_fixes_displacement
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (A P : Subgroup (L (K := F))) (hP : IsPGroup 2 P)
    (hn : P ≤ normalizer (A : Set (L (K := F))))
    (hd : Module.finrank F (displacementSpace (A.map (commutator (Sp F)).subtype)) ≤ 1)
    (x : P) (w : W)
    (hw : p w ∈ displacementSpace (A.map (commutator (Sp F)).subtype)) :
    σ x.val w = w := by
  apply cover_fixed_of_projection_fixed p hp
  exact two_normalizer_fixes_displacement _ _ (hP.map (commutator (Sp F)).subtype)
    ((map_mono hn).trans (A.le_normalizer_map (commutator (Sp F)).subtype)) hd
    ⟨x.val.val,mem_map_of_mem _ x.property⟩ (p w) hw

variable {G : Type*} [Group G]
open scoped commutatorElement

/-- The original two-group normalizer centralizes the actual embedded
displacement, including its complete central covering kernel. -/
theorem embedded_two_normalizer_centralizes_displacement
    (U T P : Subgroup G) (hP : IsPGroup 2 P) (hn : P ≤ normalizer (T : Set G))
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hjr : j.range = U) (γ : G →* L (K := F))
    (hact : ∀ (g : G) (v : W), j (Multiplicative.ofAdd (σ (γ g) v)) =
      g*j (Multiplicative.ofAdd v)*g⁻¹)
    (hd : Module.finrank F
      (displacementSpace ((T.map γ).map (commutator (Sp F)).subtype)) ≤ 1) :
    P ≤ centralizer ((⁅U,T⁆ : Subgroup G) : Set G) := by
  apply le_centralizer_iff.mpr
  rw [commutator_comm]
  apply commutator_le.mpr
  intro t ht u hu
  obtain ⟨v,rfl⟩ := (show u ∈ j.range from hjr.symm ▸ hu)
  let w := σ (γ t) v.toAdd - v.toAdd
  have hw : p w ∈ displacementSpace ((T.map γ).map (commutator (Sp F)).subtype) := by
    change p (σ (γ t) v.toAdd-v.toAdd) ∈ _
    rw [map_sub,p.isIntertwining]
    exact Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp ((T.map γ).map (commutator (Sp F)).subtype).subtype)
      ⟨(γ t).val,mem_map_of_mem _ (mem_map_of_mem γ ht)⟩ (p v.toAdd)
  have hval : j (Multiplicative.ofAdd w) = ⁅t,j v⁆ := by
    change j (Multiplicative.ofAdd (σ (γ t) v.toAdd-v.toAdd)) = _
    rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact]
    rfl
  intro x hx
  have hf := cover_two_normalizer_fixes_displacement p hp (T.map γ) (P.map γ)
    (hP.map γ) ((map_mono hn).trans (T.le_normalizer_map γ)) hd
    ⟨γ x,mem_map_of_mem γ hx⟩ w hw
  have he := congrArg (fun w => j (Multiplicative.ofAdd w)) hf
  rw [hact,hval,mul_inv_eq_iff_eq_mul] at he
  exact he

end Representation.SymplecticFourOrthogonalCover

module
public import Theory.Representation.SymplecticFourOrthogonalCover.QuadraticLifting
public import Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
/-!
# Lifting natural displacement through a marked central cover

Every vector in the field displacement span has a lift in the literal
embedded group commutator. Surjectivity of the original projection lifts
the generators, and additive generation lifts their entire span. The
projection kernel is retained; no complement is used.

Source: the secondary seed calculation in MS93 (3.6), printed p.871.
-/
public noncomputable section
open Subgroup Representation Module
open scoped IsMulCommutative commutatorElement
namespace Representation.SymplecticFourOrthogonalCover
open Representation.OneCohomology Theory.SpecificGroups.SymplecticFour
variable {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W] [Group G]

omit [Finite F] [CharP F 2] in
theorem natural_displacement_lifts
    (U A : Subgroup G) (j : Multiplicative W →* G) (hjU : j.range = U)
    (β : A →* L (K := F)) (σ : Representation (ZMod 2) (L (K := F)) W)
    (hact : ∀ a : A, ∀ w : W, j (Multiplicative.ofAdd (σ (β a) w)) =
      (a:G)*j (Multiplicative.ofAdd w)*(a:G)⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : Function.Surjective p) :
    let α := (commutator (Sp F)).subtype.comp β
    ∀ v ∈ displacementSpace α.range, ∃ w : W, p w = v ∧
      j (Multiplicative.ofAdd w) ∈ ⁅A,U⁆ := by
  dsimp only
  let α := (commutator (Sp F)).subtype.comp β
  have hP : displacementSpace α.range =
      ⨆ a : A, LinearMap.range (symplecticNatural 2 (α a)-LinearMap.id) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨y,v⟩,rfl⟩
      obtain ⟨a,ha⟩ := y.property
      change y.val • v-v ∈ _
      rw [←ha]
      exact (le_iSup (fun a : A => LinearMap.range (symplecticNatural 2 (α a)-LinearMap.id)) a)
        ⟨v,rfl⟩
    · apply iSup_le
      intro a v hv
      obtain ⟨w,rfl⟩ := hv
      exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp α.range.subtype)
        ⟨α a,⟨a,rfl⟩⟩ w
  intro v hv
  rw [hP] at hv
  refine Submodule.iSup_induction _
    (motive := fun v => ∃ w : W, p w=v ∧ j (Multiplicative.ofAdd w) ∈ ⁅A,U⁆) hv ?_ ?_ ?_
  · intro a v hv
    obtain ⟨v,rfl⟩ := hv
    obtain ⟨w,rfl⟩ := hp v
    refine ⟨σ (β a) w-w,?_,?_⟩
    · rw [map_sub,p.isIntertwining]
      rfl
    · rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      exact commutator_mem_commutator a.property (hjU ▸ ⟨_,rfl⟩)
  · exact ⟨0,map_zero _,by simp⟩
  · rintro u v ⟨w,hw,hm⟩ ⟨w',hw',hm'⟩
    refine ⟨w+w',by rw [map_add,hw,hw'],?_⟩
    simpa only [ofAdd_add,map_mul] using (⁅A,U⁆).mul_mem hm hm'
end Representation.SymplecticFourOrthogonalCover

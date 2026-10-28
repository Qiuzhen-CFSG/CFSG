module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.DualLowerBound.PlaneSeed
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# The actual plane action and its equivariant generating family

The actor is GL₄(2) on its natural space and the permutation points are its
two-dimensional subspaces. A vector fixed by a plane parabolic determines
an equivariant family indexed by these planes: transport it using any
linear automorphism carrying the original plane to the chosen plane.
The stabilizer hypothesis proves independence of the transport. The orbit
span assumption says exactly that this family generates the module.

The two explicit involutions have square-zero displacements of ranks one
and two on the natural space. Their definitions alone assert no conjugacy
classification or permutation-module exclusion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.4(5), printed p.947, and the identification
of the plane parabolic in 13.8.25, pp.960–962.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.PlanePermutation

abbrev Space := ChiefFactors.NaturalSpace
abbrev Actor := BinaryLinear.GL Space
abbrev Plane := {P : Submodule (ZMod 2) Space // Module.finrank (ZMod 2) P = 2}

instance : MulAction Actor Plane where
  smul g P := ⟨P.val.map g.toLinearMap, by rw [g.finrank_map_eq]; exact P.property⟩
  one_smul P := Subtype.ext (by change P.val.map LinearMap.id = P.val; exact Submodule.map_id _)
  mul_smul g h P := Subtype.ext (by
    change P.val.map (g.toLinearMap.comp h.toLinearMap) = _
    exact Submodule.map_comp h.toLinearMap g.toLinearMap P.val)

theorem smul_val (g : Actor) (P : Plane) : (g • P).val = P.val.map g.toLinearMap := rfl

theorem smul_eq_iff_mem_parabolic (g : Actor) (P : Plane) :
    g • P = P ↔ g ∈ BinaryLinear.parabolic P.val := by
  constructor
  · intro h v
    have he := congrArg Subtype.val h
    change P.val.map g.toLinearMap = P.val at he
    rw [← he, Submodule.mem_map_equiv]
    simp only [LinearEquiv.symm_apply_apply]
    rw [he]
  · intro h
    apply Subtype.ext
    ext v
    change v ∈ P.val.map g.toLinearMap ↔ v ∈ P.val
    rw [Submodule.mem_map_equiv]
    exact (BinaryLinear.parabolic P.val).inv_mem h v

theorem exists_smul_eq (P Q : Plane) : ∃ g : Actor, g • P = Q := by
  obtain ⟨g, hg⟩ := BinaryLinear.FourParabolicAction.exists_linearEquiv_map_eq P.val Q.val
    (P.property.trans Q.property.symm)
  exact ⟨g, Subtype.ext hg⟩

/-- The elementary root adding coordinate `j` to coordinate `i`. -/
def root (i j : Fin 4) (hij : i ≠ j) : Actor :=
  BinaryLinear.transvection (Pi.single i 1) (LinearMap.proj j)
    (by simp [hij.symm])

def firstInvolution : Actor := root 0 1 (by decide)
def secondInvolution : Actor := firstInvolution * root 2 3 (by decide)

theorem root_apply (i j : Fin 4) (hij : i ≠ j) (v : Space) :
    root i j hij v = v + v j • Pi.single i 1 := rfl


theorem root_sq (i j : Fin 4) (hij : i ≠ j) : root i j hij ^ 2 = 1 := by
  have hi : (root i j hij)⁻¹ = root i j hij := by ext v; rfl
  calc
    root i j hij ^ 2 = root i j hij * (root i j hij)⁻¹ := by rw [hi, pow_two]
    _ = 1 := mul_inv_cancel _

theorem firstInvolution_sq : firstInvolution ^ 2 = 1 := root_sq _ _ _

theorem firstInvolution_commute_root : Commute firstInvolution (root 2 3 (by decide)) := by
  change firstInvolution * root 2 3 (by decide) = root 2 3 (by decide) * firstInvolution
  ext v i
  fin_cases i <;> simp [firstInvolution, LinearEquiv.mul_apply, root_apply]

theorem secondInvolution_sq : secondInvolution ^ 2 = 1 := by
  rw [secondInvolution, firstInvolution_commute_root.mul_pow, firstInvolution_sq, root_sq,
    one_mul]

theorem firstInvolution_ne_one : firstInvolution ≠ 1 := by
  intro h
  have hh := congrArg (fun g : Actor => g (Pi.single 1 1) 0) h
  norm_num [firstInvolution, root_apply, Pi.single_apply] at hh

theorem secondInvolution_ne_one : secondInvolution ≠ 1 := by
  intro h
  have hh := congrArg (fun g : Actor => g (Pi.single 1 1) 0) h
  norm_num [secondInvolution, firstInvolution, LinearEquiv.mul_apply, root_apply,
    Pi.single_apply, show (3 : Fin 4) ≠ 1 by decide] at hh

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

/-- A parabolic-fixed cyclic vector gives a generating, equivariant family
indexed by the actual two-planes. No irreducibility or faithfulness is used. -/
theorem exists_equivariant_generating_family
    (ρ : Representation (ZMod 2) K V) (eK : K ≃* Actor)
    (hgen : IsPlaneParabolicGenerated ρ eK) :
    ∃ f : Plane → V,
      (∀ g Q, f (g • Q) = ρ (eK.symm g) (f Q)) ∧
      Submodule.span (ZMod 2) (Set.range f) = ⊤ := by
  classical
  obtain ⟨P, v, hP, hfix, hspan⟩ := hgen
  let P₀ : Plane := ⟨P, hP⟩
  choose a ha using (exists_smul_eq P₀)
  have value_eq {g h : Actor} (he : g • P₀ = h • P₀) :
      ρ (eK.symm g) v = ρ (eK.symm h) v := by
    have hm : h⁻¹ * g ∈ BinaryLinear.parabolic P := by
      apply (smul_eq_iff_mem_parabolic _ P₀).mp
      rw [mul_smul, he, inv_smul_smul]
    have hv := hfix (eK.symm (h⁻¹ * g)) (by simpa using hm)
    have hh := congrArg (ρ (eK.symm h)) hv
    simpa only [map_mul, map_inv, Module.End.mul_apply, Representation.self_inv_apply] using hh
  let f : Plane → V := fun Q => ρ (eK.symm (a Q)) v
  refine ⟨f, ?_, ?_⟩
  · intro g Q
    change ρ (eK.symm (a (g • Q))) v = ρ (eK.symm g) (ρ (eK.symm (a Q)) v)
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul]
    apply value_eq
    rw [ha, mul_smul, ha]
  · apply top_unique
    rw [← hspan]
    apply Submodule.span_mono
    rintro _ ⟨g, rfl⟩
    refine ⟨eK g • P₀, ?_⟩
    change ρ (eK.symm (a (eK g • P₀))) v = ρ g v
    rw [← eK.symm_apply_apply g]
    apply value_eq
    simpa only [eK.apply_symm_apply] using ha (eK g • P₀)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.PlanePermutation

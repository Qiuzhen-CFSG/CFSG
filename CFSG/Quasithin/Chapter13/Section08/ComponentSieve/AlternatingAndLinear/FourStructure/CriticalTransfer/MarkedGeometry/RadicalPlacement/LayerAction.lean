module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.HeadPlane
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Two layers of the marked binary plane action

A reducible action on a binary two-space has exponent two. Consequently a
faithful group fixing a lower layer pointwise and acting reducibly on its
two-dimensional quotient is a two-group (every element has fourth power one).
An actual marked subgroup which is not a two-group therefore forces quotient
irreducibility. The normal two-core kills both irreducible layers and lies in
the block-unipotent radical of the specified seed plane.

This supplies sufficient geometric action facts without requiring equality
with the full plane stabilizer. The head coordinates and actor identification
are fixed, and the seed plane is the image constructed in `HeadPlane`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.25,
printed pp.960–961 (PDF pp.977–978), using the marked subgroup L₀* which fixes
Ṽ₃ and is not a two-group.
-/

@[expose] public section

open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.RadicalPlacement
variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

private theorem action_injective (ρ : Representation (ZMod 2) A E) (g : A) :
    Function.Injective (ρ g) := by
  intro v w h
  have he := congrArg (ρ g⁻¹) h
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
    map_one, Module.End.one_apply] using he

private theorem dim_one_trivial (ρ : Representation (ZMod 2) A E)
    (hd : Module.finrank (ZMod 2) E = 1) (g : A) (v : E) : ρ g v = v := by
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd (ρ g)
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with h0 | h1
  · have hz : ρ g = 0 := by simpa [h0] using hc
    have hv0 := action_injective ρ g (show ρ g v = ρ g 0 by rw [hz]; rfl)
    rw [hv0, map_zero]
  · simpa [h1] using DFunLike.congr_fun hc v

private theorem add_self_zero (v : E) : v + v = 0 := by
  calc
    v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 from rfl, zero_smul]

private theorem square_eq_of_fixed_displacement (f : E →ₗ[ZMod 2] E) (v : E)
    (h : f (f v - v) = f v - v) : f (f v) = v := by
  rw [map_sub] at h
  apply sub_eq_zero.mp
  calc
    f (f v) - v = (f (f v) - f v) - (f v - v) + (f v + f v) - (v + v) := by abel
    _ = 0 := by simp only [h, sub_self, add_self_zero]

/-- A reducible two-dimensional binary representation has image of exponent two. -/
private theorem reducible_two_square [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) A E) (hd : Module.finrank (ZMod 2) E = 2)
    (S : Subrepresentation ρ) (hS0 : S ≠ ⊥) (hSt : S ≠ ⊤) (g : A) (v : E) :
    ρ g (ρ g v) = v := by
  have hs0 : S.toSubmodule ≠ ⊥ := fun h => hS0 (Subrepresentation.toSubmodule_injective h)
  have hst : S.toSubmodule ≠ ⊤ := fun h => hSt (Subrepresentation.toSubmodule_injective h)
  have hs1 : Module.finrank (ZMod 2) S.toSubmodule = 1 := by
    have hp : Module.finrank (ZMod 2) S.toSubmodule ≠ 0 :=
      fun he => hs0 (Submodule.finrank_eq_zero.mp he)
    have hl := Submodule.finrank_lt hst
    omega
  have hq1 : Module.finrank (ZMod 2) (E ⧸ S.toSubmodule) = 1 := by
    have he := Submodule.finrank_quotient_add_finrank S.toSubmodule
    omega
  have hq := dim_one_trivial S.quotientRepresentation hq1 g (S.toSubmodule.mkQ v)
  have hv : ρ g v - v ∈ S := (Submodule.Quotient.eq S.toSubmodule).mp hq
  apply square_eq_of_fixed_displacement
  exact congrArg Subtype.val (dim_one_trivial S.toRepresentation hs1 g ⟨_, hv⟩)

/-- Fixing one layer and acting with exponent two on the quotient gives a two-group. -/
private theorem two_of_fixed_and_quotient_square
    (ρ : Representation (ZMod 2) A E) (hfaith : Function.Injective ρ)
    (W : Subrepresentation ρ) (hfix : ∀ g (v : W), ρ g v = v)
    (hsquare : ∀ g v, W.quotientRepresentation g (W.quotientRepresentation g v) = v) :
    IsPGroup 2 A := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro g
  refine ⟨2, ?_⟩
  apply hfaith
  ext v
  rw [map_one, Module.End.one_apply]
  have hd : ρ (g * g) v - v ∈ W := by
    apply (Submodule.Quotient.eq W.toSubmodule).mp
    have hh := hsquare g (W.toSubmodule.mkQ v)
    change W.toSubmodule.mkQ (ρ g (ρ g v)) = W.toSubmodule.mkQ v at hh
    simpa only [map_mul, Module.End.mul_apply, Submodule.mkQ_apply] using hh
  have he := square_eq_of_fixed_displacement (ρ (g * g)) v (hfix (g * g) ⟨_, hd⟩)
  simpa only [show (2 : ℕ)^2 = 4 from rfl, show g ^ 4 = (g * g) * (g * g) by simp [pow_succ, mul_assoc],
    map_mul, Module.End.mul_apply] using he

/-- An odd marked action fixing the lower layer forces an irreducible binary head. -/
theorem quotient_irreducible_of_marked
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) A E) (hfaith : Function.Injective ρ)
    (W : Subrepresentation ρ)
    (hd : Module.finrank (ZMod 2) (E ⧸ W.toSubmodule) = 2)
    (R : Subgroup A) (hR : ¬ IsPGroup 2 R)
    (hfix : ∀ g ∈ R, ∀ v : W, ρ g v = v) : W.quotientRepresentation.IsIrreducible := by
  let : Nontrivial (E ⧸ W.toSubmodule) := Module.nontrivial_of_finrank_pos
    (R := ZMod 2) (M := E ⧸ W.toSubmodule) (by omega)
  refine ⟨fun S => ?_⟩
  by_cases hS0 : S = ⊥
  · exact Or.inl hS0
  by_cases hSt : S = ⊤
  · exact Or.inr hSt
  apply False.elim
  apply hR
  let WR : Subrepresentation (ρ.comp R.subtype) :=
    ⟨W.toSubmodule, fun g => W.apply_mem_toSubmodule g⟩
  apply two_of_fixed_and_quotient_square (ρ.comp R.subtype)
    (hfaith.comp R.subtype_injective) WR
  · intro g v
    exact hfix g g.property v
  · intro g v
    exact reducible_two_square W.quotientRepresentation hd S hS0 hSt g v

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.RadicalPlacement

open BinaryLinear
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry
variable {A U : Type*} [Group A] [Finite A] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) A U)

/-- The actual seed action and its marked odd subgroup place the intrinsic
two-core in the radical of the chosen natural head plane. -/
theorem seed_core_maps_radical (s : GeneratingSeed ρ) (W : Subrepresentation ρ)
    (hW : W ≠ ⊤) (eH : A ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] ChiefFactors.NaturalSpace)
    (he : ∀ g u, e (W.quotientRepresentation g u) = eH g (e u))
    (R : Subgroup A) (hRP : R ≤ s.parabolic) (hR : ¬ IsPGroup 2 R)
    (hRfix : ∀ g ∈ R, ∀ v ∈ s.space.toSubmodule, ρ g v = v) :
    (s.parabolic.pCoreIn 2).map eH.toMonoidHom ≤ radical (headPlane ρ s W e) := by
  let τ : Representation (ZMod 2) s.parabolic ChiefFactors.NaturalSpace :=
    (ChiefFactors.naturalAction eH).comp s.parabolic.subtype
  let N : Subrepresentation τ := {
    toSubmodule := headPlane ρ s W e
    apply_mem_toSubmodule g v hv :=
      ((headPlane_stable ρ s W eH e he (mem_map_of_mem _ g.property)) v).mpr hv }
  have hτ : Function.Injective τ := by
    intro a b hab
    apply Subtype.ext
    apply eH.injective
    apply LinearEquiv.ext
    intro v
    exact DFunLike.congr_fun hab v
  have hd : Module.finrank (ZMod 2) (ChiefFactors.NaturalSpace ⧸ N.toSubmodule) = 2 := by
    have hp := headPlane_finrank ρ s W hW e
    have hsum := Submodule.finrank_quotient_add_finrank N.toSubmodule
    have hn : Module.finrank (ZMod 2) ChiefFactors.NaturalSpace = 4 := by simp [ChiefFactors.NaturalSpace]
    change Module.finrank (ZMod 2) N.toSubmodule = 2 at hp
    omega
  have hnr : ¬ IsPGroup 2 (R.subgroupOf s.parabolic) :=
    fun h => hR (h.of_equiv (subgroupOfEquivOfLe hRP))
  have hfix : ∀ g ∈ R.subgroupOf s.parabolic, ∀ v : N, τ g v = v := by
    intro g hg v
    obtain ⟨u, hu⟩ := v.property
    change headSeedMap ρ s W e u = v.val at hu
    change eH g v.val = v.val
    rw [← hu]
    change eH g (e (W.toSubmodule.mkQ u)) = e (W.toSubmodule.mkQ u)
    rw [← he]
    change e (W.toSubmodule.mkQ (ρ g u)) = _
    rw [hRfix g hg u u.property]
  let : N.quotientRepresentation.IsIrreducible :=
    RadicalPlacement.quotient_irreducible_of_marked τ hτ N hd _ hnr hfix
  have hk := normal_p_subgroup_le_ker N.quotientRepresentation (pCore 2 s.parabolic) pCore_isPGroup
  let : FiniteDimensional (ZMod 2) s.space.toSubmodule :=
    Module.finite_of_finrank_pos (by rw [s.dim_two]; decide)
  let : s.space.toRepresentation.IsIrreducible :=
    (Subrepresentation.irreducible_iff_isAtom s.space).mpr s.irreducible
  have hs := normal_p_subgroup_le_ker s.space.toRepresentation (pCore 2 s.parabolic) pCore_isPGroup
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rintro v ⟨u, rfl⟩
    change eH a (e (W.toSubmodule.mkQ u)) = e (W.toSubmodule.mkQ u)
    rw [← he]
    change e (W.toSubmodule.mkQ (ρ a u)) = _
    have hsu := congrArg Subtype.val (DFunLike.congr_fun (hs ha) u)
    change ρ a u = u.val at hsu
    rw [hsu]
  · intro v
    exact (Submodule.Quotient.eq N.toSubmodule).mp
      (DFunLike.congr_fun (hk ha) (N.toSubmodule.mkQ v))
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry

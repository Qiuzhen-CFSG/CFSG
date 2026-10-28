module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Torus
public import Theory.SpecificGroups.SymplecticFour.RootTori
public import Mathlib.GroupTheory.PGroup
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Lattice
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Parabolics
public import Theory.GroupTheory.SubgroupCenterImageBound
/-!
# Central involutions and odd square orbits in the symplectic Sylow

The explicit four-root multiplication formula identifies the nonidentity
squares with the central elements having two nonzero root coordinates.
The diagonal Cartan is transitive on this set, of odd size (q - 1)².
Consequently any two-group of automorphisms of the Sylow fixes an element
in the Cartan orbit of each such square. This requires only automorphisms
of the Sylow and does not assume an extension to the full matrix group.

The remaining central elements lie in the two actual local centers; the
exceptional graph automorphism identifies the short-root center. Together
these calculations supply the three cases in the original ambient
characteristic-two argument of Aschbacher–Smith 5.3.3, printed p.659,
verifying the final clause of F.4.31(c), printed p.291 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
open CentralRootGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem theta_eq_one (s t : F) : theta s t = 1 ↔ s = 0 ∧ t = 0 := by
  rw [← element_zero, theta, element_eq_iff]
  simp

private theorem theta_square_iff (s t : F) :
    (∃ x : unipotent (F := F), x^2 = theta s t) ↔
      (s = 0 ∧ t = 0) ∨ (s ≠ 0 ∧ t ≠ 0) := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    rw [element_square] at hx
    have he := (element_eq_iff _ _ _ _ _ _ _ _).mp hx
    rcases eq_or_ne b 0 with rfl | hb
    · left; simpa using And.intro he.2.1.symm he.2.2.1.symm
    rcases eq_or_ne v 0 with rfl | hv
    · left; simpa using And.intro he.2.1.symm he.2.2.1.symm
    right
    exact ⟨he.2.1 ▸ mul_ne_zero (pow_ne_zero _ hb) hv,
      he.2.2.1 ▸ mul_ne_zero hb hv⟩
  · rintro (⟨rfl,rfl⟩ | ⟨hs,ht⟩)
    · exact ⟨1, by simp [theta, element_zero]⟩
    refine ⟨element (s/t) 0 0 (t^2/s), ?_⟩
    rw [element_square]
    congr 1 <;> field_simp

private theorem diagonal_orbit (s t u v : F)
    (hs : s = 0 ↔ u = 0) (ht : t = 0 ↔ v = 0) :
    ∃ b ∈ borel (F := F), b * (theta s t).val * b⁻¹ = (theta u v).val := by
  have scalar (x y : F) (hxy : x = 0 ↔ y = 0) :
      ∃ c : Fˣ, (c : F) * x = y := by
    by_cases hx : x = 0
    · exact ⟨1,by simp [hx,hxy.mp hx]⟩
    exact ⟨Units.mk0 (y/x) (div_ne_zero (mt hxy.mpr hx) hx), by simp [hx]⟩
  obtain ⟨c,hc⟩ := scalar s u hs
  obtain ⟨d,hd⟩ := scalar t v ht
  obtain ⟨a,ha⟩ := RootTori.weight_surjective (F := F) 0 c
  have ha' : a^2 = c := by simpa [RootTori.weight] using ha
  refine ⟨diagonalTorusHom (a,a⁻¹*d),diagonalTorus_mem_borel _ _,?_⟩
  have hh := diagonalTorus_weights (a,a⁻¹*d) s t
  rw [show (a:F)^2*s=u by rw [←Units.val_pow_eq_pow_val,ha']; exact hc,
    show (a:F)*((a⁻¹*d : Fˣ):F)*t=v by simpa using hd] at hh
  simpa only [parameter_apply, theta_val, toAdd_ofAdd] using hh

/-- The intrinsic nonidentity square set, preserved by every Sylow automorphism. -/
private def nonidentitySquares (U : Type*) [Group U] := {x : U // x ≠ 1 ∧ ∃ y : U, y^2=x}

private theorem square_coordinates (x : nonidentitySquares (unipotent (F := F))) :
    ∃ s t : F, s ≠ 0 ∧ t ≠ 0 ∧ x.val = theta s t := by
  obtain ⟨y,hy⟩ := x.property.2
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
  rw [element_square] at hy
  have hn : ¬ (b^2*v = 0 ∧ b*v = 0) := by
    intro hz
    exact x.property.1 (hy.symm.trans ((theta_eq_one _ _).mpr hz))
  have hh := (theta_square_iff (b^2*v) (b*v)).mp ⟨element b u w v,element_square _ _ _ _⟩
  exact ⟨b^2*v,b*v,(hh.resolve_left hn).1,(hh.resolve_left hn).2,hy.symm⟩

private def squareEquiv : (Fˣ × Fˣ) ≃ nonidentitySquares (unipotent (F := F)) :=
  Equiv.ofBijective (fun x => ⟨theta x.1 x.2,
    fun h => x.1.ne_zero ((theta_eq_one _ _).mp h).1,
    (theta_square_iff _ _).mpr (Or.inr ⟨x.1.ne_zero,x.2.ne_zero⟩)⟩) (by
      constructor
      · intro x y h
        have he := (element_eq_iff _ _ _ _ _ _ _ _).mp (congrArg Subtype.val h)
        exact Prod.ext (Units.ext he.2.1) (Units.ext he.2.2.1)
      · intro x
        obtain ⟨s,t,hs,ht,hx⟩ := square_coordinates x
        exact ⟨(Units.mk0 s hs,Units.mk0 t ht),Subtype.ext hx.symm⟩)

/-- Every nonidentity square in the native Sylow has a Borel-conjugate fixed
by any two-group of automorphisms of that Sylow. -/
theorem square_conjugate_fixed {A : Type*} [Group A] (hA : IsPGroup 2 A)
    (ρ : A →* MulAut (unipotent (F := F)))
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    (z : unipotent (F := F)) (hz : z ≠ 1) (hsq : ∃ y, y^2=z) :
    ∃ b ∈ borel (F := F), ∃ w : unipotent (F := F),
      b*z.val*b⁻¹=w.val ∧ ∀ a : A, ρ a w = w := by
  let X := nonidentitySquares (unipotent (F := F))
  let : MulAction A X := {
    smul a x := ⟨ρ a x.val,
      (ρ a).map_ne_one_iff.mpr x.property.1,
      by obtain ⟨y,hy⟩ := x.property.2
         exact ⟨ρ a y, by rw [←map_pow,hy]⟩⟩
    one_smul x := Subtype.ext (show ρ 1 x.val = x.val by rw [map_one]; rfl)
    mul_smul a b x := Subtype.ext (show ρ (a*b) x.val = ρ a (ρ b x.val) by rw [map_mul]; rfl) }
  have hc : Nat.card X = (2^n-1)^2 := by
    rw [← Nat.card_congr (squareEquiv (F := F)),Nat.card_prod,Nat.card_units,hF,pow_two]
  have hodd : Odd (Nat.card X) := by
    rw [hc]
    exact (Nat.Even.sub_odd (Nat.one_le_pow n 2 (by decide))
      (even_two.pow_of_ne_zero (by omega : n ≠ 0)) odd_one).pow
  obtain ⟨x,hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card X
    (by simpa only [←even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hodd))
  obtain ⟨s,t,hs,ht,he⟩ := square_coordinates (⟨z,hz,hsq⟩ : X)
  change z = theta s t at he
  obtain ⟨u,v,hu,hv,hxv⟩ := square_coordinates x
  obtain ⟨b,hb,hbuv⟩ := diagonal_orbit s t u v (by simp [hs,hu]) (by simp [ht,hv])
  refine ⟨b,hb,x.val,?_,?_⟩
  · simpa only [he,hxv] using hbuv
  · intro a
    exact congrArg Subtype.val (hx a)

private theorem short_root_central {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (t : F) : Representation.OneCohomology.SymplecticFour.rootElement 4 t ∈
      (center (planeLocal (F := F))).map planeLocal.subtype := by
  let a := DiagramAutomorphisms.ExceptionalGraph.graphAut (F := F)
  let e : pointParabolic (F := F) ≃* planeParabolic := (a.subgroupMap pointParabolic).trans
    (MulEquiv.subgroupCongr DiagramAutomorphisms.ExceptionalGraph.graphAut_map_point)
  have hmap : (pointLocal (F := F)).map a.toMonoidHom = planeLocal := by
    rw [←pointParabolic_solvableResidual_eq hF hn,map_map]
    change (solvableResidual (pointParabolic (F := F))).map
      (planeParabolic.subtype.comp e.toMonoidHom) = planeLocal
    rw [←map_map,map_solvableResidual_eq e.toMonoidHom e.surjective]
    exact planeParabolic_solvableResidual_eq hF hn
  have hc := map_subgroup_center_eq a.toMonoidHom a.injective (pointLocal (F := F))
  rw [hmap] at hc
  rw [←hc]
  have hr : Representation.OneCohomology.SymplecticFour.rootElement 0 t ∈
      (center (pointLocal (F := F))).map pointLocal.subtype := by
    rw [PointRadicalAction.center_eq_root hF hn]
    exact (RootSubgroup.mem_group_iff 0 _).mpr ⟨t,rfl⟩
  have he : a (Representation.OneCohomology.SymplecticFour.rootElement 0 t) =
      Representation.OneCohomology.SymplecticFour.rootElement 4 t := by
    simp [a,DiagramAutomorphisms.ExceptionalGraph.graphAut_apply,
      DiagramAutomorphisms.ExceptionalGraph.graphEnd_root,
      DiagramAutomorphisms.ExceptionalGraph.rootPermutation,
      DiagramAutomorphisms.ExceptionalGraph.rootParameter]
  exact he ▸ mem_map_of_mem a.toMonoidHom hr

/-- Each central Sylow element lies in one of the two actual local centers
or is a square in that Sylow. This retains the native root embeddings. -/
theorem center_local_or_square {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (z : unipotent (F := F)) (hz : z ∈ center (unipotent (F := F))) :
    z.val ∈ (center (pointLocal (F := F))).map pointLocal.subtype ∨
      z.val ∈ (center (planeLocal (F := F))).map planeLocal.subtype ∨
      ∃ y : unipotent (F := F), y^2=z := by
  obtain ⟨⟨s,t⟩,he⟩ := (theta_range (F := F)).ge hz
  change theta s.toAdd t.toAdd = z at he
  rw [←he]
  by_cases ht : t.toAdd=0
  · left
    rw [ht,theta_val,RootSubgroup.element_zero,mul_one,PointRadicalAction.center_eq_root hF hn]
    exact (RootSubgroup.mem_group_iff 0 _).mpr ⟨s.toAdd,rfl⟩
  right
  by_cases hs : s.toAdd=0
  · left
    rw [hs,theta_val,RootSubgroup.element_zero,one_mul]
    exact short_root_central hF hn t.toAdd
  right
  exact (theta_square_iff _ _).mpr (Or.inr ⟨hs,ht⟩)
end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder



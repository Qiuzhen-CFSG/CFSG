module

public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.Basic

/-!
# Borel cocycles for fixed-Sylow alignment

For the actual graph-field involution over a field of order `2^(2*m+1)`,
every cocycle in the standard symplectic Borel is a coboundary in that Borel.
This is the local descent needed to correct a Sylow conjugator.

In unipotent coordinates `(b,u,w,v)`, the cocycle equation first determines
`v` from `b`. Twisting by the root with parameter `b` leaves the central pair
`(u+b*w,w)`. The same equation determines its second coordinate from its
first, so a central root removes it. For a Borel cocycle `g`, twisting by
`g^((q-2)/2)` yields `g^(q-1)`, which lies in both determinant kernels.
The unipotent calculation then finishes the descent.

Source: the fixed-group geometry used for Aschbacher--Smith E.1.14(1),
printed p.214, and 16.1.4(7), printed p.1171 of `refs/quasithin.pdf`.
The explicit minors and root coordinates are those of GLS3, Theorem 2.5.1,
already constructed in `ExceptionalGraph.Construction` and
`Sylow.CentralRootGeometry.Coordinates`. No global cocycle descent is used.
-/

public section
open Matrix Subgroup Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms GraphFieldFixedResidual ExceptionalGraph CentralRootGeometry
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry.Alignment.BorelCocycle
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private lemma graph_element (m : ℕ) (b u w v : F) :
    graphFieldAut m (element b u w v).val =
      (element (iterateFrobeniusEquiv F 2 m v)
        (iterateFrobeniusEquiv F 2 m (b*v*w+u*v+w^2))
        (iterateFrobeniusEquiv F 2 m (b^2*v+b*w+u))
        (iterateFrobeniusEquiv F 2 m (b^2))).val := by
  apply Subtype.ext
  rw [graphFieldAut_apply, element_matrix, element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [graphMatrix, minor, first, second, Matrix.fromBlocks, map_add, map_mul, map_pow] <;>
    (ring_nf; all_goals simp [CharTwo.two_eq_zero])

/-- The actual graph-field representative preserves the standard unipotent subgroup. -/
theorem graphFieldAut_map_unipotent (m : ℕ) :
    unipotent.map (graphFieldAut (F := F) m).toMonoidHom = unipotent := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨⟨b,u,w,v⟩, he⟩ := element_surjective (⟨g,hg⟩ : unipotent)
    have he' : (element b u w v).val = g := congrArg Subtype.val he
    change graphFieldAut m g ∈ unipotent
    rw [← he', graph_element]
    exact (element _ _ _ _).property
  · rw [Subgroup.card_map_of_injective (graphFieldAut m).injective]

/-- Every cocycle in the standard unipotent subgroup is a coboundary there.
The root coordinates successively remove the two noncentral and the two
central parameters. -/
theorem unipotent_cocycle_coboundary (m : ℕ) (hF : Nat.card F = 2 ^ (2*m+1))
    (g : Sp F) (hg : g ∈ unipotent) (hc : g * graphFieldAut m g = 1) :
    ∃ d : Sp F, d ∈ unipotent ∧ g = d * (graphFieldAut m d)⁻¹ := by
  let a := graphFieldAut (F := F) m
  let σ := iterateFrobeniusEquiv F 2 m
  have haa (x : Sp F) : a (a x) = x :=
    congrArg (fun t : MulAut (Sp F) => t x) (graphFieldAut_sq m hF)
  obtain ⟨⟨b,u,w,v⟩, he⟩ := element_surjective (⟨g,hg⟩ : unipotent)
  have he' : (element b u w v).val = g := congrArg Subtype.val he
  subst g
  have hv : v = σ (b^2) := by
    rw [graph_element] at hc
    change ((element b u w v * element (σ v) (σ (b*v*w+u*v+w^2))
      (σ (b^2*v+b*w+u)) (σ (b^2))).val) = _ at hc
    have hc' : element b u w v * element (σ v) (σ (b*v*w+u*v+w^2))
        (σ (b^2*v+b*w+u)) (σ (b^2)) = 1 := Subtype.ext hc
    rw [element_mul, ← element_zero, element_eq_iff] at hc'
    exact (CharTwo.add_eq_zero.mp hc'.2.2.2)
  let x : Sp F := (element b 0 0 0).val
  let z : Sp F := (theta (u+b*w) w).val
  have hxx : x*x=1 := by
    change ((element b 0 0 0 * element b 0 0 0).val) = 1
    simp [element_mul, element_zero, CharTwo.add_self_eq_zero]
  have hxinv : x⁻¹=x := (inv_eq_iff_mul_eq_one.mpr hxx)
  have hz : z = x⁻¹ * (element b u w v).val * a x := by
    rw [hxinv]
    dsimp [x, a]
    rw [graph_element]
    change (theta (u+b*w) w).val =
      ((element b 0 0 0 * element b u w v *
      element (σ 0) (σ (b*0*0+0*0+0^2)) (σ (b^2*0+b*0+0)) (σ (b^2))).val)
    simp [theta, element_mul, ← hv, CharTwo.add_self_eq_zero]
  have hzc : z * a z = 1 := by
    rw [hz, map_mul, map_mul, map_inv, haa]
    change x⁻¹ * (element b u w v).val * a x *
      ((a x)⁻¹ * a (element b u w v).val * x) = 1
    calc
      _ = x⁻¹ * ((element b u w v).val * a (element b u w v).val) * x := by group
      _ = 1 := by rw [hc]; group
  have hw : w = σ (u+b*w) := by
    dsimp [z, theta, a] at hzc
    rw [graph_element] at hzc
    have hc' : element 0 (u+b*w) w 0 *
        element (σ 0) (σ (0*0*w+(u+b*w)*0+w^2))
        (σ (0^2*0+0*w+(u+b*w))) (σ (0^2)) = 1 := Subtype.ext hzc
    simp only [map_zero, zero_mul, mul_zero, zero_add, add_zero, zero_pow (by decide : 2 ≠ 0),
      element_mul, ← element_zero, element_eq_iff] at hc'
    exact CharTwo.add_eq_zero.mp hc'.2.2.1
  let y : Sp F := (theta (u+b*w) 0).val
  have hy : z = y * (a y)⁻¹ := by
    have hay : a y = (theta 0 (σ (u+b*w))).val := by
      dsimp [a, y, theta]
      rw [graph_element]
      simp only [mul_zero, add_zero, zero_add, map_zero, zero_pow (by decide : 2 ≠ 0)]
      rfl
    have hinv : ((theta 0 (σ (u+b*w))).val : Sp F)⁻¹ =
        (theta 0 (σ (u+b*w))).val := by
      apply inv_eq_iff_mul_eq_one.mpr
      change ((theta 0 (σ (u+b*w)) * theta 0 (σ (u+b*w))).val) = 1
      rw [theta_add]
      simp only [CharTwo.add_self_eq_zero, theta, element_zero, coe_one]
    rw [hay, hinv]
    change (theta (u+b*w) w).val =
      ((theta (u+b*w) 0 * theta 0 (σ (u+b*w))).val)
    rw [theta_add, add_zero, zero_add]
    exact congrArg (fun t => (theta (u+b*w) t).val) hw
  refine ⟨x*y, unipotent.mul_mem (element b 0 0 0).property (theta (u+b*w) 0).property, ?_⟩
  have heq := hz.symm.trans hy
  change (element b u w v).val = x*y*(a (x*y))⁻¹
  rw [map_mul]
  calc
    (element b u w v).val = x * (x⁻¹ * (element b u w v).val * a x) * (a x)⁻¹ := by group
    _ = x * (y * (a y)⁻¹) * (a x)⁻¹ := by rw [heq]
    _ = _ := by group

omit [Finite F] [CharP F 2] in
private lemma borel_power_mem_unipotent (g : Sp F) (hg : g ∈ borel) :
    g ^ (Nat.card F - 1) ∈ unipotent := by
  have aux (W : Submodule F (Vector F)) (hW : g ∈ stabilizer W) :
      g ^ (Nat.card F - 1) ∈ determinantKernel W := by
    apply (mem_determinantKernel_iff W _).mpr
    refine ⟨(stabilizer W).pow_mem hW _, ?_⟩
    change determinantCharacter W ((⟨g,hW⟩ : stabilizer W) ^ (Nat.card F - 1)) = 1
    rw [map_pow, ← Nat.card_units, pow_card_eq_one']
  exact ⟨aux (point F) hg.1, aux (plane F) hg.2⟩

/-- Every Borel cocycle is a Borel coboundary. An odd power kills both
determinant characters, reducing the calculation to the unipotent subgroup. -/
theorem borel_cocycle_coboundary (m : ℕ) (hF : Nat.card F = 2 ^ (2*m+1))
    (g : Sp F) (hg : g ∈ borel) (hc : g * graphFieldAut m g = 1) :
    ∃ d : Sp F, d ∈ borel ∧ g = d * (graphFieldAut m d)⁻¹ := by
  let a := graphFieldAut (F := F) m
  have hag : a g = g⁻¹ := eq_inv_of_mul_eq_one_right hc
  have haa (x : Sp F) : a (a x) = x :=
    congrArg (fun t : MulAut (Sp F) => t x) (graphFieldAut_sq m hF)
  let n := 2 ^ (2*m) - 1
  let t := g ^ n
  have hat : a t = t⁻¹ := by simp only [t, map_pow, hag, inv_pow]
  let u := t * g * (a t)⁻¹
  have hu : u = g ^ (Nat.card F - 1) := by
    have hn : 2*n+1 = Nat.card F - 1 := by
      dsimp [n]
      rw [hF, pow_succ]
      have : 0 < 2 ^ (2*m) := by positivity
      omega
    dsimp [u]
    rw [hat, inv_inv]
    dsimp [t]
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  have huc : u * a u = 1 := by
    dsimp [u]
    rw [map_mul, map_mul, map_inv, haa]
    change t * g * (a t)⁻¹ * (a t * a g * t⁻¹) = 1
    calc
      _ = t * (g * a g) * t⁻¹ := by group
      _ = 1 := by rw [hc]; group
  have huU : u ∈ unipotent := hu ▸ borel_power_mem_unipotent g hg
  obtain ⟨d, hd, he⟩ := unipotent_cocycle_coboundary m hF u huU huc
  refine ⟨t⁻¹*d, (borel (F := F)).mul_mem
    ((borel (F := F)).inv_mem ((borel (F := F)).pow_mem hg n))
    ((mem_unipotent_iff d).mp hd).1, ?_⟩
  change g = t⁻¹ * d * (a (t⁻¹*d))⁻¹
  rw [map_mul, map_inv]
  calc
    g = t⁻¹ * (t*g*(a t)⁻¹) * a t := by group
    _ = t⁻¹ * (d*(a d)⁻¹) * a t := by rw [← he]
    _ = _ := by group

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry.Alignment.BorelCocycle

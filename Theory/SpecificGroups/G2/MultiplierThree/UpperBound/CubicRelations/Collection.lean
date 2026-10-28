module

public import Theory.SpecificGroups.G2.MultiplierThree.UpperBound.OrthogonalDefect
public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.CommutingLifts

/-!
# Ternary positive-root relations after killing the orthogonal defect

For a central extension of the actual octonion G₂(3), torus-equivariant
additive sections satisfy all fifteen positive-root collection relations
if their B/D commutator is trivial. The split torus separates every commuting
pair except A/F, B/D and C/E. Weyl conjugation transports the B/D condition
to the other two pairs, without making assumptions about the kernel order.

The remaining polynomial words are proved additive and torus-equivariant;
uniqueness of normalized additive lifts identifies them with conjugated
roots. In the F/E relation, the quadratic A-coordinate is essential:
its cross term cancels the B/E interchange term because -2 = 1 in F₃.
This theorem is used by `CubicRelations` on the quotient by the cubic defect.

Source: Aschbacher–Smith I.1.4(2), printed p.408 (PDF p.419), and the
orthogonal-root strategy in GLS3 §6.3, printed pp.319–320. Unlike the
outer-action calculation there, the proof assumes no C₃ kernel. All root
coordinates, signs and Weyl maps are the attributed ATLAS octonion formulas
in the imported modules (LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
-/

@[expose] public section

open scoped commutatorElement
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicRelations
open MultiplierOrdinary MultiplierOrdinary.RootSections
variable {E : Type*} [Group E] {f : E →* Model (ZMod 3)}

private theorem weylS_rootD (t : ZMod 3) :
    weylS * rootD t * weylS⁻¹ = rootC t := by
  rw [weylS_inverse]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [weylS, weylSEquiv, weylSLinear, weylSApply,
      rootD, Explicit.rootDEquiv, Explicit.rootDLinear, Explicit.rootDApply,
      rootC, Explicit.rootCEquiv, Explicit.rootCLinear, Explicit.rootCApply] <;> ring

private theorem weylR_rootB (t : ZMod 3) :
    weylR * rootB t * weylR⁻¹ = rootA t := by
  rw [← weylR_rootA t]
  calc
    _ = (weylR * weylR) * rootA t * (weylR * weylR)⁻¹ := by group
    _ = rootA t := by rw [← pow_two, weylR_sq]; simp

private theorem x_eq_pow (L : RootSections f) (i : Fin 6) (t : ZMod 3) :
    L.x i t = L.x i 1 ^ t.val := by
  rw [← map_pow]
  congr 1
  change t = t.val • (1 : ZMod 3)
  simp

private theorem commute_of_generators (L : RootSections f) (i j : Fin 6)
    (h : Commute (L.x i 1) (L.x j 1)) (s t : ZMod 3) :
    L.x i s * L.x j t = L.x j t * L.x i s := by
  rw [x_eq_pow L i s, x_eq_pow L j t]
  exact (h.pow_pow _ _).eq

private theorem commute_of_conjugate (L : RootSections f)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (i j k l : Fin 6) (w : Model (ZMod 3)) (s t : ZMod 3)
    (hi : w * positiveRoot i s * w⁻¹ = positiveRoot k 1)
    (hj : w * positiveRoot j t * w⁻¹ = positiveRoot l 1)
    (h : Commute (L.x i s) (L.x j t)) : Commute (L.x k 1) (L.x l 1) := by
  obtain ⟨v, hv⟩ := hf w
  apply commutatorElement_eq_one_iff_mul_comm.mp
  calc
    ⁅L.x k 1, L.x l 1⁆ = ⁅v * L.x i s * v⁻¹, v * L.x j t * v⁻¹⁆ := by
      apply CentralExtension.commutator_eq_of_image_eq f hk
      · rw [map_mul, map_mul, map_inv, hv, L.project_x, L.project_x, hi]
      · rw [map_mul, map_mul, map_inv, hv, L.project_x, L.project_x, hj]
    _ = v * ⁅L.x i s, L.x j t⁆ * v⁻¹ := (conjugate_commutatorElement _ _ _).symm
    _ = 1 := by rw [h.commutator_eq]; simp

/-- All ten ordinary commuting pairs commute after killing the B/D defect. -/
private theorem commuting_of_defect_one (L : RootSections f) (hL : L.TorusEquivariant)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hd : orthogonalDefect L = 1) : L.CommutingRelations := by
  have hBD : Commute (L.x 1 1) (L.x 3 1) :=
    commutatorElement_eq_one_iff_mul_comm.mp hd
  have hAF : Commute (L.x 0 1) (L.x 5 1) :=
    commute_of_conjugate L hf hk 1 3 0 5 weylR 1 1
      (weylR_rootB 1) (weylR_rootD 1) hBD
  have hEC : Commute (L.x 4 1) (L.x 2 1) :=
    commute_of_conjugate L hf hk 1 3 4 2 weylS 1 1
      (weylS_rootB 1) (weylS_rootD 1) hBD
  have R := (model_collectionRelations (F := ZMod 3)).toCommutingRelations
  constructor
  · exact L.commute_of_torus_separates hL hf hk 1 0 (-1) 1
      (by decide) (by decide) R.ba
  · exact L.commute_of_torus_separates hL hf hk 2 0 1 (-1)
      (by decide) (by decide) R.ca
  · exact L.commute_of_torus_separates hL hf hk 2 1 1 (-1)
      (by decide) (by decide) R.cb
  · exact L.commute_of_torus_separates hL hf hk 3 0 (-1) 1
      (by decide) (by decide) R.da
  · exact commute_of_generators L 3 1 hBD.symm
  · exact L.commute_of_torus_separates hL hf hk 4 0 1 (-1)
      (by decide) (by decide) R.ea
  · exact commute_of_generators L 4 2 hEC
  · exact L.commute_of_torus_separates hL hf hk 4 3 1 (-1)
      (by decide) (by decide) R.ed
  · exact commute_of_generators L 5 0 hAF.symm
  · exact L.commute_of_torus_separates hL hf hk 5 1 (-1) (-1)
      (by decide) (by decide) R.fb

/-- The coefficients three vanish for these two remaining short-root pairs. -/
private theorem short_commuting (L : RootSections f) (hL : L.TorusEquivariant)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    (∀ d c, L.x 3 d * L.x 2 c = L.x 2 c * L.x 3 d) ∧
    (∀ z c, L.x 5 z * L.x 2 c = L.x 2 c * L.x 5 z) := by
  have R := (model_collectionRelations (F := ZMod 3)).toPolynomialRelations
  constructor
  · apply L.commute_of_torus_separates hL hf hk 3 2 (-1) 1
      (by decide) (by decide)
    intro d c
    simpa [modelRootSections, x, positiveRootHom, positiveRoot, show (3 : ZMod 3) = 0 by decide] using R.dc d c
  · apply L.commute_of_torus_separates hL hf hk 5 2 (-1) (-1)
      (by decide) (by decide)
    intro z c
    simpa [modelRootSections, x, positiveRootHom, positiveRoot, show (3 : ZMod 3) = 0 by decide] using R.fc z c

private theorem append_relation {a b c : E} (h : a * b = c) (z : E) :
    a * (b * z) = c * z := by rw [← mul_assoc, h]

private theorem collect_same (L : RootSections f) (i : Fin 6) (s t : ZMod 3) (z : E) :
    L.x i s * (L.x i t * z) = L.x i (s + t) * z := by
  rw [← mul_assoc, ← x_add]

/-- Compare a conjugated root with a genuine additive polynomial word. -/
private theorem interchange_of_word (L : RootSections f) (hL : L.TorusEquivariant)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (i j : Fin 6) (s : ZMod 3) (l m : (ZMod 3)ˣ)
    (hi : positiveWeight i l m = 1) (hj : positiveWeight j l m ≠ 1)
    (v : Multiplicative (ZMod 3) →* E)
    (hproj : ∀ t : ZMod 3, f (v (.ofAdd t)) =
      positiveRoot i s * positiveRoot j t * (positiveRoot i s)⁻¹)
    (hv : ∀ (z : E), f z = torus l m → ∀ t : ZMod 3,
      z * v (.ofAdd t) * z⁻¹ = v (.ofAdd ((positiveWeight j l m : ZMod 3) * t)))
    (t : ZMod 3) : L.x i s * L.x j t = v (.ofAdd t) * L.x i s := by
  obtain ⟨z, hz⟩ := hf (torus l m)
  have hfix : z * L.x i s * z⁻¹ = L.x i s := by
    rw [hL l m z hz, hi, Units.val_one, one_mul]
  let u := (MulAut.conj (L.x i s)).toMonoidHom.comp (L.root j)
  have hu : ∀ t : ZMod 3, z * u (.ofAdd t) * z⁻¹ =
      u (.ofAdd ((positiveWeight j l m : ZMod 3) * t)) := by
    intro t
    change z * (L.x i s * L.x j t * (L.x i s)⁻¹) * z⁻¹ = _
    calc
      _ = (z * L.x i s * z⁻¹) * (z * L.x j t * z⁻¹) *
          (z * L.x i s * z⁻¹)⁻¹ := by group
      _ = _ := by rw [hfix, hL l m z hz]; rfl
  have hp : f.comp u = f.comp v := by
    apply MonoidHom.ext
    intro a
    change f (L.x i s * L.x j a.toAdd * (L.x i s)⁻¹) = _
    rw [map_mul, map_mul, map_inv, L.project_x, L.project_x]
    exact (hproj a.toAdd).symm
  have he := hom_ext_of_scalar_equivariant hk u v hp z
    (positiveWeight j l m : ZMod 3) (fun h => hj (Units.ext h)) hu (hv z hz)
  have ht := DFunLike.congr_fun he (.ofAdd t)
  change L.x i s * L.x j t * (L.x i s)⁻¹ = v (.ofAdd t) at ht
  exact (mul_inv_eq_iff_eq_mul).mp ht

private theorem eb_relation (L : RootSections f) (hL : L.TorusEquivariant)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (R : L.CommutingRelations) (e b : ZMod 3) :
    L.x 4 e * L.x 1 b = L.x 0 (-b*e) * L.x 1 b * L.x 4 e := by
  let w := fun t : ZMod 3 => L.x 0 (-t*e) * L.x 1 t
  have hadd (s t : ZMod 3) : w (s+t) = w s * w t := by
    simp only [w, neg_add, add_mul, L.x_add, mul_assoc, append_relation (R.ba _ _)]
  let v : Multiplicative (ZMod 3) →* E := {
    toFun := fun t => w t.toAdd
    map_one' := by simp [w]
    map_mul' := fun s t => hadd s.toAdd t.toAdd }
  apply interchange_of_word L hL hf hk 4 1 e 1 (-1)
      (by decide) (by decide) v
  · intro t
    change f (w t) = _
    simp only [w, map_mul, L.project_x]
    apply (eq_mul_inv_iff_mul_eq).mpr
    exact ((model_collectionRelations (F := ZMod 3)).eb e t).symm
  · intro z hz t
    change z * (L.x 0 (-t*e) * L.x 1 t) * z⁻¹ =
      L.x 0 (-((positiveWeight (F := ZMod 3) 1 1 (-1) : ZMod 3)*t)*e) *
        L.x 1 ((positiveWeight (F := ZMod 3) 1 1 (-1) : ZMod 3)*t)
    rw [show z * (L.x 0 (-t*e) * L.x 1 t) * z⁻¹ =
      (z * L.x 0 (-t*e) * z⁻¹) * (z * L.x 1 t * z⁻¹) by group,
      hL 1 (-1) z hz, hL 1 (-1) z hz]
    dsimp [positiveWeight]
    simp

private theorem fd_relation (L : RootSections f) (hL : L.TorusEquivariant)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hdc : ∀ d c, L.x 3 d * L.x 2 c = L.x 2 c * L.x 3 d)
    (z d : ZMod 3) :
    L.x 5 z * L.x 3 d = L.x 2 (-2*d*z) * L.x 3 d * L.x 5 z := by
  let w := fun t : ZMod 3 => L.x 2 (-2*t*z) * L.x 3 t
  have hadd (s t : ZMod 3) : w (s+t) = w s * w t := by
    simp only [w, mul_add, add_mul, L.x_add, mul_assoc, append_relation (hdc _ _)]
  let v : Multiplicative (ZMod 3) →* E := {
    toFun := fun t => w t.toAdd
    map_one' := by simp [w]
    map_mul' := fun s t => hadd s.toAdd t.toAdd }
  apply interchange_of_word L hL hf hk 5 3 z (-1) (-1)
      (by decide) (by decide) v
  · intro t
    change f (w t) = _
    simp only [w, map_mul, L.project_x]
    apply (eq_mul_inv_iff_mul_eq).mpr
    simpa [modelRootSections, x, positiveRootHom, positiveRoot,
      show (3 : ZMod 3) = 0 by decide] using
      ((model_collectionRelations (F := ZMod 3)).fd z t).symm
  · intro a ha t
    change a * (L.x 2 (-2*t*z) * L.x 3 t) * a⁻¹ =
      L.x 2 (-2*((positiveWeight (F := ZMod 3) 3 (-1) (-1) : ZMod 3)*t)*z) *
        L.x 3 ((positiveWeight (F := ZMod 3) 3 (-1) (-1) : ZMod 3)*t)
    rw [show a * (L.x 2 (-2*t*z) * L.x 3 t) * a⁻¹ =
      (a * L.x 2 (-2*t*z) * a⁻¹) * (a * L.x 3 t * a⁻¹) by group,
      hL (-1) (-1) a ha, hL (-1) (-1) a ha]
    dsimp [positiveWeight]
    simp

private theorem fe_relation (L : RootSections f) (hL : L.TorusEquivariant)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (R : L.CommutingRelations)
    (hdc : ∀ d c, L.x 3 d * L.x 2 c = L.x 2 c * L.x 3 d)
    (heb : ∀ e b, L.x 4 e * L.x 1 b = L.x 0 (-b*e) * L.x 1 b * L.x 4 e)
    (z e : ZMod 3) :
    L.x 5 z * L.x 4 e =
      L.x 0 (-e^2*z^3) * L.x 1 (-e*z^3) * L.x 2 (e*z^2) *
        L.x 3 (-e*z) * L.x 4 e * L.x 5 z := by
  let w := fun t : ZMod 3 => L.x 0 (-t^2*z^3) * L.x 1 (-t*z^3) *
    L.x 2 (t*z^2) * L.x 3 (-t*z) * L.x 4 t
  have hadd (s t : ZMod 3) : w (s+t) = w s * w t := by
    simp only [w, mul_assoc, append_relation (R.ba _ _), append_relation (R.ca _ _),
      append_relation (R.cb _ _), append_relation (R.da _ _), append_relation (R.db _ _),
      append_relation (hdc _ _), append_relation (R.ea _ _), append_relation (heb _ _),
      append_relation (R.ec _ _), append_relation (R.ed _ _), collect_same, ← x_add]
    repeat' first
      | apply congrArg₂ (fun a b : E => a * b)
      | apply congrArg (L.x _)
    all_goals ring_nf
    all_goals simp [show (2 : ZMod 3) = -1 by decide]
  let v : Multiplicative (ZMod 3) →* E := {
    toFun := fun t => w t.toAdd
    map_one' := by simp [w]
    map_mul' := fun s t => hadd s.toAdd t.toAdd }
  apply interchange_of_word L hL hf hk 5 4 z (-1) (-1) (by decide) (by decide) v
  · intro t
    change f (w t) = _
    simp only [w, map_mul, L.project_x]
    apply (eq_mul_inv_iff_mul_eq).mpr
    exact ((model_collectionRelations (F := ZMod 3)).fe z t).symm
  · intro a ha t
    change (MulAut.conj a) (w t) = w ((positiveWeight (F := ZMod 3) 4 (-1) (-1) : ZMod 3)*t)
    dsimp only [w]
    simp only [map_mul, MulAut.conj_apply, hL (-1) (-1) a ha]
    dsimp [positiveWeight]
    simp

/-- In a central extension with trivial orthogonal defect, torus-normalized
root sections satisfy every literal positive-root relation. -/
theorem collection_of_defect_one (L : RootSections f) (hL : L.TorusEquivariant)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hd : orthogonalDefect L = 1) : L.CollectionRelations := by
  have R := commuting_of_defect_one L hL hf hk hd
  obtain ⟨hdc, hfc⟩ := short_commuting L hL hf hk
  have heb := eb_relation L hL hf hk R
  have hfd := fd_relation L hL hf hk hdc
  have hfe := fe_relation L hL hf hk R hdc heb
  refine ⟨R, ?_⟩
  constructor
  · intro d c
    simpa [show (3 : ZMod 3) = 0 by decide] using hdc d c
  · exact heb
  · intro z c
    simpa [show (3 : ZMod 3) = 0 by decide] using hfc z c
  · intro z d
    simpa [show (3 : ZMod 3) = 0 by decide] using hfd z d
  · exact hfe

end Atlas.G2.FiniteCover.MultiplierThree.CubicRelations
end

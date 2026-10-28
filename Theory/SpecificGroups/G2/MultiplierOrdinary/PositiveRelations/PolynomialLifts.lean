module
public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.TorusEquivariance
public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.ModelRelations

/-!
# Polynomial positive-root relations in central extensions of G₂

For a finite field of order greater than four, torus-equivariant additive
sections of the six actual roots satisfy the five polynomial interchange
relations, assuming the ten commuting relations. This discharges the
polynomial family of the collection interface on the given central extension.

We first prove each candidate conjugation word additive. The DC, EB and FC
words use commuting pairs only. For FD, collecting with DC contributes
`-6*s*t*z` to the A-coordinate. For FE, EB contributes `s*t*z^3` and DC
contributes `-3*s*t*z^3`, giving the required quadratic correction. Thus the
quadratic and cubic words define homomorphisms, rather than assuming this.

Conjugation and its candidate word have equal projections by the actual
model relations. A torus fixing the conjugating root scales both homomorphisms
by a common nonidentity scalar, so central-kernel uniqueness identifies them.
The tori are `(c,1)` for DC, `(c^2,c)` for EB, and `(c,c)` for FC, FD and FE.
The field-size hypothesis supplies a unit with `c^3 ≠ 1`.

The final consumer combines these equations with the supplied commuting
family and applies collection to the literal six-root product. Establishing
the commuting family and the final multiplier exclusions remains with the
source assembly; neither is assumed through a compatibility hypothesis here.

Source: Aschbacher–Smith I.1.3–I.1.4 (PDF pp.418–419), in the G₂ ranges of
A.2.2–A.2.4 (PDF p.44), referring to GLS III §6.1. Root order, signs and torus
characters are those of the attributed ATLAS octonion model imported through
`ModelRelations` and `TorusEquivariance`; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section
namespace Atlas.G2.MultiplierOrdinary.RootSections
variable {F E : Type*} [Field F] [Group E] {f : E →* Model F}

private theorem compare_word (L : RootSections f)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hL : L.TorusEquivariant) (i j : Fin 6) (s : F) (l m : Fˣ)
    (hfix : positiveWeight i l m = 1)
    (hmove : (positiveWeight j l m : F) ≠ 1)
    (w : F → E) (hzero : w 0 = 1)
    (hadd : ∀ t u, w (t+u) = w t * w u)
    (hproj : ∀ t, positiveRoot i s * positiveRoot j t = f (w t) * positiveRoot i s)
    (hweight : ∀ a, f a = torus l m → ∀ t,
      a * w t * a⁻¹ = w ((positiveWeight j l m : F) * t)) :
    ∀ t, L.x i s * L.x j t = w t * L.x i s := by
  obtain ⟨a, ha⟩ := hf (torus l m)
  let u : Multiplicative F →* E :=
    (MulAut.conj (L.x i s)).toMonoidHom.comp (L.root j)
  let v : Multiplicative F →* E := {
    toFun := fun t => w t.toAdd
    map_one' := hzero
    map_mul' := fun t u => hadd t.toAdd u.toAdd }
  have huv : u = v := hom_ext_of_scalar_equivariant hk u v (by
    apply MonoidHom.ext
    intro t
    change f (L.x i s * L.x j t.toAdd * (L.x i s)⁻¹) = f (w t.toAdd)
    rw [map_mul, map_mul, map_inv, L.project_x, L.project_x]
    exact (eq_mul_inv_iff_mul_eq.mpr (hproj t.toAdd).symm).symm)
    a (positiveWeight j l m : F) hmove (by
      intro t
      change (MulAut.conj a) (L.x i s * L.x j t * (L.x i s)⁻¹) = _
      rw [map_mul, map_mul, map_inv]
      change (a * L.x i s * a⁻¹) * (a * L.x j t * a⁻¹) *
        (a * L.x i s * a⁻¹)⁻¹ = _
      rw [hL l m a ha i s, hL l m a ha j t, hfix]
      simp only [Units.val_one, one_mul]
      rfl)
    (hweight a ha)
  intro t
  have ht := DFunLike.congr_fun huv (.ofAdd t)
  change L.x i s * L.x j t * (L.x i s)⁻¹ = w t at ht
  exact (mul_inv_eq_iff_eq_mul.mp ht)

private theorem append_relation {a b c : E} (h : a * b = c) (z : E) :
    a * (b * z) = c * z := by rw [← mul_assoc, h]

private theorem collect_same (L : RootSections f) (i : Fin 6) (s t : F) (z : E) :
    L.x i s * (L.x i t * z) = L.x i (s+t) * z := by
  rw [← mul_assoc, ← x_add]

private theorem dc_lift (L : RootSections f)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hL : L.TorusEquivariant) (hC : L.CommutingRelations)
    (c : Fˣ) (hc : (c : F) ≠ 1) (d : F) :
    ∀ t, L.x 3 d * L.x 2 t = L.x 0 (3*t*d) * L.x 2 t * L.x 3 d := by
  apply compare_word L hf hk hL 3 2 d c 1 (by simp [positiveWeight])
    (by simpa [positiveWeight] using hc) (fun t => L.x 0 (3*t*d) * L.x 2 t)
  · simp
  · intro s t
    simp only [mul_assoc, append_relation (hC.ca _ _), collect_same, ← x_add]
    repeat' first
      | apply congrArg₂ (fun a b : E => a * b)
      | apply congrArg (L.x _)
    all_goals ring
  · intro t
    simp only [map_mul, L.project_x]
    simpa only [modelRootSections, x, positiveRootHom, MonoidHom.coe_mk,
      OneHom.coe_mk, toAdd_ofAdd] using
      (model_collectionRelations (F := F)).dc d t
  · intro a ha t
    change (MulAut.conj a) (L.x 0 (3*t*d) * L.x 2 t) = _
    rw [map_mul]
    change (a * L.x 0 (3*t*d) * a⁻¹) * (a * L.x 2 t * a⁻¹) = _
    rw [hL c 1 a ha, hL c 1 a ha]
    simp [positiveWeight]
    repeat' first
      | apply congrArg₂ (fun a b : E => a * b)
      | apply congrArg (L.x _)
    all_goals ring

private theorem eb_lift (L : RootSections f)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hL : L.TorusEquivariant) (hC : L.CommutingRelations)
    (c : Fˣ) (hc : (c : F)^3 ≠ 1) (e : F) :
    ∀ t, L.x 4 e * L.x 1 t = L.x 0 (-t*e) * L.x 1 t * L.x 4 e := by
  have hw : positiveWeight 1 (c^2) c = c^3 := by
    simp [positiveWeight, pow_succ, mul_assoc]
  apply compare_word L hf hk hL 4 1 e (c^2) c (by simp [positiveWeight])
    (by simpa only [hw, Units.val_pow_eq_pow_val] using hc)
    (fun t => L.x 0 (-t*e) * L.x 1 t)
  · simp
  · intro s t
    simp only [mul_assoc, append_relation (hC.ba _ _), collect_same, ← x_add]
    repeat' first
      | apply congrArg₂ (fun a b : E => a * b)
      | apply congrArg (L.x _)
    all_goals ring
  · intro t
    simp only [map_mul, L.project_x]
    simpa only [modelRootSections, x, positiveRootHom, MonoidHom.coe_mk,
      OneHom.coe_mk, toAdd_ofAdd] using
      (model_collectionRelations (F := F)).eb e t
  · intro a ha t
    change (MulAut.conj a) (L.x 0 (-t*e) * L.x 1 t) = _
    rw [map_mul]
    change (a * L.x 0 (-t*e) * a⁻¹) * (a * L.x 1 t * a⁻¹) = _
    rw [hL (c^2) c a ha, hL (c^2) c a ha, hw]
    simp only [positiveWeight]
    dsimp
    repeat' first
      | apply congrArg₂ (fun a b : E => a * b)
      | apply congrArg (L.x _)
    all_goals ring

private theorem fc_lift (L : RootSections f)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hL : L.TorusEquivariant) (hC : L.CommutingRelations)
    (c : Fˣ) (hc : (c : F) ≠ 1) (z : F) :
    ∀ t, L.x 5 z * L.x 2 t = L.x 1 (-3*t*z) * L.x 2 t * L.x 5 z := by
  apply compare_word L hf hk hL 5 2 z c c (by simp [positiveWeight])
    (by simpa [positiveWeight] using hc) (fun t => L.x 1 (-3*t*z) * L.x 2 t)
  · simp
  · intro s t
    simp only [mul_assoc, append_relation (hC.cb _ _), collect_same, ← x_add]
    repeat' first
      | apply congrArg₂ (fun a b : E => a * b)
      | apply congrArg (L.x _)
    all_goals ring
  · intro t
    simp only [map_mul, L.project_x]
    simpa only [modelRootSections, x, positiveRootHom, MonoidHom.coe_mk,
      OneHom.coe_mk, toAdd_ofAdd] using
      (model_collectionRelations (F := F)).fc z t
  · intro a ha t
    change (MulAut.conj a) (L.x 1 (-3*t*z) * L.x 2 t) = _
    rw [map_mul]
    change (a * L.x 1 (-3*t*z) * a⁻¹) * (a * L.x 2 t * a⁻¹) = _
    rw [hL c c a ha, hL c c a ha]
    simp [positiveWeight, pow_two]
    repeat' first
      | apply congrArg₂ (fun a b : E => a * b)
      | apply congrArg (L.x _)
    all_goals ring

private theorem fd_add (L : RootSections f) (hC : L.CommutingRelations)
    (hdc : ∀ d t, L.x 3 d * L.x 2 t = L.x 0 (3*t*d) * L.x 2 t * L.x 3 d)
    (z s t : F) :
    L.x 0 (-3*(s+t)^2*z) * L.x 1 (3*(s+t)*z^2) *
        L.x 2 (-2*(s+t)*z) * L.x 3 (s+t) =
      (L.x 0 (-3*s^2*z) * L.x 1 (3*s*z^2) * L.x 2 (-2*s*z) * L.x 3 s) *
      (L.x 0 (-3*t^2*z) * L.x 1 (3*t*z^2) * L.x 2 (-2*t*z) * L.x 3 t) := by
  simp only [mul_assoc, append_relation (hC.ba _ _), append_relation (hC.ca _ _),
    append_relation (hC.cb _ _), append_relation (hC.da _ _),
    append_relation (hC.db _ _), append_relation (hdc _ _), collect_same, ← x_add]
  repeat' first
    | apply congrArg₂ (fun a b : E => a * b)
    | apply congrArg (L.x _)
  all_goals ring

private theorem fd_lift (L : RootSections f)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hL : L.TorusEquivariant) (hC : L.CommutingRelations)
    (hdc : ∀ d t, L.x 3 d * L.x 2 t = L.x 0 (3*t*d) * L.x 2 t * L.x 3 d)
    (c : Fˣ) (hc : (c : F) ≠ 1) (z : F) :
    ∀ t, L.x 5 z * L.x 3 t =
      L.x 0 (-3*t^2*z) * L.x 1 (3*t*z^2) * L.x 2 (-2*t*z) * L.x 3 t * L.x 5 z := by
  apply compare_word L hf hk hL 5 3 z c c (by simp [positiveWeight])
    (by simpa [positiveWeight] using hc)
    (fun t => L.x 0 (-3*t^2*z) * L.x 1 (3*t*z^2) * L.x 2 (-2*t*z) * L.x 3 t)
  · simp
  · exact fd_add L hC hdc z
  · intro t
    simp only [map_mul, L.project_x]
    simpa only [modelRootSections, x, positiveRootHom, MonoidHom.coe_mk,
      OneHom.coe_mk, toAdd_ofAdd] using
      (model_collectionRelations (F := F)).fd z t
  · intro a ha t
    change (MulAut.conj a) (L.x 0 (-3*t^2*z) * L.x 1 (3*t*z^2) *
      L.x 2 (-2*t*z) * L.x 3 t) = _
    simp only [map_mul, MulAut.conj_apply, hL c c a ha]
    simp [positiveWeight, pow_two]
    repeat' first
      | apply congrArg₂ (fun a b : E => a * b)
      | apply congrArg (L.x _)
    all_goals ring

private theorem fe_add (L : RootSections f) (hC : L.CommutingRelations)
    (hdc : ∀ d t, L.x 3 d * L.x 2 t = L.x 0 (3*t*d) * L.x 2 t * L.x 3 d)
    (heb : ∀ e b, L.x 4 e * L.x 1 b = L.x 0 (-b*e) * L.x 1 b * L.x 4 e)
    (z s t : F) :
    L.x 0 (-(s+t)^2*z^3) * L.x 1 (-(s+t)*z^3) * L.x 2 ((s+t)*z^2) *
        L.x 3 (-(s+t)*z) * L.x 4 (s+t) =
      (L.x 0 (-s^2*z^3) * L.x 1 (-s*z^3) * L.x 2 (s*z^2) *
        L.x 3 (-s*z) * L.x 4 s) *
      (L.x 0 (-t^2*z^3) * L.x 1 (-t*z^3) * L.x 2 (t*z^2) *
        L.x 3 (-t*z) * L.x 4 t) := by
  simp only [mul_assoc, append_relation (hC.ba _ _), append_relation (hC.ca _ _),
    append_relation (hC.cb _ _), append_relation (hC.da _ _),
    append_relation (hC.db _ _), append_relation (hdc _ _),
    append_relation (hC.ea _ _), append_relation (heb _ _),
    append_relation (hC.ec _ _), append_relation (hC.ed _ _), collect_same, ← x_add]
  repeat' first
    | apply congrArg₂ (fun a b : E => a * b)
    | apply congrArg (L.x _)
  all_goals ring

private theorem fe_lift (L : RootSections f)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hL : L.TorusEquivariant) (hC : L.CommutingRelations)
    (hdc : ∀ d t, L.x 3 d * L.x 2 t = L.x 0 (3*t*d) * L.x 2 t * L.x 3 d)
    (heb : ∀ e b, L.x 4 e * L.x 1 b = L.x 0 (-b*e) * L.x 1 b * L.x 4 e)
    (c : Fˣ) (hc : (c : F) ≠ 1) (z : F) :
    ∀ t, L.x 5 z * L.x 4 t =
      L.x 0 (-t^2*z^3) * L.x 1 (-t*z^3) * L.x 2 (t*z^2) * L.x 3 (-t*z) *
        L.x 4 t * L.x 5 z := by
  apply compare_word L hf hk hL 5 4 z c c (by simp [positiveWeight])
    (by simpa [positiveWeight, pow_two] using hc)
    (fun t => L.x 0 (-t^2*z^3) * L.x 1 (-t*z^3) * L.x 2 (t*z^2) *
      L.x 3 (-t*z) * L.x 4 t)
  · simp
  · exact fe_add L hC hdc heb z
  · intro t
    simp only [map_mul, L.project_x]
    simpa only [modelRootSections, x, positiveRootHom, MonoidHom.coe_mk,
      OneHom.coe_mk, toAdd_ofAdd] using
      (model_collectionRelations (F := F)).fe z t
  · intro a ha t
    change (MulAut.conj a) (L.x 0 (-t^2*z^3) * L.x 1 (-t*z^3) * L.x 2 (t*z^2) *
      L.x 3 (-t*z) * L.x 4 t) = _
    simp only [map_mul, MulAut.conj_apply, hL c c a ha]
    simp [positiveWeight, pow_two]
    repeat' first
      | apply congrArg₂ (fun a b : E => a * b)
      | apply congrArg (L.x _)
    all_goals ring

/-- In a central extension, torus-equivariant additive root sections satisfying
  the ten commuting relations satisfy all five polynomial relations. -/
theorem polynomialRelations_of_torusEquivariant [Finite F] (hF : 4 < Nat.card F)
    (L : RootSections f) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hL : L.TorusEquivariant) (hC : L.CommutingRelations) : L.PolynomialRelations := by
  have hcard : 3 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  obtain ⟨c, hc⟩ := exists_pow_ne_one_of_isCyclic (G := Fˣ) (by decide : 3 ≠ 0) hcard
  have hc3 : (c : F)^3 ≠ 1 := by
    intro h
    apply hc
    apply Units.ext
    simpa using h
  have hc1 : (c : F) ≠ 1 := by intro h; apply hc3; simp [h]
  have hdc := dc_lift L hf hk hL hC c hc1
  have heb := eb_lift L hf hk hL hC c hc3
  exact ⟨hdc, heb, fc_lift L hf hk hL hC c hc1,
    fd_lift L hf hk hL hC hdc c hc1, fe_lift L hf hk hL hC hdc heb c hc1⟩

/-- Combining the independently supplied commuting family with the proved
  polynomial family discharges all pairwise collection relations. -/
theorem collectionRelations_of_torusEquivariant [Finite F] (hF : 4 < Nat.card F)
    (L : RootSections f) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hL : L.TorusEquivariant) (hC : L.CommutingRelations) : L.CollectionRelations :=
  ⟨hC, polynomialRelations_of_torusEquivariant hF L hf hk hL hC⟩

/-- The actual six-root product in the cover satisfies the literal model
  multiplication law; the only inter-root input is the commuting family. -/
theorem productCompatible_of_torusEquivariant [Finite F] (hF : 4 < Nat.card F)
    (L : RootSections f) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hL : L.TorusEquivariant) (hC : L.CommutingRelations) : L.ProductCompatible :=
  (collectionRelations_of_torusEquivariant hF L hf hk hL hC).productCompatible L

end Atlas.G2.MultiplierOrdinary.RootSections
end

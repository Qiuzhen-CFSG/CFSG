module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.CommutingLifts

/-!
# Mixed root relations in central extensions of G₂(4)

Torus-equivariant additive sections of the six actual positive roots satisfy
all their collection relations. Eight commuting pairs are separated by the
field-four torus. The other two follow by expressing A as the commutator of
D and C. Four polynomial relations follow from scalar-equivariant uniqueness;
their additive words use only these commuting relations and earlier formulas.

For E–B the usual scalar argument degenerates over GF(4). Instead, conjugate
the F–C commutator by E. Its value can be computed from the downstairs
E-conjugate of F, since changing a lift by a central element does not change
a commutator. This gives E–B before the lifted F–E relation is used, so the
additivity argument for the F–E word is independent of the desired relation.

This supplies the missing mixed relations after quotienting a cover by the
common short-root defect. The transfer consumer is the exceptional multiplier
bound of Aschbacher–Smith I.1.3(1), printed p.407 (PDF p.418), and GLS III §6.1.
The field-independent polynomial-word calculations follow the neighboring
`MultiplierOrdinary.PositiveRelations.PolynomialLifts`; all root parameters
and signs are those of the attributed ATLAS octonion multiplication law.
-/

@[expose] public section

open scoped commutatorElement
namespace Atlas.G2.FiniteCover.MultiplierFourBound.TwoPrimary.MixedRelations
open Atlas.G2.MultiplierOrdinary Atlas.G2.MultiplierOrdinary.RootSections
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

private theorem four_separating_unit :
    ∃ c : FourFieldˣ, c ≠ 1 ∧ c ^ 2 ≠ 1 := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := FourFieldˣ)
  have horder : 2 < orderOf c := by
    rw [hc, Nat.card_units, GaloisField.card 2 2 (by decide)]
    decide
  refine ⟨c, ?_, pow_ne_one_of_lt_orderOf (by decide) horder⟩
  simpa using pow_ne_one_of_lt_orderOf (x := c) (n := 1) (by decide) (by omega)

private theorem commutator_of_interchange {x y z : E}
    (h : x * y = z * y * x) : ⁅x, y⁆ = z := by
  rw [commutatorElement_def, h]
  group

private theorem base_dc (a : FourField) :
    ⁅positiveRoot 3 (1 : FourField), positiveRoot 2 a⁆ = positiveRoot 0 a := by
  apply commutator_of_interchange
  have h := (model_collectionRelations (F := FourField)).dc 1 a
  simpa [modelRootSections, RootSections.x, positiveRootHom,
    CharTwo.ofNat_eq_mod] using h

private theorem commuting_four
    {f : E →* FourBase} (L : RootSections f)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hL : L.TorusEquivariant) : L.CommutingRelations := by
  obtain ⟨c, hc1, hc2⟩ := four_separating_unit
  have R := (model_collectionRelations (F := FourField)).toCommutingRelations
  have ca := L.commute_of_torus_separates hL hf hk 2 0 1 c
    (by simp [positiveWeight])
    (by simpa [positiveWeight] using hc1) R.ca
  have cb := L.commute_of_torus_separates hL hf hk 2 1 1 c
    (by simp [positiveWeight])
    (by simpa [positiveWeight] using hc1) R.cb
  have da := L.commute_of_torus_separates hL hf hk 3 0 c 1
    (by simp [positiveWeight])
    (by simpa [positiveWeight] using hc1) R.da
  have db := L.commute_of_torus_separates hL hf hk 3 1 c 1
    (by simp [positiveWeight])
    (by simpa [positiveWeight] using hc2) R.db
  have ec := L.commute_of_torus_separates hL hf hk 4 2 (c^2) c
    (by simp [positiveWeight])
    (by simpa [positiveWeight] using hc2) R.ec
  have ed := L.commute_of_torus_separates hL hf hk 4 3 (c^2) c
    (by simp [positiveWeight])
    (by simpa [positiveWeight] using hc1) R.ed
  have fa := L.commute_of_torus_separates hL hf hk 5 0 c c
    (by simp [positiveWeight])
    (by simpa [positiveWeight, pow_two] using hc2) R.fa
  have fb := L.commute_of_torus_separates hL hf hk 5 1 c c
    (by simp [positiveWeight])
    (by simpa [positiveWeight, pow_two] using hc1) R.fb
  have commute_A (v : E) (a : FourField)
      (hD : Commute v (L.x 3 1)) (hC : Commute v (L.x 2 a)) :
      Commute v (L.x 0 a) := by
    apply commutatorElement_eq_one_iff_commute.mp
    have he : f (L.x 0 a) = f ⁅L.x 3 1, L.x 2 a⁆ := by
      rw [map_commutatorElement, L.project_x, L.project_x, L.project_x, base_dc]
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl he]
    exact ((hD.mul_right hC).mul_right hD.inv_right |>.mul_right hC.inv_right).commutator_eq
  refine ⟨?_, ca, cb, da, db, ?_, ec, ed, fa, fb⟩
  · intro b a
    exact (commute_A (L.x 1 b) a (Commute.symm (db 1 b))
      (Commute.symm (cb a b))).eq
  · intro e a
    exact (commute_A (L.x 4 e) a (ed e 1) (ec e a)).eq

private theorem eb_four
    {f : E →* FourBase} (L : RootSections f)
    (hk : f.ker ≤ Subgroup.center E) (hC : L.CommutingRelations)
    (hdc : ∀ d t, L.x 3 d * L.x 2 t = L.x 0 (3*t*d) * L.x 2 t * L.x 3 d)
    (hfc : ∀ z t, L.x 5 z * L.x 2 t = L.x 1 (-3*t*z) * L.x 2 t * L.x 5 z)
    (e b : FourField) :
    L.x 4 e * L.x 1 b = L.x 0 (-b*e) * L.x 1 b * L.x 4 e := by
  have hFC : ⁅L.x 5 1, L.x 2 b⁆ = L.x 1 b := by
    apply commutator_of_interchange
    simpa [CharTwo.ofNat_eq_mod, CharTwo.neg_eq] using hfc 1 b
  have hDC : ⁅L.x 3 e, L.x 2 b⁆ = L.x 0 (b*e) := by
    apply commutator_of_interchange
    simpa [CharTwo.ofNat_eq_mod] using hdc e b
  let k := L.x 3 e * L.x 2 e * L.x 1 e * L.x 0 (e^2) * L.x 5 1
  have hkproj : f (L.x 4 e * L.x 5 1 * (L.x 4 e)⁻¹) = f k := by
    have hfe := (model_collectionRelations (F := FourField)).fe 1 e
    have hinv (i : Fin 6) (t : FourField) :
        (positiveRoot i t)⁻¹ = positiveRoot i t := by
      simpa [positiveRootHom, CharTwo.neg_eq] using
        ((positiveRootHom (F := FourField) i).map_inv (.ofAdd t)).symm
    have hfe' : positiveRoot 5 (1 : FourField) * positiveRoot 4 e =
        (positiveRoot 0 (e^2) * positiveRoot 1 e * positiveRoot 2 e * positiveRoot 3 e) *
          positiveRoot 4 e * positiveRoot 5 1 := by
      simpa [modelRootSections, RootSections.x, positiveRootHom,
        CharTwo.neg_eq] using hfe
    dsimp [k]
    simp only [map_mul, map_inv, L.project_x]
    have h : positiveRoot 4 e * positiveRoot 5 1 * (positiveRoot 4 e)⁻¹ =
        (positiveRoot 0 (e^2) * positiveRoot 1 e * positiveRoot 2 e * positiveRoot 3 e)⁻¹ *
          positiveRoot 5 1 := by
      rw [eq_inv_mul_iff_mul_eq]
      rw [← mul_assoc, ← mul_assoc, ← hfe']
      group
    simpa only [mul_inv_rev, hinv, mul_assoc] using h
  have hmiddle : Commute (L.x 2 e * L.x 1 e * L.x 0 (e^2)) (L.x 2 b) := by
    exact (((Commute.all (.ofAdd e : Multiplicative FourField) (.ofAdd b)).map
      (L.root 2)).mul_left (Commute.symm (hC.cb b e))).mul_left
        (Commute.symm (hC.ca b (e^2)))
  have hB : Commute (L.x 3 e * L.x 2 e * L.x 1 e * L.x 0 (e^2)) (L.x 1 b) := by
    exact ((Commute.mul_left (hC.db e b) (hC.cb e b)).mul_left
      ((Commute.all (.ofAdd e : Multiplicative FourField) (.ofAdd b)).map
        (L.root 1))).mul_left (Commute.symm (hC.ba b (e^2)))
  have hkC : ⁅k, L.x 2 b⁆ = L.x 0 (b*e) * L.x 1 b := by
    dsimp [k]
    rw [commutatorElement_mul_left_eq_conj_mul, hFC, hB.eq]
    simp only [mul_inv_cancel_right]
    rw [show L.x 3 e * L.x 2 e * L.x 1 e * L.x 0 (e^2) =
      L.x 3 e * (L.x 2 e * L.x 1 e * L.x 0 (e^2)) by group,
      commutatorElement_mul_left_eq_conj_mul, hmiddle.commutator_eq]
    simp only [mul_one, mul_inv_cancel, one_mul, hDC, hC.ba]
  have heB : L.x 4 e * L.x 1 b * (L.x 4 e)⁻¹ = L.x 0 (b*e) * L.x 1 b := by
    rw [← hFC, conjugate_commutatorElement]
    have heC : L.x 4 e * L.x 2 b * (L.x 4 e)⁻¹ = L.x 2 b := by
      rw [hC.ec, mul_inv_cancel_right]
    rw [heC, CentralExtension.commutator_eq_of_image_eq f hk hkproj rfl, hkC, hFC]
  simpa only [CharTwo.neg_eq] using (mul_inv_eq_iff_eq_mul.mp heB)

/-- All mixed relations lift after the individual roots have additive,
torus-equivariant sections; the exceptional field needs no larger scalar. -/
theorem collectionRelations_four
    {f : E →* FourBase} (L : RootSections f)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hL : L.TorusEquivariant) : L.CollectionRelations := by
  obtain ⟨c, hc, _⟩ := four_separating_unit
  have hc1 : (c : FourField) ≠ 1 := fun h => hc (Units.ext h)
  have hC := commuting_four L hf hk hL
  have hdc := dc_lift L hf hk hL hC c hc1
  have hfc := fc_lift L hf hk hL hC c hc1
  have heb := eb_four L hk hC hdc hfc
  exact ⟨hC, hdc, heb, hfc, fd_lift L hf hk hL hC hdc c hc1,
    fe_lift L hf hk hL hC hdc heb c hc1⟩

/-- The literal six-root product in a central G₂(4) extension is compatible
with the octonion multiplication when the roots are additive and normalized. -/
theorem productCompatible_four
    {f : E →* FourBase} (L : RootSections f)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hL : L.TorusEquivariant) : L.ProductCompatible :=
  (collectionRelations_four L hf hk hL).productCompatible L

end Atlas.G2.FiniteCover.MultiplierFourBound.TwoPrimary.MixedRelations

end

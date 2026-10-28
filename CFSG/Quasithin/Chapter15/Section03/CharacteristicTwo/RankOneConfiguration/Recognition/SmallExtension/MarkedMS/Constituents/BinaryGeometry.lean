module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.Interfaces
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates

/-!
# A moving plane in two binary natural modules

An order-24 subgroup preserving a four-element subspace cannot preserve a
vector whose two coordinates are independent: completing those coordinates to
a basis would inject the subgroup into the product of the three nonzero plane
vectors and the seven nonzero natural vectors. Thus each vector belongs to a
coordinate or diagonal natural copy. A nonzero vector and a distinct conjugate
span the plane, and the absence of fixed vectors supplies that conjugate.

We retain the actual equivariant embedding, identify its plane stabilizer by
transport from the standard parabolic, and prove Irr⁺ using irreducibility and
the literal quotient by fixed vectors. No placement or stabilizer equality is
assumed. The only new finite certificate extends a pair of distinct nonzero
vectors in the eight-element natural space to a determinant-one basis.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(1ii),
printed p.99, and the first paragraph of the proof of 15.3.31, printed p.1132
(PDF p.1149). This is the concrete doubled-module geometry used in that proof;
the source application remains with the constituent assembly.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.BinaryGeometry
private abbrev F := ZMod 2
private abbrev V := Fin 3 → F
private abbrev SL := Matrix.SpecialLinearGroup (Fin 3) F
private abbrev DV := Fin 2 → V
private noncomputable abbrev N : Representation F SL V := binaryNatural
private noncomputable abbrev D : Representation F SL DV := repeated N 2

private theorem plane_finrank {U : Type*} [AddCommGroup U] [Module F U]
    [Finite U] (E : Submodule F U) (hE : Nat.card E = 4) :
    Module.finrank F E = 2 := by
  have hh := Module.natCard_eq_pow_finrank (K := F) (V := E)
  rw [hE, Nat.card_zmod] at hh
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hh.symm

private theorem binary_pair_independent {U : Type*} [AddCommGroup U] [Module F U]
    (x y : U) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    LinearIndependent F ![x, y] := by
  apply LinearIndependent.pair_iff.mpr
  intro s t h
  have hF : ∀ c : F, c = 0 ∨ c = 1 := by decide
  rcases hF s with rfl | rfl <;> rcases hF t with rfl | rfl <;> simp_all
  have hy' : -y = y := by simpa using (neg_one_smul F y).symm
  exact hxy ((eq_neg_of_add_eq_zero_left h).trans hy')

private theorem plane_le_of_pair {U : Type*} [AddCommGroup U] [Module F U] [Finite U]
    (E K : Submodule F U) (hE : Nat.card E = 4) (x y : E)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (hxK : (x : U) ∈ K) (hyK : (y : U) ∈ K) : E ≤ K := by
  have hs := (binary_pair_independent x y hx hy hxy).span_eq_top_of_card_eq_finrank
    (by simpa using (plane_finrank E hE).symm)
  have hle : Submodule.span F (Set.range ![x, y]) ≤ K.comap E.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hxK
    · exact hyK
  rw [hs] at hle
  intro v hv
  exact hle (show (⟨v, hv⟩ : E) ∈ ⊤ from trivial)

set_option maxRecDepth 10000 in
private theorem pair_extension : ∀ a b : V, a ≠ 0 → b ≠ 0 → a ≠ b →
    ∃ c : V, Matrix.det (fun i j => (![a, b, c] j) i) = 1 := by
  decide +kernel

private theorem extension_basis (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∃ B : Module.Basis (Fin 3) F V, B 0 = a ∧ B 1 = b := by
  obtain ⟨c, hc⟩ := pair_extension a b ha hb hab
  have hi : LinearIndependent F ![a, b, c] :=
    Matrix.linearIndependent_cols_of_det_ne_zero (hc.trans_ne one_ne_zero)
  let B := Module.Basis.mk hi (hi.span_eq_top_of_card_eq_finrank (by simp [V])).ge
  exact ⟨B, Module.Basis.mk_apply _ _ _, Module.Basis.mk_apply _ _ _⟩

private theorem natural_injective : Function.Injective N := by
  intro g h he
  apply Matrix.SpecialLinearGroup.toLin'_injective
  exact LinearEquiv.toLinearMap_injective he

private theorem natural_ne_zero (g : SL) {v : V} (hv : v ≠ 0) : N g v ≠ 0 := by
  intro h
  apply hv
  have hh := congrArg (N g⁻¹) h
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply, map_zero] using hh

private theorem doubled_ne_zero (g : SL) {v : DV} (hv : v ≠ 0) : D g v ≠ 0 := by
  intro h
  apply hv
  have hh := congrArg (D g⁻¹) h
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply, map_zero] using hh

private theorem coordinates_dependent (E : Submodule F DV) (P : Subgroup SL)
    (hE : Nat.card E = 4) (hP : Nat.card P = 24)
    (hs : P ≤ subspaceStabilizer D E) (v : E) :
    v.val 0 = 0 ∨ v.val 1 = 0 ∨ v.val 0 = v.val 1 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨B, hB0, hB1⟩ := extension_basis (v.val 0) (v.val 1) hn.1 hn.2.1 hn.2.2
  have hv : (v : DV) ≠ 0 := fun he => hn.1 (congrFun he 0)
  let f : P → {w : E // w ≠ 0} × {w : V // w ≠ 0} := fun g =>
    (⟨⟨D g v, (hs g.property v).2 v.property⟩,
      fun he => doubled_ne_zero g hv (congrArg Subtype.val he)⟩,
      ⟨N g (B 2), natural_ne_zero g (B.ne_zero 2)⟩)
  have hf : Function.Injective f := by
    intro g h he
    have he1 := congrArg (fun z => z.1.val.val) he
    have he2 := congrArg (fun z => z.2.val) he
    apply Subtype.ext
    apply natural_injective
    apply B.ext
    intro i
    fin_cases i
    · change N g (B 0) = N h (B 0)
      rw [hB0]
      exact congrFun he1 0
    · change N g (B 1) = N h (B 1)
      rw [hB1]
      exact congrFun he1 1
    · exact he2
  have hh := Nat.card_le_card_of_injective f hf
  have hEn : Nat.card {w : E // w ≠ 0} = 3 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_unique]
    simpa only [Nat.card_eq_fintype_card] using congrArg (fun n => n - 1) hE
  have hVn : Nat.card {w : V // w ≠ 0} = 7 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, V, F]
  rw [hP, Nat.card_prod, hEn, hVn] at hh
  omega

private theorem natural_irreducible : IsIrreducible N := by
  exact BinaryLinearThree.IrreducibleCatalogue.natural_irreducible

private theorem invariant_trivial (J : Submodule F V) (hJ : (⊤ : Subgroup SL) ≤
    subspaceStabilizer N J) : J = ⊥ ∨ J = ⊤ := by
  let S : Subrepresentation N := ⟨J, fun g _ hv => (hJ (Subgroup.mem_top g) _).2 hv⟩
  let := natural_irreducible
  exact (eq_bot_or_eq_top S).imp (congrArg Subrepresentation.toSubmodule)
    (congrArg Subrepresentation.toSubmodule)

private theorem natural_not_fixed : ¬ (⊤ : Submodule F V) ≤ fixedSpace N ⊤ := by
  intro h
  let g : SL := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩
  have hh := h (show ![1, 0, 0] ∈ (⊤ : Submodule F V) from trivial) ⟨g, trivial⟩
  have hc := congrFun hh 0
  change (0 : F) = 1 at hc
  exact zero_ne_one hc

/-- The precise binary natural model is an Irr⁺ member for its full actor. -/
theorem natural_isIrrPlus : IsIrrPlus binaryNatural ⊤ ⊤ := by
  have hs : (⊤ : Subgroup SL) ≤ subspaceStabilizer N ⊤ :=
    le_subspaceStabilizer N ⊤ (by simp)
  have hcomm := subspaceCommutator_invariant_normalizer N hs
    (show (⊤ : Subgroup SL) ≤ Subgroup.normalizer (⊤ : Subgroup SL) from
      Subgroup.le_normalizer)
  have hc : subspaceCommutator N ⊤ ⊤ = ⊤ :=
    (invariant_trivial _ hcomm).resolve_left (fun h => natural_not_fixed
      ((subspaceCommutator_eq_bot_iff N ⊤ ⊤).mp h))
  apply isIrrPlus_of_minimal N hs hc natural_not_fixed
  intro J hJ _
  rcases invariant_trivial J hJ with h | h
  · exact Or.inr (h ▸ bot_le)
  · exact Or.inl h

private def coordinatePlane : Submodule F V := (LinearMap.proj (R := F) 2).ker

private theorem coordinatePlane_stabilizer : subspaceStabilizer N coordinatePlane =
    Matrix.PSL3Two.lineParabolicSL := by
  ext g
  rw [Matrix.PSL3Two.lineParabolicSL, MulAction.mem_stabilizer_set]
  rfl

private theorem plane_stabilizer_card (R : Submodule F V) (hR : Nat.card R = 4) :
    Nat.card (subspaceStabilizer N R) = 24 := by
  classical
  let B := Module.finBasisOfFinrankEq F R (plane_finrank R hR)
  let a : V := B 0
  let b : V := B 1
  have ha : a ≠ 0 := fun h => B.ne_zero 0 (Subtype.ext h)
  have hb : b ≠ 0 := fun h => B.ne_zero 1 (Subtype.ext h)
  have hab : a ≠ b := fun h => (by decide : (0 : Fin 2) ≠ 1)
    (B.injective (Subtype.ext h))
  obtain ⟨c, hc⟩ := pair_extension a b ha hb hab
  let g : SL := ⟨fun i j => (![a, b, c] j) i, hc⟩
  have hmap : coordinatePlane.map (N g) = R := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      have he : N g v = v 0 • a + v 1 • b := by
        have hv' : v 2 = 0 := hv
        change g.val.mulVec v = _
        ext i
        simp [g, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv', mul_comm]
      rw [he]
      exact R.add_mem (R.smul_mem _ (B 0).property) (R.smul_mem _ (B 1).property)
    · apply plane_le_of_pair R _ hR (B 0) (B 1) (B.ne_zero _) (B.ne_zero _)
        (fun h => (by decide : (0 : Fin 2) ≠ 1) (B.injective h))
      · refine ⟨![1, 0, 0], ?_, ?_⟩
        · rfl
        · change g.val.mulVec ![1, 0, 0] = a
          ext i
          simp [g, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      · refine ⟨![0, 1, 0], ?_, ?_⟩
        · rfl
        · change g.val.mulVec ![0, 1, 0] = b
          ext i
          simp [g, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have he (k : SL) (v : V) : (Matrix.SpecialLinearGroup.toLin' g) (N k v) =
      N (MulAut.conj g k) ((Matrix.SpecialLinearGroup.toLin' g) v) := by
    change N g (N k v) = N (g * k * g⁻¹) (N g v)
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  have ht := map_subspaceStabilizer_equivariant N N (MulAut.conj g)
    (Matrix.SpecialLinearGroup.toLin' g) he coordinatePlane
  change (subspaceStabilizer N coordinatePlane).map (MulAut.conj g).toMonoidHom =
    subspaceStabilizer N (coordinatePlane.map (N g)) at ht
  rw [hmap, coordinatePlane_stabilizer] at ht
  rw [← ht, Subgroup.card_map_of_injective (MulAut.conj g).injective,
    Matrix.PSL3Two.card_lineParabolicSL]

private def scalarCopy (t : Fin 2 → F) : V →ₗ[F] DV where
  toFun v i := t i • v
  map_add' v w := by funext i; exact smul_add _ _ _
  map_smul' c v := by funext i; exact smul_comm _ _ _

private theorem scalarCopy_equivariant (t : Fin 2 → F) (g : SL) (v : V) :
    scalarCopy t (N g v) = D g (scalarCopy t v) := by
  ext i j
  exact congrFun (map_smul (N g) (t i) v).symm j

private theorem scalarCopy_injective (t : Fin 2 → F) (ht : t ≠ 0) :
    Function.Injective (scalarCopy t) := by
  have hF : ∀ c : F, c ≠ 0 → c = 1 := by decide
  obtain ⟨i, hi⟩ : ∃ i, t i ≠ 0 := by
    by_contra h
    push Not at h
    exact ht (funext h)
  intro v w he
  have hh := congrFun he i
  change t i • v = t i • w at hh
  simpa only [hF _ hi, one_smul] using hh

private theorem vector_in_copy (v : DV)
    (hv : v 0 = 0 ∨ v 1 = 0 ∨ v 0 = v 1) :
    ∃ t : Fin 2 → F, t ≠ 0 ∧ v ∈ (scalarCopy t).range := by
  rcases hv with hv | hv | hv
  · refine ⟨![0, 1], by decide, v 1, ?_⟩
    ext i
    fin_cases i <;> simp [scalarCopy, hv]
  · refine ⟨![1, 0], by decide, v 0, ?_⟩
    ext i
    fin_cases i <;> simp [scalarCopy, hv]
  · refine ⟨![1, 1], by decide, v 0, ?_⟩
    ext i
    fin_cases i <;> simp [scalarCopy, hv]

private theorem plane_in_copy (E : Submodule F DV) (P : Subgroup SL)
    (hE : Nat.card E = 4) (hP : Nat.card P = 24)
    (hs : P ≤ subspaceStabilizer D E) (hd : Disjoint E (fixedSpace D P)) :
    ∃ t : Fin 2 → F, t ≠ 0 ∧ E ≤ (scalarCopy t).range := by
  classical
  have hne : E ≠ ⊥ := by intro h; subst E; simp at hE
  obtain ⟨v, hvE, hv⟩ := E.ne_bot_iff.mp hne
  obtain ⟨t, ht, w, hw⟩ := vector_in_copy v (coordinates_dependent E P hE hP hs ⟨v, hvE⟩)
  have hnfix : v ∉ fixedSpace D P := fun h => hv (Submodule.disjoint_def.mp hd v hvE h)
  obtain ⟨g, hg⟩ : ∃ g : P, D g v ≠ v := by
    by_contra h
    push Not at h
    exact hnfix h
  refine ⟨t, ht, plane_le_of_pair E _ hE ⟨v, hvE⟩
    ⟨D g v, (hs g.property v).2 hvE⟩ ?_ ?_ ?_ ⟨w, hw⟩ ?_⟩
  · exact fun h => hv (congrArg Subtype.val h)
  · exact fun h => doubled_ne_zero g hv (congrArg Subtype.val h)
  · exact fun h => hg (congrArg Subtype.val h).symm
  · exact ⟨N g w, (scalarCopy_equivariant t g w).trans (congrArg (D g) hw)⟩

/-- Every moving binary plane stabilized by an order-24 subgroup lies in an
actual natural copy, with that same subgroup as its full natural stabilizer. -/
theorem exists_binaryDoubledLine
    (E : Submodule (ZMod 2) (Fin 2 → Fin 3 → ZMod 2))
    (P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hE : Nat.card E = 4) (hP : Nat.card P = 24)
    (hs : P ≤ subspaceStabilizer (repeated binaryNatural 2) E)
    (hd : Disjoint E (fixedSpace (repeated binaryNatural 2) P)) :
    Nonempty (BinaryDoubledLine E P) := by
  obtain ⟨t, ht, hEt⟩ := plane_in_copy E P hE hP hs hd
  let f := scalarCopy t
  have hf : Function.Injective f := scalarCopy_injective t ht
  let R := E.comap f
  have hmap : R.map f = E := by
    exact (Submodule.map_comap_eq _ _).trans (inf_eq_right.mpr hEt)
  have hR : Nat.card R = 4 := by
    rw [← embedding_line_card f hf R, hmap, hE]
  have hstab := embedding_stabilizer N D f hf (scalarCopy_equivariant t) R
  rw [hmap] at hstab
  have heq : subspaceStabilizer N R = P := by
    apply (Subgroup.eq_of_le_of_card_ge (hstab ▸ hs) ?_).symm
    rw [plane_stabilizer_card R hR, hP]
  have hi : IsIrrPlus D ⊤ f.range := by
    have hh := IsIrrPlus.map_embedding D N (MonoidHom.id SL) f hf
      (fun g v => (scalarCopy_equivariant t g v).symm) ⊤ ⊤
      (by simpa using (show IsIrrPlus N ⊤ ⊤ from natural_isIrrPlus))
    simpa only [Submodule.map_top] using hh
  exact ⟨⟨R, hR, f, hf, scalarCopy_equivariant t, hmap, hi, heq⟩⟩
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.BinaryGeometry

module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.BinaryBorel.Tori

/-!
# Descent of the marked Borel action to both torus factors

Characteristic two-cores let each Borel isomorphism descend to its actual
quotient. Conjugating by the quotient coordinates gives a torus action
commuting with the product quotient map. The images of the two genuine
ambient axes are precisely the two torus axes. Thus an ambient automorphism
preserving the Borel and fixing or exchanging the factors does the same
on the quotient. Restriction to those axes constructs the corresponding
factor automorphisms or exchanging equivalences, with pointwise formulas.
When the Borel factor maps are specified, their formulas also descend.

Source: Aschbacher–Smith, proof of 13.8.16(1), printed p.952/PDF p.969.
-/

@[expose] public section

open Subgroup
open Matrix.ProjectiveSpecialLinearGroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.BinaryBorel
variable {Q : Type*} [Group Q] [Finite Q]

/-- The actual quotient equivalence induced by an isomorphism of factor Borels. -/
noncomputable def factorTorusEquiv {S T : Sylow 2 Q} (e : borel S ≃* borel T) :
    Torus S ≃* Torus T := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

omit [Finite Q] in
theorem factorTorusEquiv_mk {S T : Sylow 2 Q} (e : borel S ≃* borel T) (x : borel S) :
    factorTorusEquiv e (torusMap S x) = torusMap T (e x) := rfl

/-- Descent of a Borel automorphism through its two-core, in marked torus coordinates. -/
noncomputable def torusAction (S : Sylow 2 (Q × Q)) (e : MulAut (borel S)) :
    MulAut (Torus (firstSylow S) × Torus (secondSylow S)) :=
  (torusCoordinates S).symm.trans ((factorTorusEquiv e).trans (torusCoordinates S))

/-- The action commutes with the actual product quotient map. -/
theorem torusAction_productMap (S : Sylow 2 (Q × Q)) (e : MulAut (borel S))
    (x : borel S) : torusAction S e (productMap S x) = productMap S (e x) := by
  change torusCoordinates S (factorTorusEquiv e
    ((torusCoordinates S).symm (productMap S x))) = _
  rw [← torusCoordinates_mk S x, MulEquiv.symm_apply_apply,
    factorTorusEquiv_mk, torusCoordinates_mk]

/-- The intersection of the Borel with the first ambient factor. -/
def firstAxis (S : Sylow 2 (Q × Q)) : Subgroup (borel S) :=
  (MonoidHom.snd Q Q).ker.subgroupOf (borel S)

/-- The intersection of the Borel with the second ambient factor. -/
def secondAxis (S : Sylow 2 (Q × Q)) : Subgroup (borel S) :=
  (MonoidHom.fst Q Q).ker.subgroupOf (borel S)

omit [Finite Q] in
theorem mem_firstAxis (S : Sylow 2 (Q × Q)) (x : borel S) :
    x ∈ firstAxis S ↔ (x : Q × Q).2 = 1 := Iff.rfl

omit [Finite Q] in
theorem mem_secondAxis (S : Sylow 2 (Q × Q)) (x : borel S) :
    x ∈ secondAxis S ↔ (x : Q × Q).1 = 1 := Iff.rfl

noncomputable def firstTorusAxis (S : Sylow 2 (Q × Q)) :
    Subgroup (Torus (firstSylow S) × Torus (secondSylow S)) := (MonoidHom.snd _ _).ker

noncomputable def secondTorusAxis (S : Sylow 2 (Q × Q)) :
    Subgroup (Torus (firstSylow S) × Torus (secondSylow S)) := (MonoidHom.fst _ _).ker

theorem firstAxis_map (S : Sylow 2 (Q × Q)) :
    (firstAxis S).map (productMap S) = firstTorusAxis S := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h : (coordinates S x).2 = 1 := Subtype.ext hx
    change torusMap (secondSylow S) (coordinates S x).2 = 1
    rw [h, map_one]
  · intro hz
    obtain ⟨x, hx⟩ := torusMap_surjective (firstSylow S) z.1
    refine ⟨(coordinates S).symm (x, 1), ?_, ?_⟩
    · exact (mem_firstAxis S _).mpr rfl
    · rw [productMap_apply, MulEquiv.apply_symm_apply, map_one]
      exact Prod.ext hx hz.symm

theorem secondAxis_map (S : Sylow 2 (Q × Q)) :
    (secondAxis S).map (productMap S) = secondTorusAxis S := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h : (coordinates S x).1 = 1 := Subtype.ext hx
    change torusMap (firstSylow S) (coordinates S x).1 = 1
    rw [h, map_one]
  · intro hz
    obtain ⟨x, hx⟩ := torusMap_surjective (secondSylow S) z.2
    refine ⟨(coordinates S).symm (1, x), ?_, ?_⟩
    · exact (mem_secondAxis S _).mpr rfl
    · rw [productMap_apply, MulEquiv.apply_symm_apply, map_one]
      exact Prod.ext hz.symm hx

theorem torusAction_map (S : Sylow 2 (Q × Q)) (e : MulAut (borel S))
    (A : Subgroup (borel S)) :
    (A.map (productMap S)).map (torusAction S e).toMonoidHom =
      (A.map e.toMonoidHom).map (productMap S) := by
  rw [map_map, map_map]
  congr 1
  exact MonoidHom.ext (torusAction_productMap S e)

theorem torusAction_fixes_axes (S : Sylow 2 (Q × Q)) (e : MulAut (borel S))
    (h₁ : (firstAxis S).map e.toMonoidHom = firstAxis S)
    (h₂ : (secondAxis S).map e.toMonoidHom = secondAxis S) :
    (firstTorusAxis S).map (torusAction S e).toMonoidHom = firstTorusAxis S ∧
      (secondTorusAxis S).map (torusAction S e).toMonoidHom = secondTorusAxis S := by
  constructor
  · rw [← firstAxis_map, torusAction_map, h₁]
  · rw [← secondAxis_map, torusAction_map, h₂]

theorem torusAction_swaps_axes (S : Sylow 2 (Q × Q)) (e : MulAut (borel S))
    (h₁ : (firstAxis S).map e.toMonoidHom = secondAxis S)
    (h₂ : (secondAxis S).map e.toMonoidHom = firstAxis S) :
    (firstTorusAxis S).map (torusAction S e).toMonoidHom = secondTorusAxis S ∧
      (secondTorusAxis S).map (torusAction S e).toMonoidHom = firstTorusAxis S := by
  constructor
  · rw [← firstAxis_map, torusAction_map, h₁, secondAxis_map]
  · rw [← secondAxis_map, torusAction_map, h₂, firstAxis_map]

/-- Restrict a specified ambient automorphism preserving the Borel. -/
noncomputable def restrictAut (S : Sylow 2 (Q × Q)) (a : MulAut (Q × Q))
    (ha : (borel S).map a.toMonoidHom = borel S) : MulAut (borel S) :=
  (a.subgroupMap (borel S)).trans (MulEquiv.subgroupCongr ha)

omit [Finite Q] in
theorem restrictAut_apply (S : Sylow 2 (Q × Q)) (a : MulAut (Q × Q))
    (ha : (borel S).map a.toMonoidHom = borel S) (x : borel S) :
    (restrictAut S a ha x : Q × Q) = a x := rfl

omit [Finite Q] in
theorem restrictAut_map (S : Sylow 2 (Q × Q)) (a : MulAut (Q × Q))
    (ha : (borel S).map a.toMonoidHom = borel S) (A B : Subgroup (Q × Q))
    (hAB : A.map a.toMonoidHom = B) :
    (A.subgroupOf (borel S)).map (restrictAut S a ha).toMonoidHom =
      B.subgroupOf (borel S) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change a (y : Q × Q) ∈ B
    rw [← hAB]
    exact mem_map_of_mem _ hy
  · intro hx
    refine ⟨(restrictAut S a ha).symm x, ?_, (restrictAut S a ha).apply_symm_apply x⟩
    change a.symm (x : Q × Q) ∈ A
    apply mem_map_equiv.mp
    rwa [hAB]

theorem ambient_fixes_torus_axes (S : Sylow 2 (Q × Q)) (a : MulAut (Q × Q))
    (ha : (borel S).map a.toMonoidHom = borel S)
    (h₁ : (MonoidHom.snd Q Q).ker.map a.toMonoidHom = (MonoidHom.snd Q Q).ker)
    (h₂ : (MonoidHom.fst Q Q).ker.map a.toMonoidHom = (MonoidHom.fst Q Q).ker) :
    (firstTorusAxis S).map (torusAction S (restrictAut S a ha)).toMonoidHom =
        firstTorusAxis S ∧
      (secondTorusAxis S).map (torusAction S (restrictAut S a ha)).toMonoidHom =
        secondTorusAxis S :=
  torusAction_fixes_axes S _ (restrictAut_map S a ha _ _ h₁) (restrictAut_map S a ha _ _ h₂)

theorem ambient_swaps_torus_axes (S : Sylow 2 (Q × Q)) (a : MulAut (Q × Q))
    (ha : (borel S).map a.toMonoidHom = borel S)
    (h₁ : (MonoidHom.snd Q Q).ker.map a.toMonoidHom = (MonoidHom.fst Q Q).ker)
    (h₂ : (MonoidHom.fst Q Q).ker.map a.toMonoidHom = (MonoidHom.snd Q Q).ker) :
    (firstTorusAxis S).map (torusAction S (restrictAut S a ha)).toMonoidHom =
        secondTorusAxis S ∧
      (secondTorusAxis S).map (torusAction S (restrictAut S a ha)).toMonoidHom =
        firstTorusAxis S :=
  torusAction_swaps_axes S _ (restrictAut_map S a ha _ _ h₁) (restrictAut_map S a ha _ _ h₂)

theorem torusAction_factorwise (S : Sylow 2 (Q × Q)) (e : MulAut (borel S))
    (e₁ : MulAut (borel (firstSylow S))) (e₂ : MulAut (borel (secondSylow S)))
    (he : ∀ x, coordinates S (e x) = (e₁ (coordinates S x).1, e₂ (coordinates S x).2))
    (z : Torus (firstSylow S) × Torus (secondSylow S)) :
    torusAction S e z = (factorTorusEquiv e₁ z.1, factorTorusEquiv e₂ z.2) := by
  obtain ⟨x, rfl⟩ := productMap_surjective S z
  rw [torusAction_productMap, productMap_apply, he, productMap_apply]
  rfl

theorem torusAction_exchanging (S : Sylow 2 (Q × Q)) (e : MulAut (borel S))
    (e₁₂ : borel (firstSylow S) ≃* borel (secondSylow S))
    (e₂₁ : borel (secondSylow S) ≃* borel (firstSylow S))
    (he : ∀ x, coordinates S (e x) = (e₂₁ (coordinates S x).2, e₁₂ (coordinates S x).1))
    (z : Torus (firstSylow S) × Torus (secondSylow S)) :
    torusAction S e z = (factorTorusEquiv e₂₁ z.2, factorTorusEquiv e₁₂ z.1) := by
  obtain ⟨x, rfl⟩ := productMap_surjective S z
  rw [torusAction_productMap, productMap_apply, he, productMap_apply]
  rfl


private def leftAxisEquiv (A B : Type*) [Group A] [Group B] :
    (MonoidHom.snd A B).ker ≃* A where
  toFun x := x.1.1
  invFun x := ⟨(x, 1), rfl⟩
  left_inv x := Subtype.ext (Prod.ext rfl x.property.symm)
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def rightAxisEquiv (A B : Type*) [Group A] [Group B] :
    (MonoidHom.fst A B).ker ≃* B where
  toFun x := x.1.2
  invFun x := ⟨(1, x), rfl⟩
  left_inv x := Subtype.ext (Prod.ext x.property.symm rfl)
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem fixed_product_factors {A B : Type*} [Group A] [Group B]
    (a : MulAut (A × B))
    (h₁ : (MonoidHom.snd A B).ker.map a.toMonoidHom = (MonoidHom.snd A B).ker)
    (h₂ : (MonoidHom.fst A B).ker.map a.toMonoidHom = (MonoidHom.fst A B).ker) :
    ∃ e₁ : MulAut A, ∃ e₂ : MulAut B, ∀ x y, a (x, y) = (e₁ x, e₂ y) := by
  let e₁ := (leftAxisEquiv A B).symm.trans
    (((a.subgroupMap _).trans (MulEquiv.subgroupCongr h₁)).trans (leftAxisEquiv A B))
  let e₂ := (rightAxisEquiv A B).symm.trans
    (((a.subgroupMap _).trans (MulEquiv.subgroupCongr h₂)).trans (rightAxisEquiv A B))
  have hf (x : A) : a (x, 1) = (e₁ x, 1) := by
    have h : a (x, 1) ∈ (MonoidHom.snd A B).ker := by
      rw [← h₁]
      exact mem_map_of_mem _ rfl
    exact Prod.ext rfl h
  have hg (y : B) : a (1, y) = (1, e₂ y) := by
    have h : a (1, y) ∈ (MonoidHom.fst A B).ker := by
      rw [← h₂]
      exact mem_map_of_mem _ rfl
    exact Prod.ext h rfl
  refine ⟨e₁, e₂, fun x y => ?_⟩
  calc
    a (x, y) = a ((x, 1) * (1, y)) := by simp
    _ = (e₁ x, e₂ y) := by rw [map_mul, hf, hg]; simp

private theorem swapped_product_factors {A B : Type*} [Group A] [Group B]
    (a : MulAut (A × B))
    (h₁ : (MonoidHom.snd A B).ker.map a.toMonoidHom = (MonoidHom.fst A B).ker)
    (h₂ : (MonoidHom.fst A B).ker.map a.toMonoidHom = (MonoidHom.snd A B).ker) :
    ∃ e₁₂ : A ≃* B, ∃ e₂₁ : B ≃* A, ∀ x y, a (x, y) = (e₂₁ y, e₁₂ x) := by
  let e₁₂ := (leftAxisEquiv A B).symm.trans
    (((a.subgroupMap _).trans (MulEquiv.subgroupCongr h₁)).trans (rightAxisEquiv A B))
  let e₂₁ := (rightAxisEquiv A B).symm.trans
    (((a.subgroupMap _).trans (MulEquiv.subgroupCongr h₂)).trans (leftAxisEquiv A B))
  have hf (x : A) : a (x, 1) = (1, e₁₂ x) := by
    have h : a (x, 1) ∈ (MonoidHom.fst A B).ker := by
      rw [← h₁]
      exact mem_map_of_mem _ rfl
    exact Prod.ext h rfl
  have hg (y : B) : a (1, y) = (e₂₁ y, 1) := by
    have h : a (1, y) ∈ (MonoidHom.snd A B).ker := by
      rw [← h₂]
      exact mem_map_of_mem _ rfl
    exact Prod.ext rfl h
  refine ⟨e₁₂, e₂₁, fun x y => ?_⟩
  calc
    a (x, y) = a ((x, 1) * (1, y)) := by simp
    _ = (e₂₁ y, e₁₂ x) := by rw [map_mul, hf, hg]; simp

/-- Ambient preservation of each factor constructs the two actual torus automorphisms. -/
theorem exists_fixed_torus_factors (S : Sylow 2 (Q × Q)) (a : MulAut (Q × Q))
    (ha : (borel S).map a.toMonoidHom = borel S)
    (h₁ : (MonoidHom.snd Q Q).ker.map a.toMonoidHom = (MonoidHom.snd Q Q).ker)
    (h₂ : (MonoidHom.fst Q Q).ker.map a.toMonoidHom = (MonoidHom.fst Q Q).ker) :
    ∃ e₁ : MulAut (Torus (firstSylow S)), ∃ e₂ : MulAut (Torus (secondSylow S)),
      ∀ x y, torusAction S (restrictAut S a ha) (x, y) = (e₁ x, e₂ y) := by
  obtain ⟨hleft, hright⟩ := ambient_fixes_torus_axes S a ha h₁ h₂
  exact fixed_product_factors _ hleft hright

/-- Ambient exchange of the factors constructs the two actual torus equivalences. -/
theorem exists_exchanged_torus_factors (S : Sylow 2 (Q × Q)) (a : MulAut (Q × Q))
    (ha : (borel S).map a.toMonoidHom = borel S)
    (h₁ : (MonoidHom.snd Q Q).ker.map a.toMonoidHom = (MonoidHom.fst Q Q).ker)
    (h₂ : (MonoidHom.fst Q Q).ker.map a.toMonoidHom = (MonoidHom.snd Q Q).ker) :
    ∃ e₁₂ : Torus (firstSylow S) ≃* Torus (secondSylow S),
      ∃ e₂₁ : Torus (secondSylow S) ≃* Torus (firstSylow S),
        ∀ x y, torusAction S (restrictAut S a ha) (x, y) = (e₂₁ y, e₁₂ x) := by
  obtain ⟨hleft, hright⟩ := ambient_swaps_torus_axes S a ha h₁ h₂
  exact swapped_product_factors _ hleft hright

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.BinaryBorel

end

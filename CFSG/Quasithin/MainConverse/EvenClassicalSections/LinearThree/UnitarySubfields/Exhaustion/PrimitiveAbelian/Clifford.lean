module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.Exhaustion.PrimitiveAbelian.Basic
public import Theory.Representation.Clifford
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Clifford restriction in primitive unitary degree three

The inverse image of a nontrivial normal subgroup of a primitive projective
unitary subgroup acts irreducibly on the natural coefficient-field space.
Clifford's theorem gives an internal sum of conjugate irreducible constituents.
Their common dimension divides three, so a reducible restriction consists of
three lines. Equal multiplicities make their isomorphism classes either all
equal or pairwise distinct. The first case is scalar and contradicts projective
nontriviality; the second gives a line decomposition permuted by the full lift
and contradicts primitivity. No semisimplicity or homogeneity is assumed.

The public theorem transports this restriction to the genuine matrix image
used by the abelian normalizer argument. Normality remains relative to `M`.

Source: GLS3, proof of Hartley–Mitchell Theorem 6.5.3, the paragraphs surrounding
(6.5.1), `refs/KGroup/GLS3/chapter6.tex`.
-/

open Representation
open scoped DirectSum MonoidAlgebra
noncomputable section
variable {F G V : Type*} [Field F] [Group G]
  [AddCommGroup V] [Module F V]

-- Equal constituent dimensions and prime total dimension force three lines.
private theorem three_constituents [Finite G] [FiniteDimensional F V] [Nontrivial V]
    (ρ : Representation F G V) (H : Subgroup G) [H.Normal]
    (hρ : IsIrreducible ρ) (hdim : Module.finrank F V = 3)
    (hred : ¬ IsIrreducible (ρ.comp H.subtype)) :
    ∃ U : Fin 3 → Subrepresentation (ρ.comp H.subtype),
      DirectSum.IsInternal (fun i => (U i).asSubmodule) ∧
      (∀ i, IsIrreducible (U i).toRepresentation) ∧
      (∀ i, Module.finrank F (U i).toSubmodule = 1) ∧
      ∀ i, Nat.card {j // Nonempty ((U j).toRepresentation ≃ₗ (U i).toRepresentation)} =
        Nat.card {j // Nonempty ((U j).toRepresentation ≃ₗ (U 0).toRepresentation)} := by
  obtain ⟨W, hW⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp H.subtype)
  obtain ⟨n, g, hInt, hirr, he, hmult⟩ := isaacs_theorem_6_5 ρ H hρ W hW
  let U := fun i : Fin n => conjugateSubrepresentation ρ H W (g i)
  have hIntF : DirectSum.IsInternal (fun i => (U i).toSubmodule) := hInt
  have hedim (i : Fin n) : Module.finrank F (U i).toSubmodule = Module.finrank F W.toSubmodule :=
    (he i).some.toLinearEquiv.finrank_eq
  have hprod : n * Module.finrank F W.toSubmodule = 3 := by
    let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun i => (U i).toSubmodule)) hIntF
    have hd := e.finrank_eq
    rw [Module.finrank_directSum] at hd
    simpa [hedim, hdim] using hd
  have hdvd : Module.finrank F W.toSubmodule ∣ 3 := ⟨n, by simpa [mul_comm] using hprod.symm⟩
  rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd _ hdvd with hd | hd
  · have hn : n = 3 := by simpa [hd] using hprod
    subst n
    refine ⟨U, hInt, hirr, fun i => (hedim i).trans hd, ?_⟩
    intro i
    exact (hmult (U i).toRepresentation ⟨g i, he i⟩).symm.trans
      (hmult (U 0).toRepresentation ⟨g 0, he 0⟩)
  · have htop : W = ⊤ := Subrepresentation.toSubmodule_injective
      (Submodule.eq_top_iff_finrank_eq.mpr (hd.trans hdim.symm))
    have hatom := (Subrepresentation.irreducible_iff_isAtom W).mp hW
    exact (hred (isSimpleOrder_iff_isAtom_top.mpr (htop ▸ hatom))).elim

-- The only uniform partitions of a three-element set are the two extreme ones.
private theorem triple_uniform (R : Fin 3 → Fin 3 → Prop) (hrefl : ∀ i, R i i)
    (hsymm : ∀ i j, R i j → R j i)
    (htrans : ∀ i j k, R i j → R j k → R i k)
    (hcard : ∀ i, Nat.card {j // R j i} = Nat.card {j // R j 0}) :
    (∀ i j, R i j) ∨ (∀ i j, R i j ↔ i = j) := by
  classical
  have count (i : Fin 3) : Nat.card {j // R j i} =
      (if R 0 i then 1 else 0) + (if R 1 i then 1 else 0) +
      (if R 2 i then 1 else 0) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    by_cases h0 : R 0 i <;> by_cases h1 : R 1 i <;> by_cases h2 : R 2 i <;>
      simp [Finset.filter_insert, Finset.filter_singleton, h0, h1, h2]
  have hs (i j) : R i j ↔ R j i := ⟨hsymm i j, hsymm j i⟩
  by_cases h01 : R 0 1
  · by_cases h02 : R 0 2
    · left
      have hall (i : Fin 3) : R 0 i := by fin_cases i <;> simp [hrefl, h01, h02]
      exact fun i j => htrans i 0 j (hsymm 0 i (hall i)) (hall j)
    · have h12 : ¬ R 1 2 := fun h => h02 (htrans 0 1 2 h01 h)
      have hc := hcard 2
      rw [count, count] at hc
      simp [hrefl, h02, h12, (hs 1 0).mpr h01, hs 2 0] at hc
  · by_cases h02 : R 0 2
    · have h12 : ¬ R 1 2 := fun h => h01 (htrans 0 2 1 h02 (hsymm 1 2 h))
      have hc := hcard 1
      rw [count, count] at hc
      simp [hrefl, h01, h12, hs 2 1, hs 1 0, (hs 2 0).mpr h02] at hc
    · by_cases h12 : R 1 2
      · have hc := hcard 1
        rw [count, count] at hc
        simp [hrefl, h01, h02, hs 1 0, hs 2 0, (hs 2 1).mpr h12] at hc
      · right
        intro i j
        fin_cases i <;> fin_cases j <;> simp [hrefl, h01, h02, h12, hs 1 0, hs 2 0, hs 2 1]

-- Pairwise nonisomorphic simple summands are the unique simple subrepresentations.
private theorem irreducible_eq_summand (σ : Representation F G V)
    (U : Fin 3 → Subrepresentation σ)
    (hint : DirectSum.IsInternal (fun i => (U i).asSubmodule))
    (hirr : ∀ i, IsIrreducible (U i).toRepresentation)
    (hsep : ∀ i j, Nonempty ((U i).toRepresentation ≃ₗ (U j).toRepresentation) → i = j)
    (S : Subrepresentation σ) (hS : IsIrreducible S.toRepresentation) :
    ∃ i, S = U i := by
  classical
  let e : Subrepresentation σ ≃o Submodule (MonoidAlgebra F G) σ.asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  have hsimple (i) : IsSimpleModule (MonoidAlgebra F G) (U i).asSubmodule :=
    isSimpleModule_iff_isAtom.mpr ((e.isAtom_iff (U i)).mpr
      ((Subrepresentation.irreducible_iff_isAtom (U i)).mp (hirr i)))
  have hSat : IsAtom S := (Subrepresentation.irreducible_iff_isAtom S).mp hS
  let : IsSimpleModule (MonoidAlgebra F G) S.asSubmodule :=
    isSimpleModule_iff_isAtom.mpr ((e.isAtom_iff S).mpr hSat)
  have hle := simple_submodule_le_selected (fun i => (U i).asSubmodule) hint hsimple
    S.asSubmodule (M := S.asSubmodule) ⟨LinearEquiv.refl _ _⟩
  have hex : ∃ i, Nonempty ((U i).asSubmodule ≃ₗ[MonoidAlgebra F G] S.asSubmodule) := by
    by_contra hn
    have hbot : S.asSubmodule = ⊥ := le_bot_iff.mp (hle.trans (iSup_le fun i =>
      (hn ⟨i.val, i.property⟩).elim))
    exact hSat.ne_bot (e.injective (hbot.trans e.map_bot.symm))
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ((Subrepresentation.irreducible_iff_isAtom (U i)).mp (hirr i)).le_iff_eq
    hSat.ne_bot |>.mp ?_⟩
  apply e.le_iff_le.mp
  refine hle.trans (iSup_le fun j => ?_)
  have hji : j.val = i := hsep j.val i
    ((isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv (U j.val) (U i)).mpr
      ⟨j.property.some.trans hi.some.symm⟩)
  exact (congrArg (fun k => (U k).asSubmodule) hji).le

private theorem basis_of_three_lines [FiniteDimensional F V] (U : Fin 3 → Submodule F V)
    (hint : DirectSum.IsInternal U) (hdim : ∀ i, Module.finrank F (U i) = 1) :
    ∃ b : Module.Basis (Fin 3) F V, ∀ i, Submodule.span F {b i} = U i := by
  classical
  let bs : ∀ i, Module.Basis (Fin 1) F (U i) := fun i =>
    (Module.finBasis F (U i)).reindex (finCongr (hdim i))
  let b := (hint.collectedBasis bs).reindex (Equiv.sigmaUnique (Fin 3) (fun _ => Fin 1))
  refine ⟨b, fun i => ?_⟩
  have hm : b i ∈ U i := by
    simp [b, Module.Basis.reindex_apply, DirectSum.IsInternal.collectedBasis_coe]
  exact (eq_span_singleton_of_mem_of_finrank_eq_one (hdim i) hm (b.ne_zero i)).symm

-- Equivalent one-dimensional representations have the same scalar action.
private theorem scalar_of_isomorphic_lines (σ : Representation F G V)
    (U : Fin 3 → Subrepresentation σ)
    (hint : DirectSum.IsInternal (fun i => (U i).asSubmodule))
    (hdim : ∀ i, Module.finrank F (U i).toSubmodule = 1)
    (hequiv : ∀ i j, Nonempty ((U i).toRepresentation ≃ₗ (U j).toRepresentation)) :
    ∀ g, ∃ c : F, σ g = c • LinearMap.id := by
  intro g
  obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
    (hdim 0) ((U 0).toRepresentation g)
  have hscalar (i) (v : (U i).toSubmodule) : σ g v.val = c • v.val := by
    let e := (hequiv 0 i).some
    obtain ⟨w, rfl⟩ := e.surjective v
    have he := e.isIntertwining g w
    rw [LinearMap.congr_fun hc w] at he
    have he' : (U i).toRepresentation g (e w) = c • e w :=
      he.symm.trans (e.toLinearEquiv.map_smul c w)
    exact congrArg Subtype.val he'
  have hintF : DirectSum.IsInternal (fun i => (U i).toSubmodule) := hint
  have hle : ⊤ ≤ LinearMap.ker (σ g - c • LinearMap.id) := by
    rw [← hintF.submodule_iSup_eq_top]
    exact iSup_le fun i v hv => by
      simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero] using hscalar i ⟨v, hv⟩
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  exact sub_eq_zero.mp (hle (Submodule.mem_top : v ∈ (⊤ : Submodule F V)))

private theorem permutes_of_nonisomorphic_lines [FiniteDimensional F V]
    (ρ : Representation F G V)
    (H : Subgroup G) [H.Normal]
    (U : Fin 3 → Subrepresentation (ρ.comp H.subtype))
    (hint : DirectSum.IsInternal (fun i => (U i).asSubmodule))
    (hirr : ∀ i, IsIrreducible (U i).toRepresentation)
    (hdim : ∀ i, Module.finrank F (U i).toSubmodule = 1)
    (hsep : ∀ i j, Nonempty ((U i).toRepresentation ≃ₗ (U j).toRepresentation) → i = j) :
    ∃ b : Module.Basis (Fin 3) F V, ∀ g i, ∃ j,
      (Submodule.span F {b i}).map (ρ g) = Submodule.span F {b j} := by
  obtain ⟨b, hb⟩ := basis_of_three_lines (fun i => (U i).toSubmodule) hint hdim
  refine ⟨b, fun g i => ?_⟩
  let C := conjugateSubrepresentationOrderIso ρ H g
  have hatom : IsAtom (C (U i)) := (C.isAtom_iff (U i)).mpr
    ((Subrepresentation.irreducible_iff_isAtom (U i)).mp (hirr i))
  obtain ⟨j, hj⟩ := irreducible_eq_summand (ρ.comp H.subtype) U hint hirr hsep
    (C (U i)) ((Subrepresentation.irreducible_iff_isAtom _).mpr hatom)
  refine ⟨j, ?_⟩
  rw [hb, hb]
  simpa only [C, conjugateSubrepresentationOrderIso_toSubmodule] using
    congrArg Subrepresentation.toSubmodule hj

open Matrix BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source.Unitary
open scoped IsMulCommutative

namespace CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion.PrimitiveAbelian

variable {F : Type} [Field F] [Finite F]

private theorem primitive_normalLift_irreducible (J : HermitianForm 3 F)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hM : IsPrimitiveLift J M)
    (A : Subgroup M) [A.Normal] (hA : A ≠ ⊥) :
    IsIrreducible ((liftRepresentation J M).comp (normalLift J M A).subtype) := by
  classical
  let ρ := liftRepresentation J M
  let H := normalLift J M A
  have hρ : IsIrreducible ρ := liftRepresentation_irreducible J M hM.1
  by_contra hred
  obtain ⟨U, hint, hirr, hdim, hcard⟩ := three_constituents ρ H hρ (by simp) hred
  rcases triple_uniform
    (fun i j => Nonempty ((U i).toRepresentation ≃ₗ (U j).toRepresentation))
    (fun i => ⟨RepEquiv.refl _⟩)
    (fun _ _ h => ⟨h.some.symm⟩)
    (fun _ _ _ h k => ⟨h.some.trans k.some⟩) hcard with hequiv | hsep
  · have hscalar := scalar_of_isomorphic_lines (ρ.comp H.subtype) U hint hdim hequiv
    apply normalLiftMatrix_not_le_center J M A hA
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨c, hc⟩ := hscalar ⟨y, hy⟩
    have hc' : generalLinearNatural 3 (liftToGL J M y) = c • LinearMap.id := hc
    rw [Subgroup.mem_center_iff]
    intro z
    apply generalLinearNatural_injective 3
    simp only [map_mul, hc']
    ext v
    simp [Module.End.mul_apply]
  · obtain ⟨b, hb⟩ := permutes_of_nonisomorphic_lines ρ H U hint hirr hdim
      (fun i j => (hsep i j).mp)
    exact hM.2 ⟨b, hb⟩

/-- The abelian normal lift acts irreducibly in the primitive degree-three case.
This is the Clifford restriction step in the proof of Hartley–Mitchell 6.5.3. -/
public theorem abelian_normalLift_irreducible (J : HermitianForm 3 F)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hM : IsPrimitiveLift J M)
    (A : Subgroup M) [A.Normal] [IsMulCommutative A] (hA : A ≠ ⊥)
    [IsMulCommutative (normalLift J M A)] :
    Representation.IsIrreducible
      ((Representation.generalLinearNatural 3).comp (normalLiftMatrix J M A).subtype) := by
  have hres := primitive_normalLift_irreducible J M hM A hA
  refine ⟨fun W => ?_⟩
  let W' : Subrepresentation
      ((liftRepresentation J M).comp (normalLift J M A).subtype) := {
    toSubmodule := W.toSubmodule
    apply_mem_toSubmodule y v hv := W.apply_mem_toSubmodule
      ⟨liftToGL J M y.val, Subgroup.mem_map_of_mem (liftToGL J M) y.property⟩ hv }
  rcases hres.eq_bot_or_eq_top W' with h | h
  · have hh := congrArg Subrepresentation.toSubmodule h
    exact Or.inl (Subrepresentation.toSubmodule_injective hh)
  · have hh := congrArg Subrepresentation.toSubmodule h
    exact Or.inr (Subrepresentation.toSubmodule_injective hh)

end CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion.PrimitiveAbelian

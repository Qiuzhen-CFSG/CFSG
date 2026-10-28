module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.Symplectic.Geometry
public import Theory.SpecificGroups.SymplecticFour.Sylow.Characters

/-!
# Regular Cartan orbits of subgroups in the symplectic argument

A Cartan element stabilizing U fixes its C-projection. Since U is disjoint
from W, that projection is injective on U, so the element fixes U pointwise.
Only after this step do the two nonzero root coordinates and their weights
force both torus parameters to be one. Thus the orbit of U has (q − 1)²
members. Adjoining the fixed subgroup C yields the extra member needed
for the TI count, without confusing subgroups with their punctured union.

The Cartan interface specifies the genuine diagonal matrices through the
component equivalence. Constructing it and the source Thompson configuration
remains the responsibility of the model and configuration lemmas.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.5.13, printed p.1202.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.Symplectic
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G]

namespace Splitting
variable {V C W : Subgroup G}

/-- An actor centralizing C and preserving W acts trivially on the first
coordinate of the actual multiplication decomposition V = C × W. -/
theorem conjugation_coordinates (d : Splitting V C W) {a : G}
    (haV : a ∈ normalizer (V : Set G)) (haW : a ∈ normalizer (W : Set G))
    (haC : a ∈ centralizer (C : Set G)) (x : V) :
    d.equiv (V.normalizerMonoidHom ⟨a, haV⟩ x) =
      ((d.equiv x).1, W.normalizerMonoidHom ⟨a, haW⟩ (d.equiv x).2) := by
  apply d.equiv.symm.injective
  apply Subtype.ext
  simp only [MulEquiv.symm_apply_apply]
  rw [d.multiply (d.equiv.symm _), MulEquiv.apply_symm_apply]
  change (MulAut.conj a) (x : G) =
    ((d.equiv x).1 : G) * (MulAut.conj a) ((d.equiv x).2 : G)
  rw [d.multiply x, map_mul]
  congr 1
  change a * _ * a⁻¹ = _
  rw [← mem_centralizer_iff.mp haC _ (d.equiv x).1.property, mul_inv_cancel_right]

/-- Setwise invariance becomes pointwise fixation because the C-projection
is injective on a subgroup disjoint from W. -/
theorem fixes_of_normalizes_disjoint (d : Splitting V C W) (hd : Disjoint C W)
    {U : Subgroup G} (hUV : U ≤ V) (hUW : Disjoint U W) {a : G}
    (haV : a ∈ normalizer (V : Set G)) (haW : a ∈ normalizer (W : Set G))
    (haC : a ∈ centralizer (C : Set G)) (haU : a ∈ normalizer (U : Set G))
    {x : G} (hx : x ∈ U) : (MulAut.conj a) x = x := by
  let v : V := ⟨x, hUV hx⟩
  let v' : V := V.normalizerMonoidHom ⟨a, haV⟩ v
  let f : V →* C := (MonoidHom.fst C W).comp d.equiv.toMonoidHom
  have hf : f v' = f v := by
    have hh := congrArg Prod.fst (d.conjugation_coordinates haV haW haC v)
    exact hh
  have hk : (v⁻¹ * v' : V) ∈ f.ker := (f.eq_iff).mp hf
  have hw : ((v⁻¹ * v' : V) : G) ∈ W := (d.mem_right_iff hd _).mpr hk
  have hu : ((v⁻¹ * v' : V) : G) ∈ U :=
    U.mul_mem (U.inv_mem hx) ((mem_normalizer_iff.mp haU x).mp hx)
  have he := Subgroup.disjoint_def.mp hUW hu hw
  exact (inv_mul_eq_one.mp he).symm

end Splitting


section Cartan
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]

/-- The Cartan is realized inside the component and agrees with its actual
diagonal matrices. The two weight equations are the local matrix calculation. -/
structure CartanAction {L W : Subgroup G} {eL : L ≃* Sp F}
    (p : RootPlane L W eL) where
  hom : (Fˣ × Fˣ) →* L
  model_eq : ∀ a, eL (hom a) = diagonalTorus a.1 a.2
  normalizes_right : ∀ a, (hom a : G) ∈ normalizer (W : Set G)
  weights : ∀ a (w : W),
    p.coordinates (W.normalizerMonoidHom ⟨hom a, normalizes_right a⟩ w) =
      (Multiplicative.ofAdd ((a.1 : F)^2 * (p.coordinates w).1.toAdd),
       Multiplicative.ofAdd ((a.1 : F) * (a.2 : F) * (p.coordinates w).2.toAdd))

/-- Both nonzero root coordinates force both diagonal parameters to be one. -/
theorem cartan_parameter_eq_one {a : Fˣ × Fˣ} {s t : F} (hs : s ≠ 0) (ht : t ≠ 0)
    (h₁ : (a.1 : F)^2 * s = s) (h₂ : (a.1 : F) * (a.2 : F) * t = t) : a = 1 := by
  have hsq : (a.1 : F)^2 = 1 := mul_right_cancel₀ hs (h₁.trans (one_mul s).symm)
  have ha : (a.1 : F) = 1 := CharTwo.sq_injective (hsq.trans (one_pow 2).symm)
  have hb : (a.2 : F) = 1 := by
    rw [ha, one_mul] at h₂
    exact mul_right_cancel₀ ht (h₂.trans (one_mul t).symm)
  exact Prod.ext (Units.ext ha) (Units.ext hb)

/-- The setwise stabilizer is trivial. The essential step is pointwise
fixation through the injective C-projection, before using vector regularity. -/
theorem cartan_subgroup_stabilizer {V C W L U : Subgroup G} {eL : L ≃* Sp F}
    (d : Splitting V C W) (p : RootPlane L W eL) (A : CartanAction p)
    (hd : Disjoint C W) (hCK : C ≤ centralizer (L : Set G))
    (hUV : U ≤ V) (hUW : Disjoint U W)
    (hAV : ∀ a, (A.hom a : G) ∈ normalizer (V : Set G))
    {x : G} (hx : x ∈ U)
    (hx₁ : (p.coordinates (d.equiv ⟨x, hUV hx⟩).2).1 ≠ 1)
    (hx₂ : (p.coordinates (d.equiv ⟨x, hUV hx⟩).2).2 ≠ 1)
    (a : Fˣ × Fˣ) (haU : U.conjBy (A.hom a : G) = U) : a = 1 := by
  have haC : (A.hom a : G) ∈ centralizer (C : Set G) := by
    intro c hc
    exact (mem_centralizer_iff.mp (hCK hc) (A.hom a) (A.hom a).property).symm
  have haU' : (A.hom a : G) ∈ normalizer (U : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr haU
  let v : V := ⟨x, hUV hx⟩
  have hv : V.normalizerMonoidHom ⟨(A.hom a : G), hAV a⟩ v = v :=
    Subtype.ext (d.fixes_of_normalizes_disjoint hd hUV hUW (hAV a)
      (A.normalizes_right a) haC haU' hx)
  have hw : W.normalizerMonoidHom ⟨(A.hom a : G), A.normalizes_right a⟩
      (d.equiv v).2 = (d.equiv v).2 := by
    have hh := congrArg Prod.snd (d.conjugation_coordinates (hAV a)
      (A.normalizes_right a) haC v)
    rw [hv] at hh
    exact hh.symm
  have hh := A.weights a (d.equiv v).2
  rw [hw] at hh
  apply cartan_parameter_eq_one
      (s := (p.coordinates (d.equiv v).2).1.toAdd)
      (t := (p.coordinates (d.equiv v).2).2.toAdd)
  · exact fun h => hx₁ (congrArg Multiplicative.ofAdd h)
  · exact fun h => hx₂ (congrArg Multiplicative.ofAdd h)
  · exact (congrArg (fun b => b.1.toAdd) hh).symm
  · exact (congrArg (fun b => b.2.toAdd) hh).symm

end Cartan

section FiniteOrbit
variable [Finite G]

/-- The finite orbit consists of subgroups, rather than the union of their
nonidentity elements. -/
noncomputable def conjugateFamily (M C : Subgroup G) : Finset (Subgroup G) := by
  classical
  letI := Fintype.ofFinite M
  exact Finset.univ.image (fun a : M => C.conjBy (a : G))

theorem mem_conjugateFamily (M C D : Subgroup G) :
    D ∈ conjugateFamily M C ↔ ∃ a : M, C.conjBy (a : G) = D := by
  classical
  simp [conjugateFamily]

/-- A free Cartan orbit of U and the additional fixed subgroup C give the
source lower bound. The freeness hypothesis concerns subgroups themselves. -/
theorem conjugateFamily_lower_bound {P : Type*} [Group P] [Fintype P]
    {M C U : Subgroup G} (ρ : P →* G)
    (hρM : ∀ a, ρ a ∈ M)
    (hρC : ∀ a, ρ a ∈ normalizer (C : Set G))
    (hUC : ∃ m : M, C.conjBy m = U)
    (hne : U ≠ C)
    (hfree : ∀ a, U.conjBy (ρ a) = U → a = 1) :
    Fintype.card P + 1 ≤ (conjugateFamily M C).card := by
  classical
  let f (a : P) : Subgroup G := U.conjBy (ρ a)
  have hinj : Function.Injective f := by
    intro a b hab
    have hh : U.conjBy (ρ (a⁻¹ * b)) = U := by
      simpa only [map_mul, map_inv] using U.conjBy_inv_mul_cancel hab
    exact inv_mul_eq_one.mp (hfree (a⁻¹ * b) hh)
  have hc : C ∉ Finset.univ.image f := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro a ha
    apply hne
    have hh := congrArg (fun Q : Subgroup G => Q.conjBy ((ρ a)⁻¹)) ha
    change (U.conjBy (ρ a)).conjBy (ρ a)⁻¹ = C.conjBy (ρ a)⁻¹ at hh
    have hcN : C.conjBy (ρ a)⁻¹ = C :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (C : Set G)).inv_mem (hρC a))
    simpa only [conjBy_conjBy, inv_mul_cancel, conjBy_one, hcN] using hh
  have hsub : insert C (Finset.univ.image f) ⊆ conjugateFamily M C := by
    intro D hD
    rcases Finset.mem_insert.mp hD with hD | hD
    · subst D
      exact (mem_conjugateFamily M C C).mpr ⟨1, C.conjBy_one⟩
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hD
      obtain ⟨m, hm⟩ := hUC
      apply (mem_conjugateFamily M C _).mpr
      refine ⟨⟨ρ a * m, M.mul_mem (hρM a) m.property⟩, ?_⟩
      change C.conjBy (ρ a * m) = U.conjBy (ρ a)
      rw [← conjBy_conjBy, hm]
  have hh := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hc, Finset.card_image_of_injective _ hinj,
    Finset.card_univ] at hh
  exact hh

end FiniteOrbit
end CFSG.Quasithin.Chapter16.Intersections.RankTwo.Symplectic

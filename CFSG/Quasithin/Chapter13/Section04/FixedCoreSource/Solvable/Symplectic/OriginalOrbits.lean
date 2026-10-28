module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Symplectic.FanoCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Representatives
/-!
# The four marked H₀-orbits in the original solvable branch

Restricting H₀ to the actual generated group E and then using the constructed
Fano-core isomorphism identifies its ambient O₂(H₀) with the six-dimensional
seven-point core. The original inclusions carry conjugation by the literal
H₀ to the Fano action. Consequently the four families exhaust the nonidentity
core, are disjoint, have lengths 7, 7, 21, 28 and weights 6, 4, 2, 4.
The weight-six family maps to transvections in the original plane directions.

The final existence theorem constructs the marking and coordinates from the
original MarkedC3; the module action is not an additional assumption. The
four families still need to be separated as classes of E by their intrinsic
symplectic invariants. Case-(ii) selection from genuine 13.4.7 alternatives
also remains with the solvable source assembly. Universal Structural1222
and the earlier-source conclusions retain their original producer and final
discharge with qt-d-1341-fixed-core-source.
Source: Aschbacher–Smith H.5.3(3–4), 13.4.9, printed pp.385–386,906–907.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher Quasithin.I5 Quasithin.I5.C3Recognition
open Chapter12.Section02 SolvableCentralizerC3 BinaryLinearThree.FanoLocalStructure
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
variable (D : ChosenModule T L V) (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
variable (m : SymplecticMark C.system)
variable (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace C.system.basePlane)

/-- The Fano-core isomorphism on the literal ambient H₀ two-core. -/
noncomputable def originalFanoEquiv : Multiplicative BinaryLinearThree.Core ≃* H₀.pCoreIn 2 := by
  let E := generated (normalizer (L : Set G)) z H₀
  have hTE : (T : Subgroup G) ≤ E :=
    D.sylow_normalizes_component.trans (first_le_generated _ _ _)
  have hHE : H₀ ≤ E := le_sup_right
  have hQE : H₀.pCoreIn 2 ≤ E := (pCoreIn_le 2 H₀).trans hHE
  have hQ : C.system.Q 2 = (H₀.pCoreIn 2).subgroupOf E := by
    change (C.system.family 2).pCoreIn 2 = _
    rw [C.third,pCoreIn_subgroupOf 2 H₀ E hHE]
  exact (m.planeFanoEquiv b (T.subtype hTE) C.chamber.symm).trans
    ((MulEquiv.subgroupCongr hQ).trans (subgroupOfEquivOfLe hQE))

theorem originalFanoEquiv_apply (a : Multiplicative BinaryLinearThree.Core) :
    (originalFanoEquiv D z H₀ C m b a).val = (m.fanoLift b a).val := rfl

/-- The original inclusion, not an unmarked abstract isomorphism, gives the action. -/
theorem original_fano_orbit_iff (a c : BinaryLinearThree.Core) :
    (∃ g ∈ H₀, MulAut.conj g (originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd a)).val =
      (originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd c)).val) ↔ c ∈ orbit a := by
  let E := generated (normalizer (L : Set G)) z H₀
  have hTE : (T : Subgroup G) ≤ E :=
    D.sylow_normalizes_component.trans (first_le_generated _ _ _)
  have hHE : H₀ ≤ E := le_sup_right
  rw [← m.fanoLift_orbit_iff b (T.subtype hTE) C.chamber.symm]
  simp only [originalFanoEquiv_apply]
  constructor
  · rintro ⟨g,hg,he⟩
    let gE : E := ⟨g,hHE hg⟩
    have hgS : gE ∈ C.system.family 2 := by rw [C.third]; exact hg
    exact ⟨⟨gE,hgS⟩,Subtype.ext he⟩
  · rintro ⟨g,he⟩
    have hg : g.val.val ∈ H₀ :=
      (show C.system.family 2 ≤ H₀.subgroupOf E from C.third.le) g.property
    exact ⟨g.val.val,hg,congrArg Subtype.val he⟩

noncomputable def originalFanoFamily (A : Set BinaryLinearThree.Core) : Set G :=
  (fun a => (originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd a)).val) '' A

theorem originalFanoFamily_card (A : Set BinaryLinearThree.Core) :
    Nat.card (originalFanoFamily D z H₀ C m b A) = Nat.card A := by
  apply (Nat.card_congr (Equiv.Set.image _ A ?_)).symm
  intro a c h
  have he := (originalFanoEquiv D z H₀ C m b).injective (Subtype.ext h)
  exact congrArg Multiplicative.toAdd he

/-- The original H₀ has four orbits of the source sizes on O₂(H₀). -/
theorem originalFanoFamily_cards :
    Nat.card (originalFanoFamily D z H₀ C m b pointComplements) = 7 ∧
    Nat.card (originalFanoFamily D z H₀ C m b lineComplements) = 7 ∧
    Nat.card (originalFanoFamily D z H₀ C m b weightTwo) = 21 ∧
    Nat.card (originalFanoFamily D z H₀ C m b basisComplements) = 28 := by
  simp only [originalFanoFamily_card]
  exact four_families_card

/-- Any nonzero original core element has exactly its indicated Fano orbit. -/
theorem originalFanoFamily_orbit (a : BinaryLinearThree.Core) :
    {c : G | ∃ g ∈ H₀, MulAut.conj g
      (originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd a)).val = c} =
        originalFanoFamily D z H₀ C m b (orbit a) := by
  ext c
  constructor
  · rintro ⟨g,hg,rfl⟩
    have hnorm : H₀ ≤ normalizer (H₀.pCoreIn 2 : Set G) :=
      H₀.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H₀ (pCore 2 H₀))
    have hmem : MulAut.conj g
        (originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd a)).val ∈ H₀.pCoreIn 2 :=
      (mem_normalizer_iff.mp (hnorm hg) _).mp
        (originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd a)).property
    obtain ⟨x,hx⟩ := (originalFanoEquiv D z H₀ C m b).surjective ⟨_,hmem⟩
    have he := congrArg Subtype.val hx
    refine ⟨x.toAdd,?_,he⟩
    exact (original_fano_orbit_iff D z H₀ C m b a x.toAdd).mp ⟨g,hg,he.symm⟩
  · rintro ⟨d,hd,rfl⟩
    exact (original_fano_orbit_iff D z H₀ C m b a d).mpr hd

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Quasithin.I5 Quasithin.I5.C3Recognition
open Chapter12.Section02 SolvableCentralizerC3 BinaryLinearThree.FanoLocalStructure
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
variable (D : ChosenModule T L V) (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
variable (m : SymplecticMark C.system)
variable (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace C.system.basePlane)

theorem originalFanoFamily_union :
    originalFanoFamily D z H₀ C m b pointComplements ∪
      originalFanoFamily D z H₀ C m b lineComplements ∪
      originalFanoFamily D z H₀ C m b weightTwo ∪
      originalFanoFamily D z H₀ C m b basisComplements =
        {a : G | a ∈ H₀.pCoreIn 2 ∧ a ≠ 1} := by
  simp only [originalFanoFamily,←Set.image_union,four_families_union]
  let e := originalFanoEquiv D z H₀ C m b
  ext a
  constructor
  · rintro ⟨c,hc,rfl⟩
    refine ⟨(e (Multiplicative.ofAdd c)).property,?_⟩
    intro he
    have hh := e.injective ((show e (Multiplicative.ofAdd c) = 1 from Subtype.ext he).trans e.map_one.symm)
    exact hc (congrArg Multiplicative.toAdd hh)
  · rintro ⟨ha,ha1⟩
    obtain ⟨c,hc⟩ := e.surjective ⟨a,ha⟩
    refine ⟨c.toAdd,?_,congrArg Subtype.val hc⟩
    intro hz
    have hc1 : c = 1 := congrArg Multiplicative.ofAdd hz
    have he : (e c).val = a := congrArg Subtype.val hc
    rw [hc1,e.map_one] at he
    exact ha1 he.symm

/-- Weight is measured in the seven original plane directions, through the
constructed core isomorphism. -/
noncomputable def originalFanoWeight (a : H₀.pCoreIn 2) : ℕ :=
  (support ((originalFanoEquiv D z H₀ C m b).symm a).toAdd).card

private theorem originalFanoWeight_image (A : Set BinaryLinearThree.Core) (k : ℕ)
    (hA : ∀ a ∈ A, (support a).card = k) (a : H₀.pCoreIn 2)
    (ha : a.val ∈ originalFanoFamily D z H₀ C m b A) :
    originalFanoWeight D z H₀ C m b a = k := by
  obtain ⟨c,hc,he⟩ := ha
  have he' : originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd c) = a := Subtype.ext he
  rw [originalFanoWeight,←he',MulEquiv.symm_apply_apply]
  exact hA c hc

theorem originalFanoFamily_weights :
    (∀ a : H₀.pCoreIn 2, a.val ∈ originalFanoFamily D z H₀ C m b pointComplements →
      originalFanoWeight D z H₀ C m b a = 6) ∧
    (∀ a : H₀.pCoreIn 2, a.val ∈ originalFanoFamily D z H₀ C m b lineComplements →
      originalFanoWeight D z H₀ C m b a = 4) ∧
    (∀ a : H₀.pCoreIn 2, a.val ∈ originalFanoFamily D z H₀ C m b weightTwo →
      originalFanoWeight D z H₀ C m b a = 2) ∧
    (∀ a : H₀.pCoreIn 2, a.val ∈ originalFanoFamily D z H₀ C m b basisComplements →
      originalFanoWeight D z H₀ C m b a = 4) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := BinaryLinearThree.FanoTransvection.four_families_weights
  exact ⟨originalFanoWeight_image D z H₀ C m b _ _ h₁,
    originalFanoWeight_image D z H₀ C m b _ _ h₂,
    originalFanoWeight_image D z H₀ C m b _ _ h₃,
    originalFanoWeight_image D z H₀ C m b _ _ h₄⟩

/-- The original marked chamber supplies the Fano marking and basis;
neither the core module identification nor its orbit action is assumed. -/
theorem exists_original_fano_orbit_marking :
    ∃ (m : SymplecticMark C.system)
      (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace C.system.basePlane),
      ∀ a c : BinaryLinearThree.Core,
        (∃ g ∈ H₀, MulAut.conj g
          (originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd a)).val =
            (originalFanoEquiv D z H₀ C m b (Multiplicative.ofAdd c)).val) ↔ c ∈ orbit a := by
  let S := C.system
  let d := S.source_local_polar_facts
  obtain ⟨m⟩ := exists_symplecticMark S
    ⟨S.c3_points_card d,S.faithful_points,S.c3_exists_noncollinear,
      fun x y h => S.source_one_or_all_triples d x y h⟩
  let b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace S.basePlane :=
    LinearEquiv.ofFinrankEq _ _ (by rw [m.planeSpace_finrank]; simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector])
  exact ⟨m,b,original_fano_orbit_iff D z H₀ C m b⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Quasithin.I5 Quasithin.I5.C3Recognition
open Chapter12.Section02 SolvableCentralizerC3 BinaryLinearThree.FanoLocalStructure
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
variable (D : ChosenModule T L V) (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
variable (m : SymplecticMark C.system)
variable (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace C.system.basePlane)

/-- Exhaustiveness on the actual ambient core, with the actual H₀ conjugators. -/
theorem originalFanoFamily_nonidentity_orbits (a : H₀.pCoreIn 2) (ha : a ≠ 1) :
    let O := {c : G | ∃ g ∈ H₀, MulAut.conj g a.val = c}
    O = originalFanoFamily D z H₀ C m b pointComplements ∨
    O = originalFanoFamily D z H₀ C m b lineComplements ∨
    O = originalFanoFamily D z H₀ C m b weightTwo ∨
    O = originalFanoFamily D z H₀ C m b basisComplements := by
  obtain ⟨x,rfl⟩ := (originalFanoEquiv D z H₀ C m b).surjective a
  have hx : x.toAdd ≠ 0 := by
    intro hz
    have hx1 : x = 1 := congrArg Multiplicative.ofAdd hz
    exact ha (hx1 ▸ map_one _)
  have ho := (nonzero_orbits x.toAdd).mp hx
  have he := originalFanoFamily_orbit D z H₀ C m b x.toAdd
  dsimp only
  rcases ho with ho | ho | ho | ho
  · exact Or.inl (he.trans (congrArg (originalFanoFamily D z H₀ C m b) ho))
  · exact Or.inr (Or.inl (he.trans (congrArg (originalFanoFamily D z H₀ C m b) ho)))
  · exact Or.inr (Or.inr (Or.inl (he.trans (congrArg (originalFanoFamily D z H₀ C m b) ho))))
  · exact Or.inr (Or.inr (Or.inr (he.trans (congrArg (originalFanoFamily D z H₀ C m b) ho))))

theorem originalFanoFamily_disjoint :
    Disjoint (originalFanoFamily D z H₀ C m b pointComplements)
      (originalFanoFamily D z H₀ C m b lineComplements) ∧
    Disjoint (originalFanoFamily D z H₀ C m b pointComplements)
      (originalFanoFamily D z H₀ C m b weightTwo) ∧
    Disjoint (originalFanoFamily D z H₀ C m b pointComplements)
      (originalFanoFamily D z H₀ C m b basisComplements) ∧
    Disjoint (originalFanoFamily D z H₀ C m b lineComplements)
      (originalFanoFamily D z H₀ C m b weightTwo) ∧
    Disjoint (originalFanoFamily D z H₀ C m b lineComplements)
      (originalFanoFamily D z H₀ C m b basisComplements) ∧
    Disjoint (originalFanoFamily D z H₀ C m b weightTwo)
      (originalFanoFamily D z H₀ C m b basisComplements) := by
  have hdis {A B : Set BinaryLinearThree.Core} (h : Disjoint A B) :
      Disjoint (originalFanoFamily D z H₀ C m b A) (originalFanoFamily D z H₀ C m b B) := by
    rw [Set.disjoint_left] at h ⊢
    rintro a ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    have he' := congrArg Multiplicative.toAdd
      ((originalFanoEquiv D z H₀ C m b).injective (Subtype.ext he))
    change y = x at he'
    exact h hx (he' ▸ hy)
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := four_families_disjoint
  exact ⟨hdis h₁,hdis h₂,hdis h₃,hdis h₄,hdis h₅,hdis h₆⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Quasithin.I5 Quasithin.I5.C3Recognition
open Chapter12.Section02 SolvableCentralizerC3
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
variable (D : ChosenModule T L V) (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
variable (m : SymplecticMark C.system)
variable (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace C.system.basePlane)

/-- The ambient core isomorphism retains the actual symplectic displacement. -/
theorem originalFanoEquiv_marking (a : Multiplicative BinaryLinearThree.Core) :
    m.hom ⟨(originalFanoEquiv D z H₀ C m b a).val,
      ((pCoreIn_le 2 H₀).trans (show H₀ ≤ generated (normalizer (L : Set G)) z H₀ from le_sup_right))
        (originalFanoEquiv D z H₀ C m b a).property⟩ =
      BinaryLinearThree.FanoTransvection.shear (m.fanoEmbedding b) (m.fanoEmbedding_isotropic b) a :=
  m.fanoLift_marking b a

/-- The original weight-six family is the marked transvection family. -/
theorem originalFanoEquiv_pointSpike (p : BinaryLinearThree.Point) :
    m.hom ⟨(originalFanoEquiv D z H₀ C m b
      (Multiplicative.ofAdd (BinaryLinearThree.FanoDecomposition.pointSpike p))).val,
      ((pCoreIn_le 2 H₀).trans (show H₀ ≤ generated (normalizer (L : Set G)) z H₀ from le_sup_right))
        (originalFanoEquiv D z H₀ C m b
          (Multiplicative.ofAdd (BinaryLinearThree.FanoDecomposition.pointSpike p))).property⟩ =
      Matrix.PSp4Three.transvection (m.fanoEmbedding b p.val) 1 := by
  rw [originalFanoEquiv_marking,BinaryLinearThree.FanoTransvection.shear_pointSpike]

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

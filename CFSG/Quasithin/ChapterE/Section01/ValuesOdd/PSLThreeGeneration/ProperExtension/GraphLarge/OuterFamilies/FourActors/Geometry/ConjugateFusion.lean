module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors.Geometry.Transfer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors.Geometry.ConjugateFusion.Coordinates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors.Geometry.ConjugateFusion.NormalForms

/-!
# Positioning the outer four-group fusion seed

The concrete seed in `Coordinates` lies in the centralizer of the standard
inner involution. Align that involution with the supplied z. Because the given
ambient Sylow T lies in C(z), it is Sylow in C(z); Sylow conjugacy there moves
the entire seed into T while fixing z. The transported quarter-turn provides
the second actual conjugate of the original actor. No Sylow assertion about
C_T(w) is used.

The finite-field congruence theorem in `NormalForms` puts every original actor
in the displayed simultaneous normal form. Combining it with this transport
proves the exact `OuterFourConjugateFusion` conclusion over every finite field
of odd characteristic with simple PSL₃. In particular, the source's odd-prime
field hypotheses suffice, without a quasithinness or residue-class premise.
The original-family commutator transfer then leaves only the independent
`FourGroupOddMixing` construction for the generation assembly owner.

Source: Aschbacher--Smith E.1.1--5 and E.1.14(7), printed pp.209--210,214;
A.3.21(a), p.55; Aschbacher (1982), Lemma 4.11.
-/

public section

open Subgroup
open scoped Pointwise

private theorem position {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (z : G)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer ({z} : Set G)) :
    ∃ c ∈ centralizer ({z} : Set G), P.map (MulAut.conj c).toMonoidHom ≤ T := by
  let C := centralizer ({z} : Set G)
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q (T.subtype hT)
  refine ⟨c, c.property, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  have hyQ : (⟨y, hPC hy⟩ : C) ∈ Q := hQ hy
  have hh : MulAut.conj c (⟨y, hPC hy⟩ : C) ∈ (c • Q : Sylow 2 C) :=
    ⟨_, hyQ, rfl⟩
  rw [hc] at hh
  exact hh


private theorem fusion_of_seed {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G) (A : Subgroup G) (z : G)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer ({z} : Set G))
    (g₀ w r : G) (hAP : A.map (MulAut.conj g₀).toMonoidHom ≤ P)
    (hwL : w ∈ L) (hw : orderOf w = 2) (hwz : w ≠ z)
    (hwA : w ∈ A.map (MulAut.conj g₀).toMonoidHom)
    (hrP : r ∈ P) (hrw : MulAut.conj r w = w * z) :
    ∃ g h v : G,
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      A.map (MulAut.conj h).toMonoidHom ≤ (T : Subgroup G) ∧
      v ∈ L ∧ orderOf v = 2 ∧ v ≠ z ∧
      v ∈ A.map (MulAut.conj g).toMonoidHom ∧
      v * z ∈ A.map (MulAut.conj h).toMonoidHom := by
  obtain ⟨c, hc, hPT⟩ := position T z hT P hP hPC
  let e := MulAut.conj c
  have hez : e z = z := by
    change c * z * c⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  have comp (a b x : G) : MulAut.conj (a * b) x = MulAut.conj a (MulAut.conj b x) := by
    simp only [MulAut.conj_apply, _root_.mul_inv_rev, mul_assoc]
  have hfirst : A.map (MulAut.conj (c * g₀)).toMonoidHom ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    change MulAut.conj (c * g₀) a ∈ T
    rw [comp]
    exact hPT ⟨_, hAP ⟨a, ha, rfl⟩, rfl⟩
  have hsecond : A.map (MulAut.conj (c * (r * g₀))).toMonoidHom ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    change MulAut.conj (c * (r * g₀)) a ∈ T
    rw [comp, comp]
    apply hPT
    refine ⟨_, ?_, rfl⟩
    exact P.mul_mem (P.mul_mem hrP (hAP ⟨a, ha, rfl⟩)) (P.inv_mem hrP)
  refine ⟨c * g₀, c * (r * g₀), e w, hfirst, hsecond,
    (inferInstance : L.Normal).conj_mem w hwL c, (e.orderOf_eq w).trans hw, ?_, ?_, ?_⟩
  · intro h
    exact hwz (e.injective (h.trans hez.symm))
  · obtain ⟨a, ha, hea⟩ := hwA
    exact ⟨a, ha, (comp c g₀ a).trans (congrArg e hea)⟩
  · obtain ⟨a, ha, hea⟩ := hwA
    refine ⟨a, ha, ?_⟩
    change MulAut.conj (c * (r * g₀)) a = e w * z
    change MulAut.conj g₀ a = w at hea
    rw [comp, comp, hea, hrw]
    exact (e.map_mul w z).trans (congrArg (e w * ·) hez)

open Matrix
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]
open ConjugateFusion

/-- The matrix seed and Sylow conjugacy discharge every fusion condition once
all original actors have been put into the displayed simultaneous normal form. -/
theorem outerFourConjugateFusion_of_standardActorCoverage
    (h2 : (2 : F) ≠ 0) (hcoverage : StandardActorCoverage F) :
    OuterFourConjugateFusion F := by
  intro T A hAE _ hAcard hinter z hz hzL _ hTz
  obtain ⟨g₀, d, hg₀⟩ := hcoverage A hAE hAcard hinter
  obtain ⟨s, hs⟩ := exists_standard_coordinates F h2 z hz hzL
  let u := innerSL F s
  let e := MulAut.conj u
  have hez : e (standardInner F) = z := hs
  obtain ⟨hP, hPC, hAP, hwL, hw, hwz, hwA, hrP, hrw⟩ := standardActor_seed F h2 d
  let P := (seed F d).map e.toMonoidHom
  have hPz : P ≤ centralizer ({z} : Set (graphExtension F)) := by
    rintro x ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e y * z = z * e y
    rw [← hez, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (hPC hy)]
  have comp (a b x : graphExtension F) :
      MulAut.conj (a * b) x = MulAut.conj a (MulAut.conj b x) := by
    simp only [MulAut.conj_apply, _root_.mul_inv_rev, mul_assoc]
  have hAP' : A.map (MulAut.conj (u * g₀)).toMonoidHom ≤ P := by
    rintro x ⟨a, ha, rfl⟩
    refine ⟨MulAut.conj g₀ a, hAP ?_, ?_⟩
    · rw [← hg₀]
      exact ⟨a, ha, rfl⟩
    · exact (comp u g₀ a).symm
  have hwA' : e (reflection F) ∈ A.map (MulAut.conj (u * g₀)).toMonoidHom := by
    rw [← hg₀] at hwA
    obtain ⟨a, ha, hea⟩ := hwA
    exact ⟨a, ha, (comp u g₀ a).trans (congrArg e hea)⟩
  apply fusion_of_seed (innerPart F) T A z hTz P (hP.map e.toMonoidHom) hPz
    (u * g₀) (e (reflection F)) (e (quarterTurn F)) hAP'
  · exact (inferInstance : (innerPart F).Normal).conj_mem _ hwL u
  · exact (e.orderOf_eq _).trans hw
  · intro h
    exact hwz (e.injective (h.trans hez.symm))
  · exact hwA'
  · exact mem_map_of_mem e.toMonoidHom hrP
  · change e (quarterTurn F) * e (reflection F) * (e (quarterTurn F))⁻¹ =
      e (reflection F) * z
    rw [← map_inv, ← map_mul, ← map_mul]
    change e (MulAut.conj (quarterTurn F) (reflection F)) = _
    rw [hrw, map_mul, hez]

/-- The existing original-family commutator transfer applied to the concrete
normal forms, with their coverage retained as an explicit input. -/
theorem fourActorCentralizerGeneration_of_standardActorCoverage
    (h2 : (2 : F) ≠ 0) (hcoverage : StandardActorCoverage F)
    (hgeometry : FourGroupOddMixing F) : FourActorCentralizerGeneration F :=
  fourActorCentralizerGeneration_of_conjugate_fusion F hgeometry
    (outerFourConjugateFusion_of_standardActorCoverage F h2 hcoverage)

/-- Every original outer four-group has two actual conjugates in the supplied
Sylow subgroup meeting the required inner lines through its central involution.
Finite-field normal forms discharge the entire coverage premise. -/
theorem outerFourConjugateFusion (h2 : (2 : F) ≠ 0) :
    OuterFourConjugateFusion F :=
  outerFourConjugateFusion_of_standardActorCoverage F h2
    (standardActorCoverage F h2)

/-- The source's odd-prime field supplies all hypotheses for conjugate fusion;
primality, the lower bound, and the congruence modulo four are unnecessary here. -/
theorem outerFourConjugateFusion_of_odd_card {p : ℕ}
    (ho : Odd p) (hF : Nat.card F = p) : OuterFourConjugateFusion F :=
  outerFourConjugateFusion F
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho
      (by simpa only [pow_one] using hF : Nat.card F = p ^ 1))

/-- Apply the proved fusion to the original family's commutator controls.
This discharges the fusion input of E.1.14(7)'s outer four-group branch;
the independent inner four-group mixing construction remains explicit. -/
theorem fourActorCentralizerGeneration_of_odd_card {p : ℕ}
    (ho : Odd p) (hF : Nat.card F = p) (hgeometry : FourGroupOddMixing F) :
    FourActorCentralizerGeneration F :=
  fourActorCentralizerGeneration_of_conjugate_fusion F hgeometry
    (outerFourConjugateFusion_of_odd_card F ho hF)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies

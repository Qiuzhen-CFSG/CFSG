module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.Reduction
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.FullAxis
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Source
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Transport
/-!
# Special-linear conjugacy of the source axes

A nonzero covector is completed explicitly to a determinant-one matrix in
SL₃. Thus arbitrary full hyperplane centralizers are conjugate in the actual
special linear group. Transport through the literal quotient intertwiner
places every source axis four-group in a G-conjugate of a given full axis
actor, and transports upstairs quadraticity. This proves the global F₄
clause of B.4.9(1), even when the two axes differ.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9(1)–(2), printed pp.92–94.
-/

public section
open Representation Representation.BinaryOffender Matrix
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.LargerFieldThree.AxisFourGeometry
variable (F : BinaryField)

private theorem exists_first_row (u : Fin 3 → F.Carrier) (hu : u ≠ 0) :
    ∃ s : SpecialLinearGroup (Fin 3) F.Carrier, ∀ v,
      specialLinearNatural 3 s v 0 = u ⬝ᵥ v := by
  classical
  by_cases h0 : u 0 = 0
  · by_cases h1 : u 1 = 0
    · have h2 : u 2 ≠ 0 := by
        intro h2
        apply hu
        funext i
        fin_cases i <;> assumption
      refine ⟨⟨!![u 0, u 1, u 2; (u 2)⁻¹, 0, 0; 0, 1, 0], ?_⟩, ?_⟩
      · simp [det_fin_three, h2]
      · intro v
        change _ ⬝ᵥ v = _
        congr 1
        ext i
        fin_cases i <;> rfl
    · refine ⟨⟨!![u 0, u 1, u 2; (u 1)⁻¹, 0, 0; 0, 0, 1], ?_⟩, ?_⟩
      · simp [det_fin_three, h1, CharTwo.neg_eq]
      · intro v
        change _ ⬝ᵥ v = _
        congr 1
        ext i
        fin_cases i <;> rfl
  · refine ⟨⟨!![u 0, u 1, u 2; 0, (u 0)⁻¹, 0; 0, 0, 1], ?_⟩, ?_⟩
    · simp [det_fin_three, h0]
    · intro v
      change _ ⬝ᵥ v = _
      congr 1
      ext i
      fin_cases i <;> rfl

/-- An actual determinant-one change of coordinates sends a hyperplane to the
zeroth coordinate hyperplane. -/
theorem hyperplane_coordinates (P : Submodule F.Carrier (Fin 3 → F.Carrier))
    (hP : Module.finrank F.Carrier ((Fin 3 → F.Carrier) ⧸ P) = 1) :
    ∃ s : SpecialLinearGroup (Fin 3) F.Carrier, ∀ v,
      specialLinearNatural 3 s v ∈ coordinateHyperplane F 3 0 ↔ v ∈ P := by
  classical
  let e : ((Fin 3 → F.Carrier) ⧸ P) ≃ₗ[F.Carrier] F.Carrier :=
    LinearEquiv.ofFinrankEq _ _ (by simpa only [Module.finrank_self] using hP)
  let f := e.toLinearMap.comp P.mkQ
  have hf : Function.Surjective f := e.surjective.comp P.mkQ_surjective
  have hfker (v : Fin 3 → F.Carrier) : f v = 0 ↔ v ∈ P := by
    change e (P.mkQ v) = 0 ↔ v ∈ P
    rw [map_eq_zero_iff e e.injective]
    exact Submodule.Quotient.mk_eq_zero P
  let u : Fin 3 → F.Carrier := fun i => f (Pi.single i 1)
  have hfu (v : Fin 3 → F.Carrier) : u ⬝ᵥ v = f v := by
    have hs (i : Fin 3) : f (Pi.single i (v i)) = v i * u i := by
      rw [show Pi.single i (v i) = v i • Pi.single i (1 : F.Carrier) by
        rw [← Pi.single_smul]; simp only [smul_eq_mul, mul_one]]
      exact f.map_smul (v i) (Pi.single i 1)
    calc
      u ⬝ᵥ v = ∑ i, f (Pi.single i (v i)) := by
        simp only [dotProduct, hs]
        apply Finset.sum_congr rfl
        intro i hi
        exact mul_comm _ _
      _ = f (∑ i, Pi.single i (v i)) := (map_sum f _ _).symm
      _ = f v := by rw [Finset.univ_sum_single]
  have hu : u ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := hf 1
    have := hfu v
    rw [hz, zero_dotProduct, hv] at this
    exact zero_ne_one this
  obtain ⟨s, hs⟩ := exists_first_row F u hu
  exact ⟨s, fun v => by rw [mem_coordinateHyperplane, hs, hfu, hfker]⟩

/-- All full axis groups are conjugate in SL₃ itself. -/
theorem full_axis_conjugate_standard
    {A : Subgroup (SpecialLinearGroup (Fin 3) F.Carrier)} (hA : IsFullAxisGroup F 3 A) :
    ∃ s : SpecialLinearGroup (Fin 3) F.Carrier,
      A.map (MulAut.conj s).toMonoidHom = hyperplaneCentralizer F 3 0 := by
  obtain ⟨P, hP, hA⟩ := hA
  obtain ⟨s, hs⟩ := hyperplane_coordinates F P hP
  refine ⟨s, ?_⟩
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨Subgroup.mem_top _, ?_⟩
    intro v hv
    have hsp : specialLinearNatural 3 s⁻¹ v ∈ P := by
      apply (hs _).mp
      simpa only [self_inv_apply] using
        (show v ∈ coordinateHyperplane F 3 0 from hv)
    change specialLinearNatural 3 (s * b * s⁻¹) v = v
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      (hA b).mp hb _ hsp, self_inv_apply]
  · intro ha
    refine ⟨s⁻¹ * a * s, (hA _).mpr ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    intro v hv
    have hfix := ha.2 _ ((hs v).mpr hv)
    change specialLinearNatural 3 a (specialLinearNatural 3 s v) = _ at hfix
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix,
      inv_self_apply]

/-- Conjugacy of arbitrary full axis groups uses the same special linear actor. -/
theorem full_axis_conjugate
    {A B : Subgroup (SpecialLinearGroup (Fin 3) F.Carrier)}
    (hA : IsFullAxisGroup F 3 A) (hB : IsFullAxisGroup F 3 B) :
    ∃ s : SpecialLinearGroup (Fin 3) F.Carrier,
      A = B.map (MulAut.conj s).toMonoidHom := by
  obtain ⟨a, ha⟩ := full_axis_conjugate_standard F hA
  obtain ⟨b, hb⟩ := full_axis_conjugate_standard F hB
  refine ⟨a⁻¹ * b, ?_⟩
  apply Subgroup.map_injective (f := (MulAut.conj a).toMonoidHom)
    (MulAut.conj a).injective
  rw [ha, Subgroup.map_map]
  have hcomp : (MulAut.conj a).toMonoidHom.comp
      (MulAut.conj (a⁻¹ * b)).toMonoidHom = (MulAut.conj b).toMonoidHom := by
    ext g
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, hb]

/-- An actor with a fixed hyperplane is contained in a conjugate of any given
full axis group, even when their original axes differ. -/
theorem le_conjugate_full_axis_of_cost
    {A B : Subgroup (SpecialLinearGroup (Fin 3) F.Carrier)}
    (hA : fixedCodim (linearNatural F 3) A = F.degree) (hB : IsFullAxisGroup F 3 B) :
    ∃ s : SpecialLinearGroup (Fin 3) F.Carrier,
      A ≤ B.map (MulAut.conj s).toMonoidHom := by
  let P := fieldFixedSpace F 3 A
  have hP : Module.finrank F.Carrier ((Fin 3 → F.Carrier) ⧸ P) = 1 := by
    rw [fixedCodim_eq_field_codim] at hA
    exact Nat.eq_of_mul_eq_mul_left F.degree_pos (hA.trans (mul_one F.degree).symm)
  let Q := subspaceKernel (linearNatural F 3) (P.restrictScalars (ZMod 2)) ⊤
  have hQ : IsFullAxisGroup F 3 Q :=
    ⟨P, hP, fun g => ⟨fun h => h.2, fun h => ⟨Subgroup.mem_top _, h⟩⟩⟩
  have hAQ : A ≤ Q := by
    intro a ha
    exact ⟨Subgroup.mem_top _, fun v hv => hv ⟨a, ha⟩⟩
  obtain ⟨s, hs⟩ := full_axis_conjugate F hQ hB
  exact ⟨s, hs ▸ hAQ⟩

section Original
open QuadraticSplitting
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : DoubleNatural F 3 ρ)
  (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)

/-- The common nonidentity-element axis is the fixed space of the whole four. -/
theorem axis_four_cost {E : Subgroup G} (hE : IsAxisFour d E) :
    fixedCodim d.space.quotientRepresentation E = F.degree := by
  obtain ⟨_, hcard, I, hI, hfix⟩ := hE
  have hne : E ≠ ⊥ := by
    intro h
    rw [h, Nat.card_eq_fintype_card] at hcard
    norm_num at hcard
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hane : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  have hcommon : fixedSpace d.space.quotientRepresentation E = I := by
    apply le_antisymm
    · rw [← hfix a a.property hane]
      exact fixedSpace_antitone _ (Subgroup.zpowers_le.mpr a.property)
    · intro v hv b
      by_cases hb : (b : G) = 1
      · simp [hb]
      · exact (mem_fixedSpace_zpowers_iff d.space.quotientRepresentation (b : G) v).mp ((hfix b b.property hb).symm ▸ hv)
  change Module.finrank (ZMod 2) ((V ⧸ d.space.toSubmodule) ⧸
    fixedSpace d.space.quotientRepresentation E) = F.degree
  rw [hcommon]
  exact hI

/-- Every source axis four lies in a conjugate of the original full axis actor.
The conjugator is in G and uses the original natural marking. -/
theorem axis_four_le_conjugate {B E : Subgroup G}
    (hB : IsFullAxisGroup F 3 (B.map (d.threeQuotientAction e).groupEquiv.toMonoidHom))
    (hE : IsAxisFour d E) :
    ∃ g : G, E ≤ B.map (MulAut.conj g).toMonoidHom := by
  let m := d.threeQuotientAction e
  have hc : fixedCodim (linearNatural F 3) (E.map m.groupEquiv.toMonoidHom) = F.degree := by
    rw [← fixedCodim_map_equivariant _ _ _ m.linearEquiv m.intertwines]
    exact axis_four_cost F d hE
  obtain ⟨s, hs⟩ := le_conjugate_full_axis_of_cost F hc hB
  refine ⟨m.groupEquiv.symm s, ?_⟩
  intro a ha
  obtain ⟨b, ⟨c, hc, rfl⟩, hb⟩ := hs (Subgroup.mem_map_of_mem _ ha)
  refine ⟨c, hc, m.groupEquiv.injective ?_⟩
  simpa only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
    m.groupEquiv.apply_symm_apply] using hb

/-- Quadraticity of one full axis group gives quadraticity of every axis four.
In particular, this proves the global F₄ clause, with no restriction on the axis. -/
theorem axis_four_quadratic {B E : Subgroup G}
    (hq : IsQuadratic ρ B)
    (hB : IsFullAxisGroup F 3 (B.map (d.threeQuotientAction e).groupEquiv.toMonoidHom))
    (hE : IsAxisFour d E) : IsQuadratic ρ E := by
  obtain ⟨g, hg⟩ := axis_four_le_conjugate F d e hB hE
  have hqg : IsQuadratic ρ (B.map (MulAut.conj g).toMonoidHom) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
    change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) = ρ (g * b * g⁻¹) v - v
    simpa only [map_mul, Module.End.mul_apply, map_sub, ρ.inv_self_apply,
      ρ.self_inv_apply] using congrArg (ρ g) (hq a ha b hb (ρ g⁻¹ v))
  exact fun a ha b hb v => hqg a (hg ha) b (hg hb) v
end Original

end CFSG.Quasithin.ChapterB.NaturalExtensions.LargerFieldThree.AxisFourGeometry

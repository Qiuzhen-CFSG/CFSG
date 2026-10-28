module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.MovingPlane
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.CubicActions
public import Theory.Representation.G2BinaryPlaneOrbits.Sylow
public import Theory.Representation.G2BinaryPlaneOrbits.Stabilizer

/-!
# Recognizing the G₂(2)′ parabolic from the source moving plane

Conjugate the given Sylow two-subgroup to the marked derived Sylow. The
actual natural action transports the given plane, and the proved uniqueness
of a Sylow-invariant binary plane identifies it with the marked null plane.
Its stabilizer is the first derived parabolic of order 96. The subgroup
D S contains a Sylow of order 32 and has order divisible by three, so it is
that entire stabilizer. Since S normalizes D, the quotient D S / D is a
two-group. Thus D contains the transported cubic, whose action on the
genuine six-dimensional scalar quotient fixes only zero.

The source contract is `recognition`, with its action consequence
`fixed_eq_zero`. The stronger `recognition_of_three_dvd` shows that the
prime-support bound, two-perfectness and displacement identity are not
needed for this particular geometric deduction. The input `MovingPlane`
still retains the source plane and its displacement identity. The actual
ambient embedding of the derived group is preserved in both conclusions,
so the cubic membership supplies the marking required by
`BinaryRankTwo.g2_checked_centralizer_eq`.

Source: Aschbacher–Smith, Lemma 13.6.22, printed p.932 (PDF p.949).
The octonion root conventions and plane calculations are reused from the
licensed ATLAS port through the imported modules; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff. No additional upstream source is copied.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Atlas.G2.BinaryParabolicPair
open Atlas.G2.Natural.BinaryPlane

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.G2Geometry

private theorem standard_placement (S : Sylow 2 Actor) (D : Subgroup Actor)
    (h3 : 3 ∣ Nat.card D) (e : MovingPlane action S D) :
    ∃ g : Actor, (D ⊔ (S : Subgroup Actor)).map (MulAut.conj g).toMonoidHom =
      derivedFirst := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Actor S standardSylow
  let f : Actor ≃* Actor := MulAut.conj g
  let c := innerCoordinates g
  let P := D ⊔ (S : Subgroup Actor)
  have hS : (S : Subgroup Actor).map f.toMonoidHom =
      (standardSylow : Subgroup Actor) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hSP : (standardSylow : Subgroup Actor) ≤ P.map f.toMonoidHom := by
    rw [← hS]
    exact map_mono le_sup_right
  have hmap : P.map f.toMonoidHom ≤
      subspaceStabilizer action (e.plane.map c.toLinearMap) := by
    rw [← map_subspaceStabilizer_equivariant action action f c
      (innerCoordinates_equivariant g) e.plane]
    exact map_mono e.invariant
  have hc : Nat.card (e.plane.map c.toLinearMap) = 4 := by
    rw [← Nat.card_congr
      (Submodule.equivMapOfInjective c.toLinearMap c.injective e.plane).toEquiv]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, e.dimension]
    norm_num
  have hw := eq_standardPlane_of_standardSylow _ hc (hSP.trans hmap)
  have hP : P.map f.toMonoidHom ≤ derivedFirst := by
    simpa only [hw, standardPlane_stabilizer] using hmap
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hP ?_⟩
  have h32 : 32 ∣ Nat.card (P.map f.toMonoidHom) := by
    simpa only [card_standardSylow] using Subgroup.card_dvd_of_le hSP
  have h3P : 3 ∣ Nat.card (P.map f.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective f.injective]
    exact h3.trans (Subgroup.card_dvd_of_le (show D ≤ P from le_sup_left))
  have h96 : 96 ∣ Nat.card (P.map f.toMonoidHom) :=
    (by decide : Nat.Coprime 32 3).mul_dvd_of_dvd_of_dvd h32 h3P
  rw [card_derivedFirst]
  exact Nat.le_of_dvd (Nat.card_pos) h96

private theorem cubic_mem_of_normalizes (S : Sylow 2 Actor) (D : Subgroup Actor)
    (hn : (S : Subgroup Actor) ≤ normalizer (D : Set Actor))
    (x : Actor) (hx : x ∈ D ⊔ (S : Subgroup Actor)) (hx3 : x ^ 3 = 1) : x ∈ D := by
  let P := D ⊔ (S : Subgroup Actor)
  let N := D.subgroupOf P
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le D.le_normalizer hn)
  have hsup : N ⊔ (S : Subgroup Actor).subgroupOf P = ⊤ := by
    rw [← subgroupOf_sup (show D ≤ P from le_sup_left)
      (show (S : Subgroup Actor) ≤ P from le_sup_right)]
    exact subgroupOf_self P
  have hq : IsPGroup 2 (P ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N _ S.isPGroup'.comap_subtype hsup
  have hres : pResidual 2 P ≤ N := sInf_le ⟨inferInstance, hq⟩
  have hxres : (⟨x, hx⟩ : P) ∈ pResidual 2 P := by
    apply mem_pResidual_of_orderOf_coprime
    exact (by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one (show (⟨x, hx⟩ : P) ^ 3 = 1 from Subtype.ext hx3))
  exact hres hxres

/-- The actual invariant plane and a three-divisible normalized subgroup
recognize the first derived parabolic and put its cubic in the subgroup.
The witness conjugates in the full octonion group, preserving the literal
derived-carrier embedding. -/
theorem recognition_of_three_dvd (S : Sylow 2 Actor) (D : Subgroup Actor)
    (hn : (S : Subgroup Actor) ≤ normalizer (D : Set Actor))
    (h3 : 3 ∣ Nat.card D) (e : MovingPlane action S D) :
    ∃ g : Atlas.G2.Model (ZMod 2),
      (D ⊔ (S : Subgroup Actor)).map Actor.subtype =
        derivedFirstAmbient.map (MulAut.conj g).toMonoidHom ∧
      g * cubicActor * g⁻¹ ∈ D.map Actor.subtype := by
  obtain ⟨g,hg⟩ := standard_placement S D h3 e
  let f : Actor ≃* Actor := MulAut.conj g
  have hback : derivedFirst.map f.symm.toMonoidHom = D ⊔ (S : Subgroup Actor) := by
    rw [← hg, map_map]
    change (D ⊔ (S : Subgroup Actor)).map (f.symm.toMonoidHom.comp f.toMonoidHom) = _
    have hid : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id Actor := by
      ext x : 1
      exact f.symm_apply_apply x
    rw [hid, map_id]
  have hc : f.symm ⟨cubicActor, cubicActor_mem_derived⟩ ∈ D ⊔ (S : Subgroup Actor) := by
    rw [← hback]
    exact mem_map_of_mem f.symm.toMonoidHom cubicActor_mem_derivedFirst
  have hc3 : (f.symm ⟨cubicActor, cubicActor_mem_derived⟩) ^ 3 = 1 := by
    rw [← map_pow, show (⟨cubicActor, cubicActor_mem_derived⟩ : Actor) ^ 3 = 1 from
      Subtype.ext cubicActor_cube, map_one]
  have hcD := cubic_mem_of_normalizes S D hn _ hc hc3
  refine ⟨g.val⁻¹, ?_, ?_⟩
  · rw [← hback, Subgroup.map_map, ← derivedFirst_map_subtype, Subgroup.map_map]
    rfl
  · exact ⟨f.symm ⟨cubicActor, cubicActor_mem_derived⟩, hcD, rfl⟩

/-- The concrete G₂(2)′ moving-plane recognition used in 13.6.22.
All source hypotheses are retained; placement and cubic membership are
proved from the original plane and Sylow marking. -/
theorem recognition (S : Sylow 2 Actor) (D : Subgroup Actor)
    (_hperfect : IsPPerfect 2 D)
    (hn : (S : Subgroup Actor) ≤ normalizer (D : Set Actor))
    (_hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card D → p = 2 ∨ p = 3)
    (hQ : ∃ Q : Sylow 3 D, Nat.card Q = 3) (e : MovingPlane action S D) :
    ∃ g : Atlas.G2.Model (ZMod 2),
      (D ⊔ (S : Subgroup Actor)).map Actor.subtype =
        derivedFirstAmbient.map (MulAut.conj g).toMonoidHom ∧
      g * cubicActor * g⁻¹ ∈ D.map Actor.subtype := by
  obtain ⟨Q, hQ⟩ := hQ
  apply recognition_of_three_dvd S D hn _ e
  simpa only [hQ] using (Q : Subgroup D).card_subgroup_dvd_card

/-- Application of the constructed cubic to the genuine natural scalar
quotient: the normalized actor has zero fixed space. -/
theorem fixed_eq_zero_of_three_dvd (S : Sylow 2 Actor) (D : Subgroup Actor)
    (hn : (S : Subgroup Actor) ≤ normalizer (D : Set Actor))
    (h3 : 3 ∣ Nat.card D) (e : MovingPlane action S D)
    (w : Atlas.G2.Natural.Space (ZMod 2))
    (hw : ∀ d ∈ D, action d w = w) : w = 0 := by
  obtain ⟨g, _, hc⟩ := recognition_of_three_dvd S D hn h3 e
  apply G2Action.g2_conjugate_cubic_fixed_eq_zero g w
  obtain ⟨d, hd, he⟩ := hc
  rw [← he]
  exact hw d hd

/-- The source moving-plane hypotheses imply C_V(D)=0 for the actual
six-dimensional natural quotient representation. -/
theorem fixed_eq_zero (S : Sylow 2 Actor) (D : Subgroup Actor)
    (hperfect : IsPPerfect 2 D)
    (hn : (S : Subgroup Actor) ≤ normalizer (D : Set Actor))
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card D → p = 2 ∨ p = 3)
    (hQ : ∃ Q : Sylow 3 D, Nat.card Q = 3) (e : MovingPlane action S D)
    (w : Atlas.G2.Natural.Space (ZMod 2))
    (hw : ∀ d ∈ D, action d w = w) : w = 0 := by
  obtain ⟨g, _, hc⟩ := recognition S D hperfect hn hprimes hQ e
  apply G2Action.g2_conjugate_cubic_fixed_eq_zero g w
  obtain ⟨d, hd, he⟩ := hc
  rw [← he]
  exact hw d hd

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.G2Geometry

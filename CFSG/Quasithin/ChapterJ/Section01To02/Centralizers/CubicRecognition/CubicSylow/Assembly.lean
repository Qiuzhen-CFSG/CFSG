module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.OrbitIndex
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.ElementFusion

/-!
# The cubic Sylow and order-three fusion conclusions of J.2.7

The earlier marking constructs the local semidihedral action. OrbitIndex
excludes E₂₇, so the order-27 group is extraspecial with both center and
commutator mapped onto the original B. Characteristicity promotes the
same image to an ambient Sylow, and ElementFusion proves the single
ambient class of order-three elements, retaining actual conjugators.

The only inputs are |B|=3, B's literal Sylow placement in H, the order of
the original z, the Aut(A₆) normalizer marking with its M₁₀ compatibility,
and the transposition part of J.2.7(7). Their earlier-source discharge
and the genuine triple-cover identification stay with the J.2.7 assembly
owner; no Sylow structure, exponent, E₂₇ exclusion or cubic fusion is assumed.

Source: Aschbacher–Smith, J.2.7, printed pp.435 and 437 (PDF pp.446 and 448).
-/

public section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
open Subgroup LocalAction
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- Exponent three is an equality, as R has order 27 and every cube is one. -/
theorem exponent_eq_three {hB : Nat.card c.B = 3}
    {e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))}
    (D : LocalAction.Data c hB e) : Monoid.exponent (ambient c D.R) = 3 := by
  let : Nontrivial (ambient c D.R) := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [D.r_card]; decide)
  apply (Monoid.exponent_eq_prime_iff (by decide : Nat.Prime 3)).mpr
  intro x hx
  exact orderOf_eq_prime (D.cube_eq_one x) hx

/-- The exact cubic Sylow conclusion, conditional only on the earlier-source
marking, Sylow placement, and transposition clause (7). Both characteristic
subgroups have the original ambient image B, and fusion retains its conjugators. -/
theorem exists_extraspecial_sylow_data (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (h7 : TranspositionFusion c e) :
    ∃ D : LocalAction.Data c hB e, ∃ S : Sylow 3 G,
      (S : Subgroup G) = ambient c D.R ∧
      Nat.card S = 27 ∧ IsExtraspecial 3 S ∧ Monoid.exponent S = 3 ∧
      (∀ x : S, x ^ 3 = 1) ∧
      (center S).map (S : Subgroup G).subtype = c.B ∧
      (_root_.commutator S).map (S : Subgroup G).subtype = c.B ∧
      ∀ x y : G, orderOf x = 3 → orderOf y = 3 → ∃ g : G, g * x * g⁻¹ = y := by
  obtain ⟨D⟩ := LocalAction.exists_data c hB P hP hz e hM h7
  have hn := not_commutative c D
  obtain ⟨S, hS⟩ := exists_ambient_sylow_of_noncommutative c hB e hM D.R hn
  obtain ⟨hextra, hcenter, hcomm⟩ := nonabelian_structure c hB e hM D.R hn
  let result (K : Subgroup G) : Prop :=
    Nat.card K = 27 ∧ IsExtraspecial 3 K ∧ Monoid.exponent K = 3 ∧
    (∀ x : K, x ^ 3 = 1) ∧
    (center K).map K.subtype = c.B ∧
    (_root_.commutator K).map K.subtype = c.B
  have hR : result (ambient c D.R) :=
    ⟨D.r_card, hextra, exponent_eq_three c D, D.cube_eq_one, hcenter, hcomm⟩
  have hSR : result (S : Subgroup G) := hS.symm ▸ hR
  exact ⟨D, S, hS, hSR.1, hSR.2.1, hSR.2.2.1, hSR.2.2.2.1, hSR.2.2.2.2.1, hSR.2.2.2.2.2,
    order_three_fusion_of_noncommutative c D hM hn⟩

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow

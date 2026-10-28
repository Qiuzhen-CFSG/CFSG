module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieveBounds
public import CFSG.Quasithin.ChapterG.Section07.MathieuRecognition.DegreeBounds
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Automorphisms
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.Mathieu.M24.Properties.AutomorphismTwoRank
public import Theory.Mathieu.M24.Properties.Simplicity

/-!
# Eliminating the simple Mathieu rows of the exchanged sieve

The sharper exchanged degree bound contradicts the faithful binary degree
lower bounds for the actual Mathieu carriers. For M₁₂ the order of its full
automorphism group already suffices; M₂₂, M₂₃ and M₂₄ use their proved
intrinsic automorphism rank bounds. No small-module catalogue is needed.
The final application excludes these models on the literal image of H,
regardless of which component its faithful stabilizer moves.

Source: Aschbacher--Smith G.9.3(0),(1), G.11.6, printed pp.353,366.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedFaithfulSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)

include s

open Sporadic.Mathieu

/-- The actual M12 group is incompatible with the exchanged degree bound. -/
theorem not_m12_equiv (e : componentOrbit L ⊤ ≃* M12) : False := by
  have hr : primeRank 2 (MulAut M12) ≤ 7 := by
    apply primeRank_le_of_prime_pow_not_dvd
    rw [← Nat.card_congr M12ExceptionalExtension.automorphismEquiv.toEquiv,
      M12ExceptionalExtension.carrier_order]
    decide
  have hu := s.orbit_degree_le_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hl := ChapterG.Section07.MathieuRecognition.ten_le_finrank_of_m12
    s.orbitAction s.orbit_faithful e
  change 10 ≤ finrank (ZMod 2) I at hl
  omega

/-- The actual M22 group is incompatible with the exchanged degree bound. -/
theorem not_m22_equiv (e : componentOrbit L ⊤ ≃* M22) : False := by
  have hu := s.orbit_degree_le_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := m22_automorphism_twoRank_le_five
  have hl := ChapterG.Section07.MathieuRecognition.ten_le_finrank_of_m22
    s.orbitAction s.orbit_faithful e
  change 10 ≤ finrank (ZMod 2) I at hl
  omega

/-- The same argument excludes every perfect central cover of M₂₂, in
particular the triple-cover component in G.9.3(2). Divisibility by eleven
lifts from the central quotient; no representation catalogue is assumed. -/
theorem not_m22_central_quotient
    (e : (componentOrbit L ⊤) ⧸ center (componentOrbit L ⊤) ≃* M22) : False := by
  have hu := s.orbit_degree_le_central_quotient_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := m22_automorphism_twoRank_le_five
  have hd : 11 ∣ Nat.card (componentOrbit L ⊤) := by
    have hq := (center (componentOrbit L ⊤)).card_quotient_dvd_card
    rw [Nat.card_congr e.toEquiv, m22_order] at hq
    exact (by norm_num : 11 ∣ 443520).trans hq
  have hl := BinaryPrimeDegree.orderOf_le_finrank s.orbitAction s.orbit_faithful
    (by decide : Nat.Prime 11) (by decide) hd
  rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hl
  change 10 ≤ finrank (ZMod 2) I at hl
  omega

/-- The actual M23 group is incompatible with the exchanged degree bound. -/
theorem not_m23_equiv (e : componentOrbit L ⊤ ≃* M23) : False := by
  have hu := s.orbit_degree_le_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := m23_automorphism_twoRank_le_four
  have hl := ChapterG.Section07.MathieuRecognition.eleven_le_finrank_of_m23
    s.orbitAction s.orbit_faithful e
  change 11 ≤ finrank (ZMod 2) I at hl
  omega

/-- The actual M24 group is incompatible with the exchanged degree bound. -/
theorem not_m24_equiv (e : componentOrbit L ⊤ ≃* M24) : False := by
  let : Group.IsPerfect (componentOrbit L ⊤) := s.component.orbit_isPerfect ⊤
  let : Group.IsPerfect M24 := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup M24 := m24_isSimpleGroup
  have hz : center M24 = ⊥ := by
    rcases (inferInstance : (center M24).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative M24 (center_eq_top_iff.mp h)).elim
  have hu := s.orbit_degree_le_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := m24_automorphism_rank_le_six hz
  have hl := ChapterG.Section07.MathieuRecognition.eleven_le_finrank_of_m24
    s.orbitAction s.orbit_faithful e
  change 11 ≤ finrank (ZMod 2) I at hl
  omega

/-- None of the simple Mathieu candidates occurs on the same constituent H image. -/
theorem image_not_mathieu :
    ¬ (Nonempty (s.image (componentOrbit L ⊤) ≃* M12) ∨
      Nonempty (s.image (componentOrbit L ⊤) ≃* M22) ∨
      Nonempty (s.image (componentOrbit L ⊤) ≃* M23) ∨
      Nonempty (s.image (componentOrbit L ⊤) ≃* M24)) := by
  intro h
  rcases h with h | h | h | h <;> obtain ⟨e⟩ := h
  · exact s.not_m12_equiv (s.orbitEquiv.trans e)
  · exact s.not_m22_equiv (s.orbitEquiv.trans e)
  · exact s.not_m23_equiv (s.orbitEquiv.trans e)
  · exact s.not_m24_equiv (s.orbitEquiv.trans e)

/-- The literal image central quotient cannot be M₂₂ either. The quotient
comparison is induced by the same faithful orbit-image equivalence. -/
theorem image_not_m22_central_quotient
    (e : (s.image (componentOrbit L ⊤)) ⧸ center (s.image (componentOrbit L ⊤)) ≃*
      M22) : False := by
  let : Group.IsPerfect (componentOrbit L ⊤) := s.component.orbit_isPerfect ⊤
  let f : PerfectCentralCovering.Cover (componentOrbit L ⊤) (s.image (componentOrbit L ⊤)) := {
    toMonoidHom := s.orbitEquiv.toMonoidHom
    surjective := s.orbitEquiv.surjective
    isPerfect := inferInstance
    ker_le_center := by rw [s.orbitEquiv.toMonoidHom.ker_eq_bot_iff.mpr s.orbitEquiv.injective]; exact bot_le }
  exact s.not_m22_central_quotient (f.quotientCenterEquiv.trans e)

end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

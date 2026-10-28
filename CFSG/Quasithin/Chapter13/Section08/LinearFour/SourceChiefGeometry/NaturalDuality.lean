module
public import Theory.Representation.BinaryConjugationSection.MarkedCentralDuality
public import Theory.Representation.BinaryConjugationSection.PairingCentralizer
public import Theory.Representation.BinaryConjugationSection.LineConjugacy
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.SeedRadical
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.ComplementAccounting

/-!
# The dual core section from the original natural marking

Transitivity of H/O₂(H) on the natural four-space, together with the
nonzero seed commutator, gives C_{U_H}(Q_H) = V₁. The central commutator
pairing therefore constructs Q_H/H_C as the dual of the specified natural
action. Its coordinate pairing detects the original ambient commutators.
Restriction to V₃/V₁ proves the centralizer index four used in the final
contradiction. The same dual marking supplies the complementary cubic's
length one on Q_H/H_C in the surrounding chief-factor calculation.

The terminal application derives this index instead of assuming it. It
retains the source CriticalPair, its conjugator, and the original quotient
maps. No elementary abelianness of H_C/V_H is assumed. The natural/exterior
markings, seed-normalizer control, excluded lines and chief obstruction
remain explicit, so this does not complete 13.8.28. The local tensor and
chief geometry remains with qt-d-138-linear-four-source; earlier 13.8.27
setup belongs to qt-d-138-six-g2-source and final assembly to qt-d-1381-source.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
13.7.3(6),13.7.4(2),13.8.31 and the proof of13.8.28, printed pp.936,965–966.
-/

public noncomputable section
open Subgroup Representation
open scoped commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]

/-- The natural action and the original noncentral seed commutator construct
both sides of the actual commutator pairing, in the given natural coordinates. -/
theorem source_natural_core_duality
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    [IsElementaryAbelian 2 (Source.UH F.H F.Vplus)]
    (ρ : Representation (ZMod 2) F.H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection F.H (Source.UH F.H F.Vplus) F.V₁ ρ)
    (π : F.H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH F.H).subgroupOf F.H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hseedQ : ⁅F.Vplus,Source.QH F.H⁆ ≠ ⊥) :
    ∃ ddual : BinaryConjugationSection F.H (Source.QH F.H) (Source.HC F.H F.Vplus) ρ.dual,
      ∀ (q : Source.QH F.H) (u : Source.UH F.H F.Vplus),
        (ddual.coordinates q).toAdd (d.coordinates u).toAdd = 0 ↔ ⁅(q:G),(u:G)⁆ = 1 := by
  have htrans : ∀ u v : Fin 4 → ZMod 2, u ≠ 0 → v ≠ 0 → ∃ h : F.H, ρ h u = v := by
    intro u v hu hv
    obtain ⟨a,ha⟩ := exists_linearEquiv_apply_eq hu hv
    obtain ⟨h,hh⟩ := honto ((slEquivLinear 4).symm a)
    refine ⟨h,?_⟩
    rw [hnatural,hh]
    change slEquivLinear 4 ((slEquivLinear 4).symm a) u = v
    rw [(slEquivLinear 4).apply_symm_apply]
    exact ha
  have hmove : ⁅Source.UH F.H F.Vplus,Source.QH F.H⁆ ≠ ⊥ := by
    intro he
    exact hseedQ (bot_unique ((commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans_eq he))
  have hZ : F.V₁ ≤ centralizer (F.H:Set G) := le_centralizer_iff.mp hF.H_centralizes
  have hfixed := d.centralizer_eq_kernel_of_transitive (Source.QH F.H)
    (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D:=F))
    (hZ.trans (centralizer_le (pCoreIn_le 2 F.H))) hmove htrans
  have hCQ : Source.HC F.H F.Vplus ≤ Source.QH F.H :=
    d.centralizer_le_of_action_kernel (Source.QH F.H)
      (source_natural_action_kernel F.H (Source.QH F.H) ρ π hker hnatural)
  have hCeq : Source.QH F.H ⊓ centralizer (Source.UH F.H F.Vplus:Set G) =
      Source.HC F.H F.Vplus :=
    le_antisymm (inf_le_inf_right _ (pCoreIn_le 2 F.H)) (le_inf hCQ inf_le_right)
  obtain ⟨ddual,hpair⟩ := d.exists_marked_central_duality (Source.QH F.H)
    (pCoreIn_le 2 F.H) (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D:=F))
    (d.kernel_le.trans hF.UH_le_QH) hZ
    (by rw [commutator_comm]; exact hF.commutator_UH_QH_le_point) hF.point_card hfixed
  exact ⟨{ ddual with
    kernel_le := hCeq ▸ ddual.kernel_le
    kernel_eq := by rw [ddual.kernel_eq,hCeq] },hpair⟩

/-- Restriction of the constructed perfect pairing to the original seed
proves the literal centralizer index used at the end of 13.8.28. -/
theorem source_seed_centralizer_index_four
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    [IsElementaryAbelian 2 (Source.UH F.H F.Vplus)]
    (ρ : Representation (ZMod 2) F.H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection F.H (Source.UH F.H F.Vplus) F.V₁ ρ)
    (π : F.H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH F.H).subgroupOf F.H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hseedQ : ⁅F.Vplus,Source.QH F.H⁆ ≠ ⊥) (hseedcard : Nat.card F.Vplus = 8) :
    (Source.QH F.H ⊓ centralizer (F.Vplus:Set G)).relIndex (Source.QH F.H) = 4 := by
  obtain ⟨ddual,hpair⟩ := source_natural_core_duality F hF ρ d π hker honto hnatural hseedQ
  have hi := d.centralizer_index_of_dual_pairing ddual hpair F.Vplus (le_conjugateSpanBy _ _)
  rw [d.imageSpace_card_eq_relIndex F.Vplus (le_conjugateSpanBy _ _)] at hi
  have hc := (F.V₁.subgroupOf F.Vplus).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hF.point_lt.le).toEquiv,hF.point_card,hseedcard] at hc
  change 2 * F.V₁.relIndex F.Vplus = 8 at hc
  rw [inf_comm,inf_relIndex_right]
  omega
end CFSG.Quasithin.Chapter13.Section08.LinearFour

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open CriticalGeometry NoncentralChiefRefinement BinaryLinear.OuterCyclic
open Atlas.Order20160A8.Bivectors (exteriorMap)
variable {G : Type*} [Group G] [Finite G]
/-- The literal endgame application derives the dual centralizer index from
the original noncentral seed and natural quotient, with all critical maps retained. -/
theorem source_linear_four_exclusion_of_natural_duality
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    (c : CriticalPair F.L (F.T:Subgroup G) F.H F.V) (hb : 3 ≤ c.path.length)
    (Q R K : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH F.H F.V)]
    (ρ : Representation (ZMod 2) F.H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection F.H (Source.UH F.H F.Vplus) F.V₁ ρ)
    (π : F.H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH F.H).subgroupOf F.H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (ξ : Representation (ZMod 2) F.H (Fin 6 → ZMod 2))
    (dx : BinaryConjugationSection F.H (Source.VH F.H F.V) (Source.UH F.H F.Vplus) ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hH : F.H = normalizer (F.V₁:Set G))
    (hseed : ⁅centralizer (F.Vplus:Set G),F.V⁆ ≤ F.V₁)
    (hseedcard : Nat.card F.Vplus = 8)
    (hseedQ : ⁅F.Vplus,Source.QH F.H⁆ ≠ ⊥)
    (hcontrol : F.H ⊓ normalizer (F.Vplus:Set G) ≤ F.LT)
    (houtside : ¬ c.Ugamma F.Vplus ≤ Source.QH F.H)
    (hline : ¬ c.Aone F.V₁ ≤ Source.UH F.H F.Vplus) (hbackline : ¬ F.V₁ ≤ c.Ugamma F.Vplus)
    (hQR : Source.QH F.H ≤ R) (hindex : Q.relIndex R = 4)
    (hcent : Q ⊓ Source.QH F.H ≤ centralizer (F.Vplus:Set G))
    (hQV : Q ≤ centralizer (F.V:Set G))
    (hcover : IsSQTK KnownSimple.IsKnownSimple F.H)
    (e : (F.H ⧸ pCore 2 F.H) ≃* LinearGroup 4)
    (hKH : K ≤ F.H) (hK : IsPPerfect 2 K)
    (hmove : ¬ ⁅Source.HC F.H F.Vplus,K⁆ ≤ Source.VH F.H F.V)
    (hKonto : Function.Surjective
      ((QuotientGroup.mk' (pCore 2 F.H)).comp (K.subgroupOf F.H).subtype))
    (hnotfour : ∀ s : ChiefSeries F.H,
      s.head.val.map F.H.subtype = Source.VH F.H F.V → s.last.val.map F.H.subtype = Source.HC F.H F.Vplus →
      (∀ i : Fin s.length, ∀ D : Subgroup (Section (s i.castSucc) (s i.succ)),
        (∀ k : K.subgroupOf F.H, ∀ x, x ∈ D →
          sectionAction (s i.castSucc) (s i.succ) k x ∈ D) → D = ⊥ ∨ D = ⊤) →
      s.restrictedNoncentralCount (K.subgroupOf F.H) = 1 → ∀ i : Fin s.length,
        (¬ ∀ k : K.subgroupOf F.H, ∀ x,
          sectionAction (s i.castSucc) (s i.succ) k x = x) →
          Nat.card (Section (s i.castSucc) (s i.succ)) ≠ 16) : False := by
  let : IsElementaryAbelian 2 (Source.UH F.H F.Vplus) := IsElementaryAbelian.of_le dx.kernel_le
  have hdual := source_seed_centralizer_index_four F hF ρ d π hker honto hnatural hseedQ hseedcard
  exact source_linear_four_exclusion_of_seed_normalizer F hF c hb Q R K
    ρ d π hker honto hnatural ξ dx hexterior hH hseed hseedcard hcontrol
    houtside hline hbackline hQR hindex hcent hdual hQV hcover e hKH hK hmove hKonto hnotfour

end CFSG.Quasithin.Chapter13.Section08.LinearFour

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryParabolicExteriorSquare.PlaneSpan
open NoncentralChiefRefinement Atlas.Order20160A8.Bivectors
variable {G : Type*} [Group G] [Finite G]

/-- The original natural and exterior markings determine the three lower
cubic lengths, including the dual section constructed from commutators. -/
theorem source_complement_cubic_lengths_of_natural_duality
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    [IsElementaryAbelian 2 (Source.VH F.H F.V)]
    (ρ : Representation (ZMod 2) F.H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection F.H (Source.UH F.H F.Vplus) F.V₁ ρ)
    (π : F.H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH F.H).subgroupOf F.H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hseedQ : ⁅F.Vplus,Source.QH F.H⁆ ≠ ⊥)
    (ξ : Representation (ZMod 2) F.H Six)
    (dx : BinaryConjugationSection F.H (Source.VH F.H F.V) (Source.UH F.H F.Vplus) ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (A : Subgroup G) (hAH : A ≤ F.H) (hA : Nat.card A = 3)
    (a : A) (ha : ∀ b, b ∈ zpowers a)
    (hmat : (π (inclusion hAH a)).val = complementCubic) :
    sectionCubicLength A F.V₁ (Source.UH F.H F.Vplus) = 1 ∧
      sectionCubicLength A (Source.UH F.H F.Vplus) (Source.VH F.H F.V) = 2 ∧
      sectionCubicLength A (Source.HC F.H F.Vplus) (Source.QH F.H) = 1 := by
  let : IsElementaryAbelian 2 (Source.UH F.H F.Vplus) := IsElementaryAbelian.of_le dx.kernel_le
  obtain ⟨ddual,_⟩ := source_natural_core_duality F hF ρ d π hker honto hnatural hseedQ
  have hVC : Source.VH F.H F.V ≤ Source.HC F.H F.Vplus := le_inf dx.section_le
    ((commutator_eq_bot_iff_le_centralizer.mp (commutator_self_eq_bot_iff.mpr
      (inferInstance : IsMulCommutative (Source.VH F.H F.V)))).trans (centralizer_le dx.kernel_le))
  exact source_complement_cubic_lengths F.H (Source.UH F.H F.Vplus) F.V₁
    (Source.VH F.H F.V) (Source.HC F.H F.Vplus) (Source.QH F.H) A hAH hA
    (isPGroup_pCoreIn 2 F.H) hVC ρ d ddual ξ dx a ha
    (fun w => (hnatural _ w).trans (by rw [hmat]))
    (fun w => (hexterior _ w).trans (by rw [hmat]))
end CFSG.Quasithin.Chapter13.Section08.LinearFour

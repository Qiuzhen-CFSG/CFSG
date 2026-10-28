module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.ModelGeometry.Assembly
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Nonsplit
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.SquareReduction

/-!
# Assembly of the HS normalizer cover and its nonsplit binary module

The concrete degree-100 HS normalizer supplies every model premise of the
abelian-section and nonsplitting arguments. Its core is C₄³ with the specified
SL₃(2) action. Lifting the center and residual incidences gives Q ≤ X ≤ C_K(V)
and Q = ⟨Vᴹ⟩, hence Q is abelian. The actual Sylow-seven decomposition produces
Φ(Q) ≃ C₂³ and the natural quotient of the four-dimensional Frattini module.

Odd-index transfer makes M perfect. The lifted two-central involution outside
Q rules out a splitting of the central line by the SL₂(7) central-cover
obstruction. The genuine B.4.8(2) then gives fixed-displacement equality for
this faithful indecomposable action. We discharge the literal fixed-subgroup
premise in M/E and apply coset fusion. The core involution marking supplies
the complementary branch inside Q.

Only the earlier cover-centralizer facts and the universal B.4.8(2) are
explicit inputs. Their producers are CentralizerRestriction.Assembly
(normalizerCentralizerInput) and qt-b-04-natural-extensions, respectively;
qt-i22-hs-local-cover discharges them in the full I.2.2(5) assembly.
No normalizer-specific incidence, module or fusion premise remains.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, printed p.412 / PDF p.423,
and B.4.8(2), printed p.91 / PDF p.102.
-/

public section

open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.ThreeCovers.CentralExtension
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule
open Sporadic.LeechRelated.HS.BlockNormalizer
open Sporadic.LeechRelated.HS.EvenLocalCandidates
open Theory.GroupTheory.DoubleCoverCentralizer

universe u
variable {K : Type u} [Group K] [Finite K]

/-- The source incidences and abelianness, with every model premise discharged. -/
theorem core_incidence
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (c : AbelianSection.CentralizerInput e u) :
    coreCenter u ≤ M e ∧
      (Q e).map (M e).subtype ≤ centralizerTwoResidual u ∧
      centralizerTwoResidual u ≤ centralizer (coreCenter u : Set K) ∧
      normalClosure ((coreCenter u).subgroupOf (M e) : Set (M e)) = Q e ∧
      IsMulCommutative (Q e) := by
  obtain ⟨hVM, hQX, hgen, hab⟩ :=
    AbelianSection.core_incidence_and_abelian e hZ u c ModelGeometry.abelianSectionModelInput
  exact ⟨hVM, hQX, c.centralizes, hgen, hab⟩

/-- The source internal direct product and Frattini section, on the original
relative subgroups and covering map. -/
theorem coprime_frattini_section
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (c : AbelianSection.CentralizerInput e u) :
    ∃ Y : Sylow 7 (M e),
      Q e = ⁅Q e, (Y : Subgroup (M e))⁆ ⊔ centralFactor e ∧
      Disjoint ⁅Q e, (Y : Subgroup (M e))⁆ (centralFactor e) ∧
      Nonempty (Q e ≃* (↥⁅Q e, (Y : Subgroup (M e))⁆ × ↥(centralFactor e))) ∧
      Nonempty (↥⁅Q e, (Y : Subgroup (M e))⁆ ≃* Multiplicative (Fin 3 → ZMod 4)) ∧
      E e ≤ ⁅Q e, (Y : Subgroup (M e))⁆ ∧
      Nonempty (E e ≃* Multiplicative (Fin 3 → ZMod 2)) ∧
      Nat.card (E e) = 8 ∧
      E e ≤ (centralizerCore u).subgroupOf (M e) ∧
      Disjoint (E e) (centralFactor e) ∧
      ((E e).map (localMap e)).map baseNormalizer.subtype = baseElementary := by
  obtain ⟨Y, _, hsplit, hd, hprod, hcoords, hED, hEiso, hE, hER, hEZ, himage, _, _⟩ :=
    AbelianSection.exists_coprime_frattini_section e hZ u c ModelGeometry.abelianSectionModelInput
  exact ⟨Y, hsplit, hd, hprod, hcoords, hED, hEiso, hE, hER, hEZ, himage⟩

/-- The faithful four-dimensional module has the actual central image as its
fixed line and a natural three-dimensional quotient, including actor coordinates. -/
theorem natural_frattini_section
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (c : AbelianSection.CentralizerInput e u) :
    centralLine e hZ = (frattiniRepresentation e).invariants ∧
      Module.finrank (ZMod 2) (centralLine e hZ) = 1 ∧
      Module.finrank (ZMod 2) (Additive (Qbar e)) = 4 ∧
      Function.Injective (frattiniRepresentation e) ∧
      Nonempty (ActionEquiv (reducedAction (frattiniRepresentation e))
        (linearNatural BinaryField.two 3)) := by
  obtain ⟨hc, hline, hdim, hfaithful, _⟩ :=
    AbelianSection.natural_frattini_section e hZ u c ModelGeometry.abelianSectionModelInput
  exact ⟨hc, hline, hdim, hfaithful,
    ⟨AbelianSection.naturalFrattiniActionEquiv e hZ u c ModelGeometry.abelianSectionModelInput⟩⟩

/-- The branch inside Q uses the involutions in the actual model C₄³.
No assertion about lifting non-two-central involutions is assumed. -/
theorem core_involution_image_twoCentral
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (x : M e) (hxQ : x ∈ Q e)
    (hximage : orderOf (modelMap e (x : K)) = 2) :
    TwoCentral (modelMap e (x : K)) := by
  have hx : localMap e x ∈ pCore 2 baseNormalizer := by
    rwa [Q_eq_model_core_preimage e hZ] at hxQ
  exact ModelGeometry.A_involutions_twoCentral _
    (mem_map_of_mem baseNormalizer.subtype hx) hximage

/-- All normalizer-specific hypotheses of the nonsplitting argument and
B.4.8(2) are discharged. The displayed fixed-subgroup premise is literally
that of coset_fusion_mod_frattini in the actual quotient M/E. -/
theorem nonsplit_and_fusion [Group.IsPerfect K]
    (h48 : EarlierB48Two.{u,u})
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K) (hu : modelMap e u = e0)
    (c : AbelianSection.CentralizerInput e u) :
    Group.IsPerfect (M e) ∧
    (∀ W : Subrepresentation (frattiniRepresentation e),
      ¬ IsCompl (centralLine e hZ) W.toSubmodule) ∧
    IsIndecomposable (frattiniRepresentation e) ∧
    E e ≤ (centralizerCore u).subgroupOf (M e) ∧
    ∃ j : M e, (j : K) ∈ centralizerCore u ∧ orderOf j = 2 ∧
      localMap e j = ModelGeometry.j₀Normalizer ∧
      orderOf (QuotientGroup.mk' (Q e) j) = 2 ∧
      orderOf (QuotientGroup.mk' (E e) j) = 2 ∧
      (∀ a : M e ⧸ Q e, orderOf a = 2 → ∃ m : M e,
        QuotientGroup.mk' (Q e) m * a * (QuotientGroup.mk' (Q e) m)⁻¹ =
          QuotientGroup.mk' (Q e) j) ∧
      (∀ v : Additive (Qbar e),
        frattiniRepresentation e (QuotientGroup.mk' (Q e) j) v = v →
        ∃ w : Additive (Qbar e),
          frattiniRepresentation e (QuotientGroup.mk' (Q e) j) w - w = v) ∧
      (Qbar e ⊓ centralizer ({QuotientGroup.mk' (E e) j} : Set _) ≤
        ⁅Qbar e, zpowers (QuotientGroup.mk' (E e) j)⁆) ∧
      (∀ x : M e, x ^ 2 = 1 →
        QuotientGroup.mk' (Q e) x = QuotientGroup.mk' (Q e) j →
        ∃ q : Q e, QuotientGroup.mk' (E e) ((q : M e) * j * (q : M e)⁻¹) =
          QuotientGroup.mk' (E e) x) ∧
      (∀ x : M e, x ^ 2 = 1 → x ∉ Q e →
        ∃ y ∈ centralizerCore u, IsConj (x : K) y) := by
  obtain ⟨Y, hZE, hgen, hE, hER, ⟨hnatural⟩⟩ :=
    AbelianSection.nonsplit_inputs e hZ u c ModelGeometry.abelianSectionModelInput
  have hXmap : (centralizerTwoResidual u).map (modelMap e) =
      centralizerTwoResidual (modelMap e u) := by
    rw [hu]
    exact c.residual_image
  have hjR : (ModelGeometry.j₀Normalizer : Sporadic.LeechRelated.HS.Carrier) ∈
      centralizerCore (modelMap e u) := by
    rw [hu]
    exact ModelGeometry.j₀_mem_R₀
  obtain ⟨hperfect, hcentral, hn, hi, j, hjR, hj2, hjlocal, hjQ, hjE, hconj, hf, hcore⟩ :=
    Nonsplit.nonsplit_and_fusion h48 e hZ ModelGeometry.normalizer_perfect
      ModelGeometry.normalizer_index_not_even u hXmap ModelGeometry.j₀Normalizer
      ModelGeometry.j₀Normalizer_order ModelGeometry.j₀_twoCentral hjR
      ModelGeometry.j₀Normalizer_not_mem_core hZE Y hgen hE hER hnatural
  have hline : centralLine e hZ = Nonsplit.centralLine e :=
    (natural_frattini_section e hZ u c).1.trans hcentral.symm
  have hfixed := fixed_le_commutator_of_frattini_displacement e j hf
  refine ⟨hperfect, ?_, hi, hER, j, hjR, hj2, hjlocal, hjQ, hjE, hconj, hf,
    hfixed, ?_, hcore⟩
  · simpa only [hline] using hn
  · exact fun x hx hcoset => coset_fusion_mod_frattini e j hjE hfixed x hx hcoset

/-- Actual consumer of both normalizer branches: an involution in M with
nontrivial image has a two-central image in the literal HS carrier. -/
theorem involution_image_twoCentral [Group.IsPerfect K]
    (h48 : EarlierB48Two.{u,u})
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K) (hu : modelMap e u = e0)
    (c : AbelianSection.CentralizerInput e u)
    (x : M e) (hx : x ^ 2 = 1)
    (hximage : orderOf (modelMap e (x : K)) = 2) :
    TwoCentral (modelMap e (x : K)) := by
  by_cases hxQ : x ∈ Q e
  · exact core_involution_image_twoCentral e hZ x hxQ hximage
  obtain ⟨_, _, _, _, j, _, _, _, _, _, _, _, _, _, hcore⟩ :=
    nonsplit_and_fusion h48 e hZ u hu c
  obtain ⟨y, hy, hxy⟩ := hcore x hx hxQ
  obtain ⟨g, hg⟩ := isConj_iff.mp ((modelMap e).map_isConj hxy)
  have horder : orderOf (modelMap e y) = 2 := by
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq _).trans hximage
  have hcentral := core_image_twoCentral e hZ u
    (by rw [hu]; exact CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.central_involution_order) (by rw [hu]; exact e0_twoCentral) y hy horder
  have heq : (MulAut.conj g⁻¹) (modelMap e y) = modelMap e (x : K) := by
    rw [← hg]
    simp [mul_assoc]
  exact heq ▸ hcentral.map (MulAut.conj g⁻¹)

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule

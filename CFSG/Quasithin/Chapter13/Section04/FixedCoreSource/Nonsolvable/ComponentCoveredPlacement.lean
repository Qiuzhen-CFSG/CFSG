module
public import Theory.GroupTheory.PResidual.CubicComponentPlacement
public import Theory.SpecificGroups.PSL3Two.Automorphisms.SylowStabilizer
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearShort

/-!
# Placement and exclusion of the original covered cubic in the linear row

The literal L₀ is two-perfect with cubic two-core quotient. It is normalized
by T and normalizes the selected component K inside C_G(z). If L₀ does not
lie in K, the cubic-placement theorem makes K normalize L₀. The original
maximal-local uniqueness bounds N_G(L₀) by N_G(L), contrary to K escaping
that normalizer. Thus L₀≤K. The checked upper and lower cubic lengths on
its same intrinsic O₂(L₀) now exclude the covered original row altogether.

This discharges the placement step in 13.4.10(2) without using a natural
four-dimensional setup or assuming an identification of cubic directions.
The five-dimensional CoreMarking and original quotient maps are retained.
Earlier source inputs and LargeDistanceInput remain explicit; the latter
is produced by qt-e-ms-small-a6-exhaustion-large-distance. The remaining
centralizer, comparison, commutator and graph assembly belongs to the
nonsolvable owner, and nonsolvability at both escaping weights is still
required for final assembly.
Source: Aschbacher--Smith 13.4.10(2--3), printed pp.908--909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

private theorem linear_three_sylow_stabilizer_two
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (S : Sylow 2 (K ⧸ pCore 2 K)) :
    IsPGroup 2 (MulAction.stabilizer (MulAut (K ⧸ pCore 2 K))
      (S : Subgroup (K ⧸ pCore 2 K))) := by
  let U := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let φ := MulAut.congr e
  let A := MulAction.stabilizer (MulAut (K ⧸ pCore 2 K)) (S : Subgroup (K ⧸ pCore 2 K))
  let ψ : A →* MulAction.stabilizer (MulAut BinaryLinearThree.Group)
      (U : Subgroup BinaryLinearThree.Group) :=
    (φ.toMonoidHom.comp A.subtype).codRestrict _ (fun a => by
      change ((S : Subgroup (K ⧸ pCore 2 K)).map e.toMonoidHom).map (φ a).toMonoidHom =
        (S : Subgroup (K ⧸ pCore 2 K)).map e.toMonoidHom
      rw [Subgroup.map_map]
      have he : (φ a).toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.val.toMonoidHom := by
        apply MonoidHom.ext
        intro x
        change e (a.val (e.symm (e x))) = e (a.val x)
        rw [e.symm_apply_apply]
      rw [he,←Subgroup.map_map]
      exact congrArg (Subgroup.map e.toMonoidHom) a.property)
  exact (Matrix.PSL3Two.automorphism_sylow_stabilizer_two U).of_injective ψ (by
    intro a b he
    exact Subtype.ext (φ.injective (congrArg Subtype.val he)))

/-- The actual original L₀ lies in K; its cubic quotient and source normalizer
bound discharge the centralizing alternative of the Sylow-action argument. -/
theorem covered_zero_le_linear_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    zero L ≤ K := by
  have hTA := D.sylow_normalizes_component.trans (normalizer_le_zero_normalizer L)
  have hTK := (Solvable.original_sylow_le_centralizer hzT).trans hHN
  have hAK : zero L ≤ normalizer (K : Set G) :=
    (Solvable.covered_zero_centralizes_core D m).trans
      ((centralizer_le (Set.singleton_subset_iff.mpr z.property)).trans hHN)
  have hcard := Solvable.covered_zero_core_card hc
  have hne : zero L ≠ ⊥ := by
    intro he
    rw [he] at hcard
    have hbot : Nat.card ((⊥ : Subgroup G) ⧸ pCore 2 (⊥ : Subgroup G)) = 1 := Nat.card_unique
    omega
  have hNM : normalizer (zero L : Set G) ≤ normalizer (L : Set G) :=
    h.normal_subgroup_normalizer_le D.sylow_normalizes_component
      ((zero_le L).trans le_sup_left) hne
      ((sup_le L.le_normalizer D.sylow_normalizes_component).trans (normalizer_le_zero_normalizer L))
  exact (cubic_residual_le_or_normalized T (zero L) K hTA hTK hAK
    (residual_isPPerfect _) hcard (linear_three_sylow_stabilizer_two eK)).resolve_right
      (fun hn => hKM (hn.trans hNM))

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- The source placement makes the conflicting cubic bounds apply to the same
original O₂(L₀), excluding the covered-original linear-three row. -/
theorem covered_linear_component_false
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) : False :=
  covered_zero_not_le_linear_component hl h₀ h structural modules D m h1332 fixed
    hindex hc z hzT hzL hKz hHN hKM hfK eK
    (covered_zero_le_linear_component h D m hc z hzT hHN hKM eK)

/-- The selected linear-three row forces the original quotient to be ordinary A₆. -/
theorem ordinary_original_of_linear_component
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  let := h.quasisimple
  have hn : ¬ 2 ∣ Nat.card (center (L ⧸ pCore 2 L)) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center (L ⧸ pCore 2 L)) le_rfl
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) :=
    Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
    (augmentationCentralQuotient D m) ho with hc | ⟨_,hc⟩
  · exact ⟨GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6
      (augmentationCentralQuotient D m) hc⟩
  · exact (covered_linear_component_false hl h₀ h structural modules D m h1332 fixed
      hindex hc z hzT hzL hKz hHN hKM hfK eK).elim

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.Basic
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ParabolicCore.Replacement
public import Theory.GroupTheory.CharacteristicCoreCenter
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.ParabolicActions.RootTransfer
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual
public import Theory.SpecificGroups.SymplecticFour.RootCoreTori
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models

/-!
# A central Levi complement gives the symplectic local core bound

Put P = L ∩ M and C = C_L(V). Choose a complement Y to C in P whose
image in P/O₂(P) is central. The preimage of the quotient center is
characteristic in P. Every odd actor with action commuting with Y
normalizes P, so its commutator with Y lies in that preimage and in C.
Their intersection is O₂(P) in the symplectic model.

The replacement lemma transfers all regular cyclic section clauses from
X to Y through their equal action images. The final reduction transports
the intrinsic complement and intersection calculation through the actual
Sp₄ isomorphism, with the original matrix root and relative two-core.
No automorphism classification or two-group assumption on C is used.

The final theorem discharges the intrinsic calculation with
`RootCoreTori.exists_core_central_complement`. Its scalar Levi torus
uses equal diagonal parameters in the short-root case. This completes
the symplectic local calculation from the stated earlier E.6.11 outputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11(3c),
printed pp.249–250 (PDF pp.260–261), and the factor-count paragraph of
E.6.25, printed p.255 (PDF p.266).
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.ChapterE.Section06.Components
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
variable {G : Type*} [Group G]

private theorem image_of_centralizer_complement {V B C Y : Subgroup G}
    (hBN : B ≤ normalizer (V : Set G)) (hCV : C ≤ centralizer (V : Set G))
    (hcomp : C ⊔ Y = B) : inducedAutomizer V Y = inducedAutomizer V B := by
  have hCN : C ≤ normalizer (V : Set G) :=
    hCV.trans (centralizer_le_normalizer _)
  have hYN : Y ≤ normalizer (V : Set G) := (hcomp ▸ le_sup_right).trans hBN
  have hz : (C.subgroupOf (normalizer (V : Set G))).map
      V.normalizerMonoidHom.rangeRestrict = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, MonoidHom.ker_rangeRestrict,
      normalizerMonoidHom_ker]
    exact comap_mono hCV
  unfold inducedAutomizer
  rw [← hcomp, subgroupOf_sup hCN hYN, Subgroup.map_sup, hz, bot_sup_eq]

variable {H : Type*} [Group H] {L U V R : Subgroup G}

private theorem map_back (e : L ≃* H) {B : Subgroup G} (hBL : B ≤ L) :
    ((B.subgroupOf L).map e.toMonoidHom).map (L.subtype.comp e.symm.toMonoidHom) = B := by
  rw [map_map]
  have hf : (L.subtype.comp e.symm.toMonoidHom).comp e.toMonoidHom = L.subtype := by
    ext x
    simp
  rw [hf, map_subgroupOf_eq_of_le hBL]

private theorem centralizer_model (e : L ≃* H) (S : Subgroup H)
    (hRL : R ≤ L) (hspan : U ⊔ R = V) (hLC : L ≤ centralizer (U : Set G))
    (hR : (R.subgroupOf L).map e.toMonoidHom = S) :
    ((L ⊓ centralizer (V : Set G)).subgroupOf L).map e.toMonoidHom =
      centralizer (S : Set H) := by
  have hRV : R ≤ V := hspan ▸ le_sup_right
  have hc (l : L) : (l : G) ∈ centralizer (V : Set G) ↔
      e l ∈ centralizer (S : Set H) := by
    constructor
    · intro hl
      apply mem_centralizer_iff.mpr
      intro s hs
      rw [← hR] at hs
      obtain ⟨r, hr, rfl⟩ := hs
      have he : r * l = l * r := Subtype.ext
        (mem_centralizer_iff.mp hl r (hRV hr))
      change e r * e l = e l * e r
      simpa only [map_mul] using congrArg e he
    · intro hl
      have hn : V ≤ centralizer ({(l : G)} : Set G) := by
        rw [← hspan]
        refine sup_le ?_ ?_
        · intro u hu
          exact mem_centralizer_singleton_iff.mpr
            (mem_centralizer_iff.mp (hLC l.property) u hu)
        · intro r hr
          have hs : e ⟨r, hRL hr⟩ ∈ S := hR ▸ mem_map_of_mem e.toMonoidHom hr
          have he := mem_centralizer_iff.mp hl _ hs
          have hh : (⟨r, hRL hr⟩ : L) * l = l * ⟨r, hRL hr⟩ :=
            e.injective (by simpa only [map_mul] using he)
          exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hh)
      exact mem_centralizer_iff.mpr fun v hv => mem_centralizer_singleton_iff.mp (hn hv)
  apply le_antisymm
  · rintro _ ⟨l, hl, rfl⟩
    exact (hc l).mp hl.2
  · intro s hs
    exact ⟨e.symm s, ⟨(e.symm s).property, (hc (e.symm s)).mpr (by simpa)⟩,
      e.apply_symm_apply s⟩

variable [Finite G] {K : GroupClass} {T : Sylow 2 G}
variable {M X Y : Subgroup G} [IsElementaryAbelian 2 V]

/-- A complement central modulo the local core supplies every odd-actor
bound, once its intersection with the action kernel is separated. -/
theorem parabolic_core_control_of_complement
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hTX : TorusAction M V L X (subgroupCorank V U))
    (hcomp : (L ⊓ centralizer (V : Set G)) ⊔ Y = L ⊓ M)
    (hdis : (L ⊓ centralizer (V : Set G)) ⊓ Y = ⊥)
    (hcentral : Y ≤ (L ⊓ M).coreCenterIn 2)
    (hsep : (L ⊓ M).coreCenterIn 2 ⊓ (L ⊓ centralizer (V : Set G)) ≤
      (L ⊓ M).pCoreIn 2) :
    Y ≤ L ∧ RegularCyclicSection M V U Y ∧
      inducedAutomizer V Y = inducedAutomizer V X ∧
      ∀ A : Subgroup G, A ≤ normalizer (V : Set G) → Odd (Nat.card A) →
        (∀ a ∈ inducedAutomizer V A, ∀ y ∈ inducedAutomizer V Y, Commute a y) →
        ⁅A, Y⁆ ≤ (L ⊓ M).pCoreIn 2 := by
  have hYP : Y ≤ L ⊓ M := hcomp ▸ le_sup_right
  have hYL := hYP.trans inf_le_left
  have hPN : L ⊓ M ≤ normalizer (V : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans hL.1)).trans
      (h.localCentralizer_le_normalizer hU.2.1 hU.1)
  have hi : inducedAutomizer V Y = inducedAutomizer V X :=
    (image_of_centralizer_complement hPN inf_le_right hcomp).trans
      (image_of_centralizer_complement hPN inf_le_right hTX.complement).symm
  have hYcontained : Y ≤ localNormalizer M V ⊓ centralizer (U : Set G) :=
    le_inf (le_inf (hYP.trans inf_le_right) (hYP.trans hPN)) (hYL.trans hL.1)
  have hYfaith : Y ⊓ centralizer (V : Set G) = ⊥ := by
    apply bot_unique
    intro y hy
    exact hdis ▸ (show y ∈ (L ⊓ centralizer (V : Set G)) ⊓ Y from
      ⟨⟨hYL hy.1, hy.2⟩, hy.1⟩)
  have hY := regularCyclicSection_of_same_image hX hYcontained hYfaith hi
  refine ⟨hYL, hY, hi, ?_⟩
  intro A hA ho hc
  apply commutator_le_core_of_coreCenterIn
    (odd_normalizes_local_intersection h earlier hU hY hL hA ho hc) hcentral
    (cross_commutator_le_kernel hA (hYP.trans hPN) hc)
  intro x hx
  exact hsep ⟨hx.1, ⟨((coreCenterIn_le 2 (L ⊓ M)) hx.1).1, hx.2⟩⟩

open Theory.SpecificGroups.SymplecticFour

/-- The complete ambient selection and odd-actor bound reduce to two
intrinsic facts: a central Levi complement and its separation from the
root centralizer. The intrinsic matrix calculation remains explicit. -/
theorem exists_parabolic_core_control_of_root_calculation
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hn : 1 < subgroupCorank V U)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hVN : V ≤ normalizer (L : Set G))
    (hTX : TorusAction M V L X (subgroupCorank V U))
    (hP : MaximalParabolic L (L ⊓ M))
    (hroot : SymplecticRoot L ⁅V, X⁆ (subgroupCorank V U))
    (model : ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
      (n : ℕ), Nat.card F = 2 ^ n → 1 < n → ∀ r : Fin 8,
      let R := RootSubgroup.group (F := F) r
      let N := normalizer (R : Set (Sp F))
      let C := centralizer (R : Set (Sp F))
      ∃ Z : Subgroup (Sp F), C ⊔ Z = N ∧ C ⊓ Z = ⊥ ∧
        Z ≤ N.coreCenterIn 2 ∧ N.coreCenterIn 2 ⊓ C ≤ N.pCoreIn 2) :
    ∃ Y : Subgroup G, Y ≤ L ∧ RegularCyclicSection M V U Y ∧
      inducedAutomizer V Y = inducedAutomizer V X ∧
      ∀ A : Subgroup G, A ≤ normalizer (V : Set G) → Odd (Nat.card A) →
        (∀ a ∈ inducedAutomizer V A, ∀ y ∈ inducedAutomizer V Y, Commute a y) →
        ⁅A, Y⁆ ≤ (L ⊓ M).pCoreIn 2 := by
  obtain ⟨hRL, F, hfield, hfinite, hcard, e, r, hR⟩ := hroot
  let := hfield
  let := hfinite
  let := EvenProjective.charTwo_of_card hcard
  let R := RootSubgroup.group (F := F) r
  let N := normalizer (R : Set (Sp F))
  let C := centralizer (R : Set (Sp F))
  change ((⁅V, X⁆ : Subgroup G).subgroupOf L).map e.toMonoidHom = R at hR
  have hPN : ((L ⊓ M).subgroupOf L).map e.toMonoidHom = N :=
    Components.ParabolicActions.parabolic_map_eq_root_normalizer e R hVN hP
      (by rw [← hTX.displacement]; exact hR) (RootNormalizerResidual.normalizer_ne_top r)
  have hCC : ((L ⊓ centralizer (V : Set G)).subgroupOf L).map e.toMonoidHom = C :=
    centralizer_model e R hRL hX.spanning hL.1 hR
  let f : Sp F →* G := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hNP : N.map f = L ⊓ M := by
    rw [← hPN]
    exact map_back e inf_le_left
  have hCG : C.map f = L ⊓ centralizer (V : Set G) := by
    rw [← hCC]
    exact map_back e inf_le_left
  obtain ⟨Z, hcomp, hdis, hcentral, hsep⟩ := model F _ hcard hn r
  refine ⟨Z.map f, parabolic_core_control_of_complement h earlier hU hX hL hTX
    ?_ ?_ ?_ ?_⟩
  · have he := congrArg (Subgroup.map f) hcomp
    rwa [Subgroup.map_sup, hCG, hNP] at he
  · have he := congrArg (Subgroup.map f) hdis
    rwa [Subgroup.map_inf _ _ _ hf, hCG, Subgroup.map_bot] at he
  · have he := map_mono (f := f) hcentral
    rwa [map_coreCenterIn_of_injective 2 N f hf, hNP] at he
  · have he := map_mono (f := f) hsep
    rwa [Subgroup.map_inf _ _ _ hf, map_coreCenterIn_of_injective 2 N f hf,
      map_pCoreIn_of_injective 2 N f hf, hCG, hNP] at he

omit [IsElementaryAbelian 2 V] in
/-- Choose a compatible symplectic torus with the same faithful regular
action image and control its commutators with every odd commuting actor.
The intrinsic matrix calculation is discharged for all eight roots; only
the stated earlier component and torus conclusions remain as inputs. -/
theorem exists_parabolic_core_control
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hn : 1 < subgroupCorank V U)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hVN : V ≤ normalizer (L : Set G))
    (hTX : TorusAction M V L X (subgroupCorank V U))
    (hP : MaximalParabolic L (L ⊓ M))
    (hroot : SymplecticRoot L ⁅V, X⁆ (subgroupCorank V U)) :
    ∃ Y : Subgroup G, Y ≤ L ∧ RegularCyclicSection M V U Y ∧
      inducedAutomizer V Y = inducedAutomizer V X ∧
      ∀ A : Subgroup G, A ≤ normalizer (V : Set G) → Odd (Nat.card A) →
        (∀ a ∈ inducedAutomizer V A, ∀ y ∈ inducedAutomizer V Y, Commute a y) →
        ⁅A, Y⁆ ≤ (L ⊓ M).pCoreIn 2 := by
  let _ := h.elementary
  apply exists_parabolic_core_control_of_root_calculation
    h earlier hU hX hn hL hVN hTX hP hroot
  intro F _ _ _ n hcard hn r
  exact RootCoreTori.exists_core_central_complement hcard hn r

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts

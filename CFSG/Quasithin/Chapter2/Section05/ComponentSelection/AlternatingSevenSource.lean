module
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.InvariantLocalSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.AlternatingSeven
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.Local
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry
public import Theory.SpecificGroups.AlternatingSeven.OddSylowLocal

/-! The A7 and triple-A7 cases in the original empty-Γ-even branch.
A Sylow-stable S4 in the component lifts through its odd center. The component
orbit argument forces this actual local subgroup into M, but its quotient
does not centralize the marked triple transposition, contradicting the proved
intersection identification of 2.3.9(7)(c).
Source: Aschbacher--Smith 2.5.2, printed p.551. -/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open ComponentRefinement
variable {G : Type*} [Group G] [Finite G] {M H L : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original A7 and triple-A7 intersection cannot occur when Gamma-even-zero
is empty. All local subgroup geometry and odd-cover splitting are proved. -/
theorem alternating_seven_intersection_false
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (h : LocalSetup H L M S z)
    (e : (L ⧸ center L) ≃* AlternatingSeven.A7)
    (ho : Odd (Nat.card (center L)))
    (hI : (M.subgroupOf L).map (AlternatingSeven.quotientMap e) =
      AlternatingSeven.alternatingStabilizer) : False := by
  obtain ⟨P,hP⟩ := h.component_sylow
  obtain ⟨K,_hPK,⟨eK⟩,hKinvariant,hKn⟩ :=
    AlternatingSevenSylowLocal.exists_invariant_local_of_odd_center e ho P
  let A := K.map L.subtype
  have hAc : A ∈ Chapter1.He G := by
    apply Chapter1.mem_He_iff.mpr
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (K.equivMapOfInjective L.subtype L.subtype_injective)).mp
      (Matrix.PSL3Two.ParabolicCoreModel.core_selfCentralizing eK)
  have hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤ normalizer (A : Set G) := by
    intro s hs
    let α := L.normalizerMonoidHom ⟨s,hs.2⟩
    have hα : (P : Subgroup L).map α.toMonoidHom = P := by
      rw [hP]
      exact LieType.Binary.component_intersection_fixed_by_normalizer _ hs.1 hs.2
    have hK := hKinvariant α hα
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he : (MulAut.conj s).toMonoidHom.comp L.subtype = L.subtype.comp α.toMonoidHom := by
      ext x;rfl
    change (K.map L.subtype).map (MulAut.conj s).toMonoidHom = K.map L.subtype
    rw [map_map,he,← map_map,hK]
  have hAM := component_invariant_local_le hH hempty S h.sylow_le h.component
    h.component_le (map_subtype_le K) hAc hinv
  apply hKn AlternatingSeven.tripleSwap (by decide)
  intro k hk
  have hm : k ∈ M.subgroupOf L := hAM (mem_map_of_mem L.subtype hk)
  have hq : AlternatingSeven.quotientMap e k ∈ AlternatingSeven.alternatingStabilizer :=
    hI ▸ mem_map_of_mem _ hm
  exact (AlternatingSeven.mem_alternatingStabilizer _).mp hq

open Chapter15.Section03.Candidates.ComponentStructure

/-- The marked alternatives of 1.1.5(3)(d), for both A7 and its triple cover,
are excluded from the original empty-Γ-even configuration. The center order
and adapted partition are derived from the actual model action. -/
theorem alternating_seven_action_false
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (h : LocalSetup H L M S z) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (σ : Equiv.Perm (Fin 7)) (hσ : σ.cycleType = {2, 2, 2})
    (ha : AlternatingAction α 7 σ) : False := by
  have main (e : (L ⧸ center L) ≃* AlternatingSeven.A7)
      (hc : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3)
      (ha : ∀ x : L, (AlternatingSeven.quotientMap e (α x) : Equiv.Perm (Fin 7)) =
        σ * (AlternatingSeven.quotientMap e x : Equiv.Perm (Fin 7)) * σ⁻¹) : False := by
    obtain ⟨e', _, hi, _⟩ := AlternatingSeven.exists_partition_identification h e hc α hα σ hσ ha
    have ho : Odd (Nat.card (center L)) := hc.elim (fun hc => hc ▸ (by decide))
      (fun hc => hc ▸ (by decide))
    exact alternating_seven_intersection_false hH hempty h e' ho hi
  rcases ha with ⟨e,ha⟩ | ⟨_,⟨ec⟩,e,ha⟩
  · have hc : Nat.card (center L) = 1 := by
      rw [Nat.card_congr (centerCongr e).toEquiv,
        alternatingGroup.center_eq_bot (by simp)]
      exact card_bot
    let q : (L ⧸ center L) ≃* AlternatingSeven.A7 :=
      ((QuotientGroup.quotientMulEquivOfEq ((eq_bot_iff_card _).mpr hc)).trans
        QuotientGroup.quotientBot).trans e
    exact main q (.inl hc) ha
  · have hc : Nat.card (center L) = 3 := by
      rw [Nat.card_congr ec.toEquiv]
      simp
    exact main e (.inr hc) ha

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection

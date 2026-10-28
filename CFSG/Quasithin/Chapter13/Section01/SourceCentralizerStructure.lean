module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents.Moved
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents.OddCore

/-!
# Original 13.1.12: structure of the actual involution centralizer

The source Sylow upgrade and Fitting argument control the literal preimage
O₂,F(C_G(u)). A central involution of T supplies the original 1.1.6 setup;
inversion of the odd core then makes that core trivial. If C_G(u) escapes
N_G(L), the detected C-component is normalized and fully moved by Ξ_p(L),
and cannot normalize Ξ_p(L) in return. All conclusions retain the original
ambient subgroups and commutators.

The earlier orbit, Frattini action, and central-involution data remain
explicit. The later component-model sieve and full centralizer containment
are separate source obligations.
Source: Aschbacher–Smith, proof of 13.1.12(3), printed pp.873–874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]

/-- The original centralizer has trivial odd core and, if it escapes the
maximal normalizer, an actual component fully moved by the original radical. -/
theorem source_centralizer_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : G) (hu : orderOf u = 2) (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)))
    (hindex : ((centralizer ({u} : Set G)).subgroupOf (T : Subgroup G)).index ≤ 2)
    (hcentral : ∀ g : G,
      (T : Subgroup G) ≤ centralizer ({g * u * g⁻¹} : Set G) →
        centralizer ({g * u * g⁻¹} : Set G) ≤ normalizer (L : Set G))
    (hXMu : XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ s : (normalizer (L : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G),
        ∀ a ∈ A, xiFrattiniAction
          (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
          (XiP_invariant p inf_le_left) s a ∈ A) → A = ⊥ ∨ A = ⊤)
    (z : G) (hz : orderOf z = 2) (hzT : z ∈ (T : Subgroup G))
    (hzcentral : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hCz : centralizer ({z} : Set G) ≤ normalizer (L : Set G)) :
    (twoFittingCore (centralizer ({u} : Set G))).map
        (centralizer ({u} : Set G)).subtype ≤
          normalizer (L : Set G) ⊓ centralizer ({u} : Set G) ∧
      pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥ ∧
      (centralizer ({u} : Set G) ≤ normalizer (L : Set G) ∨
        ∃ K : Subgroup G, K ∈ cComponentsIn (centralizer ({u} : Set G)) ∧
          IsQuasisimple (XiQuotient K) ∧
            ¬ ⁅K,XiP p L⁆ ≤ (centralizer ({u} : Set G)).pCoreIn 2 ∧
              XiP p L ≤ normalizer (K : Set G) ∧ ⁅K,XiP p L⁆ = K ∧
                ¬ K ≤ normalizer (XiP p L : Set G)) := by
  let H := centralizer ({u} : Set G)
  let B := zpowers u
  obtain ⟨hq,hNX,hmax⟩ := RadicalConjugateRigidity.maximal_radical_structure hG T hL hn ho hd
  obtain ⟨hfit,hcomp⟩ := source_centralizer_fitting_and_component hG T hL hn ho hd u hu
    hTM hlocal hindex hcentral hXMu hirr
  obtain ⟨S,hS⟩ := SourceCentralizerSylow.source_centralizer_sylow hG T hL hn ho hd u
    hTM hlocal hindex hcentral hXMu hirr
  have hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G) :=
    hS ▸ inf_le_left
  have hBne : B ≠ ⊥ := zpowers_ne_bot.mpr (by intro he; simp [he] at hu)
  have hB : IsPGroup 2 B := IsPGroup.of_card (n := 1) (by
    simpa only [B,Nat.card_zpowers,pow_one] using hu)
  have hBH : B ≤ H := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCH : centralizer (B : Set G) = H := by
    change centralizer (zpowers u : Set G) = centralizer ({u} : Set G)
    rw [zpowers_eq_closure,centralizer_closure]
  have hHN : H ≤ normalizer (B : Set G) := hCH ▸ Subgroup.centralizer_le_normalizer _
  have h115 : Lemma115Hypotheses H S (normalizer (L : Set G)) z :=
    lemma_1_1_6 hBne hB hBH hCH.le hHN S T hST hz hzT hzcentral hmax hCz
      (fun N hN hTN => mem_He_iff.mpr (hG.evenCharacteristic T N hN hTN))
  have hodd : pPrimeCore 2 H = ⊥ := oddCore_eq_bot_of_twoFitting_le h115
    (hfit.trans inf_le_left)
  refine ⟨hfit,hodd,?_⟩
  rcases hcomp with hc | ⟨K,hK,hQK,hm⟩
  · exact Or.inl hc
  · have hs : Group.IsSolvable (XiP p L) := by
      let : Group.IsNilpotent (XiQuotient (XiP p L)) := hq.isPGroup.isNilpotent
      let : Group.IsNilpotent (pCore 2 (XiP p L)) := pCore_isPGroup.isNilpotent
      exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 (XiP p L))).mpr
        ⟨inferInstance,inferInstance⟩
    exact Or.inr ⟨K,hK,hQK,hm,moved_component_properties_in H (XiP p L) K
      (hG.involution_centralizer_sqtk hu) (hXMu.trans inf_le_right)
      (XiP_isPPerfect p L) hs hK hQK hm⟩

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents

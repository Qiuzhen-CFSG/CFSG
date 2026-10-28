module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.FaithfulTransfer.Seed
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.FaithfulTransfer.Conjugation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.FaithfulTransfer.Selection

/-!
# The faithful component over the conjugated Sylow subgroup

Under the temporary centralization assumption in 13.6.17, construct the
actual replacement K₁ in L_f(G,Tᵍ), inside C_G(a), with its A₅ two-core
quotient and transported Hypothesis 13.3.1(4). The seed a = g z g⁻¹ is
nonidentity and central in Tᵍ, as witnessed by omega-center membership.

The proof derives V(K) ≠ 1 from the earlier seed data, applies the checked
small-index normality and first A.4.9 transfer, selects a moving component
in C_G(a), and applies A.4.9 again. The source inputs include the Sylow
arrangement, index two, 13.6.6 and the invariance from 13.6.14. The full
universal earlier A.3.9(1) stays explicit. The parent source assembly owns
its discharge and the application of the universal 13.6.3(2) consequence
to the constructed witness.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
Lemma 13.6.17, printed pp.930–931.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
open ChapterA.Section04 Chapter1.Section02.Adequate A5Module ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The replacement witness required by the last sentence of 13.6.17.
No transfer witness or intrinsic-module nontriviality is assumed. -/
theorem exists_faithful_component_of_checked_centralizes {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G)
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X)
    (T : Sylow 2 G) (L K : Subgroup G) (z v g : G) (a : Gv v)
    (hA5 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hchoice : UniformA5Choice T L)
    (hK : K ∈ Yz L (T : Subgroup G) z v)
    (hTK : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hvT : v ∈ T) (hv : v ^ 2 = 1)
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hag : (a : G) = MulAut.conj g z)
    (ha : checkedQuotientMap v a ∈ centralizer
      (checkedImage v (Tv (T : Subgroup G) v) : Set (Gcheck v)))
    (hKa : K ≤ Gv (a : G)) :
    let Tg := T.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
    (a : G) ≠ 1 ∧
      (a : G) ∈ omegaOneCenterAmbient (Tg : Subgroup G) ∧
      ∃ K₁ : Subgroup G, K₁ ∈ MainForward.faithfulLocalComponents Tg ∧
        K₁ ≤ Gv (a : G) ∧
        Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* alternatingGroup (Fin 5)) ∧
        UniformA5Choice Tg K₁ := by
  dsimp only
  let Tg := T.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have ha1 : (a : G) ≠ 1 := hag ▸ conjugate_seed_ne_one g z hz1
  have haz : (a : G) ∈ omegaOneCenterAmbient (Tg : Subgroup G) :=
    hag ▸ conjugate_seed_mem_omegaCenter T g z hz
  obtain ⟨haT, ha2, haC⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp haz
  have haord : orderOf (a : G) = 2 := orderOf_eq_prime_iff.mpr ⟨ha2, ha1⟩
  have hTa : (Tg : Subgroup G) ≤ Gv (a : G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (haC t ht)
  have hchar : HasCharacteristicTwo (Gv (a : G)) := Chapter1.mem_He_iff.mp
    (Chapter1.twoLocal_mem_He_of_sylow_le Tg (hG.evenCharacteristic Tg)
      (Theory.GroupTheory.isTwoLocal_involution_centralizer haord) hTa)
  obtain ⟨hzT, hz2, hzC⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hzv : z ∈ omegaOneCenterAmbient (Tv (T : Subgroup G) v) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨⟨hzT, mem_centralizer_singleton_iff.mpr (hzC v hvT).symm⟩,
      hz2, fun t ht => hzC t ht.1⟩
  have hintrinsic := intrinsic_module_ne_bot_of_source_seed (T : Subgroup G) L K z v
    hK hTK hSylow hzv hf
  have hm := moves_centralizer_core_of_intrinsic_module T L K z v a hK hv hidx
    hTK ha hKa hintrinsic hchar
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.1.2
  obtain ⟨K₁, hK₁, hfaith⟩ := faithful_component_of_moving_core hG hA39 Tg (a : G)
    haord hTa K hKa hm
  have hchoiceg : UniformA5Choice Tg L :=
    uniformA5Choice_map_replacement hG.evenCharacteristic T L L (MulAut.conj g) hchoice hA5
  exact ⟨ha1, haz, K₁, hfaith, hK₁.1, hchoiceg hA5 K₁ hfaith,
    uniformA5Choice_replacement Tg L K₁ hchoiceg hA5⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields

end

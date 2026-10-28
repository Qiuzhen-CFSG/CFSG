module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.Inputs
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.LocalFacts
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.ResidualA4.Component
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.ResidualA4.MarkedInvolution
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.ResidualA4.ModelFacts
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.ResidualA4.CoverRigidity
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.ResidualA4.LocalRecognition
/-!
# Component and A₄ extraction in the S₆ paragraph

`Component` proves O^{3′}(Gᵥ) = K and Lᵥ ≤ K using the exact earlier
conjugacy alternative. `MarkedInvolution` supplies an involution of Lᵥ
which is not central. After intrinsic A₆ cover rigidity removes the center
of K, the literal component action embeds Lᵥ in A₆ ≤ S₆. Its order is
divisible by six, it is two-perfect, and the marked a induces a nontrivial
involution centralizing its image. The intrinsic S₆ local-recognition fact
then identifies Lᵥ with A₄.

`residual_isA4` supplies both proved intrinsic model facts to the source
application. Only the preceding universal `EarlierConjugates` contract
remains explicit, as in `Component`; no A.3.18 or further model assumption
is needed. Together with `primeToResidual_eq_component` and
`residual_le_component`, this completes the component and A₄ extraction.
The S₆ branch owner uses this result in the independent block-recognition
argument and its subsequent contradiction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the S₆
paragraph of 13.6.6, printed p.927, with the marked module on p.926.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
open A5Module
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}

private def residualToComponent (K : Subgroup (Gv (markedV s)))
    (hle : residual s ≤ K) : Lv L (markedV s) →* K :=
  (inclusion hle).comp (subgroupOfEquivOfLe (Lv_le_Gv L (markedV s))).symm.toMonoidHom

omit [Finite G] in
private theorem residualToComponent_injective (K : Subgroup (Gv (markedV s)))
    (hle : residual s ≤ K) : Function.Injective (residualToComponent K hle) :=
  (inclusion_injective hle).comp (subgroupOfEquivOfLe (Lv_le_Gv L (markedV s))).symm.injective

/-- Apply central-cover rigidity to the noncentral involution constructed
inside the literal marked residual. -/
theorem component_center_eq_bot_of_cover_rigidity
    (cover : SixCoverRigidity.{u}) (d : Setup κ T s)
    (m : ModuleData s) (earlier : EarlierConjugates κ)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (e : XStar K ≃* Equiv.Perm (Fin 6)) : center K = ⊥ := by
  let : IsQuasisimple K := hK.2
  let j := residualToComponent K (residual_le_component d m earlier hodd K hK e)
  have hj : Function.Injective j := residualToComponent_injective K _
  apply cover K (hK.1.pPrimeCore_eq_bot hodd K) (componentCentralQuotientEquivSix K hK e)
  obtain ⟨x, hx, hxc⟩ := exists_residual_moved_involution d
  refine ⟨j x, (orderOf_injective j hj x).trans hx, ?_⟩
  intro hc
  apply hxc
  apply mem_center_iff.mpr
  intro y
  apply hj
  simpa only [map_mul] using mem_center_iff.mp hc (j y)

/-- Assembly for the S₆ paragraph from the two universal intrinsic model
contracts, with every source-specific premise proved here. `residual_isA4`
below supplies their proved instances. -/
theorem residual_isA4_of_model_facts
    (cover : SixCoverRigidity.{u}) (localRecognition : SixLocalRecognition)
    (d : Setup κ T s) (m : ModuleData s) (earlier : EarlierConjugates κ)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) (e : XStar K ≃* Equiv.Perm (Fin 6)) :
    Nonempty (Lv L (markedV s) ≃* alternatingGroup (Fin 4)) := by
  have hz := component_center_eq_bot_of_cover_rigidity cover d m earlier hodd K hK e
  have hle := residual_le_component d m earlier hodd K hK e
  let j := residualToComponent K hle
  have hj : Function.Injective j := residualToComponent_injective K hle
  have hcm : Function.Injective (NormalizerAction.componentMap K) := by
    apply (NormalizerAction.componentMap K).ker_eq_bot_iff.mp
    rw [NormalizerAction.componentMap_ker, hz]
  let f : Lv L (markedV s) →* Equiv.Perm (Fin 6) :=
    e.toMonoidHom.comp ((NormalizerAction.componentMap K).comp j)
  have hf : Function.Injective f := e.injective.comp (hcm.comp hj)
  let D := f.range
  let eD : Lv L (markedV s) ≃* D := MonoidHom.ofInjective hf
  have hDa : D ≤ alternatingGroup (Fin 6) := by
    rintro y ⟨x, rfl⟩
    rw [← component_image_eq_alternating K hK e]
    apply mem_map_of_mem
    rw [← NormalizerAction.componentMap_range]
    exact ⟨j x, rfl⟩
  have hDp : IsPPerfect 2 D :=
    (isPPerfect_embedded_pResidual 2 (L ⊓ Gv (markedV s))).of_surjective
      f.rangeRestrict f.rangeRestrict_surjective
  have hD3 : 3 ∣ Nat.card D := by
    rw [← Nat.card_congr eD.toEquiv]
    exact three_dvd_card_residual m
  have hD2 : 2 ∣ Nat.card D := by
    obtain ⟨x, hx, _⟩ := exists_residual_moved_involution d
    have hh := orderOf_dvd_natCard (eD x)
    have ho : orderOf (eD x) = 2 :=
      (orderOf_injective eD.toMonoidHom eD.injective x).trans hx
    rwa [ho] at hh
  let aX : X K := ⟨aLocal s, a.a_normalizes⟩
  let σ : Equiv.Perm (Fin 6) := e (NormalizerAction.quotient K aX)
  have hσ2 : orderOf σ = 2 := by
    apply (orderOf_eq_prime_iff (p := 2)).mpr
    constructor
    · have ha2 : aX ^ 2 = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        change (s.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.a)) ^ 2 = 1
        rw [← map_pow, show (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.a) ^ 2 = 1 by decide +kernel,
          map_one]
      change e (NormalizerAction.quotient K aX) ^ 2 = 1
      rw [← map_pow, ← map_pow, ha2, map_one, map_one]
    · intro he
      have hq : NormalizerAction.quotient K aX = 1 := e.map_eq_one_iff.mp he
      exact (hK.not_centralizes_of_twoCore_centralizer (aLocal s) d.centralizer_cores.1)
        ((NormalizerAction.quotient_eq_one_iff K aX).mp hq)
  have hσD : σ ∈ centralizer (D : Set _) := by
    apply mem_centralizer_iff.mpr
    rintro y ⟨x, rfl⟩
    let xX : X K := inclusion K.le_normalizer (j x)
    have hax : xX * aX = aX * xX := by
      apply Subtype.ext
      apply Subtype.ext
      exact mem_centralizer_iff.mp d.a_centralizes x x.property
    change e (NormalizerAction.quotient K xX) * e (NormalizerAction.quotient K aX) =
      e (NormalizerAction.quotient K aX) * e (NormalizerAction.quotient K xX)
    simpa only [map_mul] using
      congrArg (fun w : X K => e (NormalizerAction.quotient K w)) hax
  obtain ⟨i⟩ := localRecognition D hDa hDp hD3 hD2 σ hσ2 hσD
  exact ⟨eD.trans i⟩

/-- The actual marked residual is A₄ in the S₆ branch of 13.6.6.
Central-cover rigidity and involution-centralizer recognition are discharged;
the explicit earlier input is the full universal A.3.8(3) contract. -/
theorem residual_isA4
    (d : Setup κ T s) (m : ModuleData s) (earlier : EarlierConjugates κ)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) (e : XStar K ≃* Equiv.Perm (Fin 6)) :
    Nonempty (Lv L (markedV s) ≃* alternatingGroup (Fin 4)) :=
  residual_isA4_of_model_facts sixCoverRigidity sixLocalRecognition d m earlier hodd K hK a e

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix

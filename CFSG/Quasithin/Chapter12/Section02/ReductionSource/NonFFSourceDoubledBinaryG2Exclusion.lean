module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryG2Exclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryG2Placement

/-!
# G₂ exclusion on the original chosen paired plane

For each remaining G₂ component, the original Sylow lies in Q and the
component is relatively normal. Its canonical inner image is fixed by Q.
Ratios of the fixed highest-root parameters construct at least fifteen
scalar actors normalizing this same Q. Characteristic-normalizer control
places them in M. Their action on the literal paired-plane quotient has
order at most six, a contradiction.

Thus only genuine triality and Ree F₄ component models remain. Their
exclusions, ambient containment and final doubled contradiction remain with
qt-d-1222-nonff-doubled. No additional geometric premise is assumed here.
Source: Aschbacher–Smith 7.7.6, printed p.706, refs/quasithin.pdf; the scalar
argument is an alternative to local C(G,Q) for this particular row.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore
open DoubledBinaryG2Exclusion
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Only twisted exceptional components remain on the same original paired plane. -/
theorem sourceOrbit_binary_pairedPlane_twisted_components_with_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
          DoubledBinaryOmega.HasMarking D.sourceOrbit L E ∧
          let U := ambientPlane D.sourceOrbit E v f
          let B := localBase L (T : Subgroup G) U
          let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
          let S₀ := (T : Subgroup G) ⊓ centralizer (U : Set G)
          let A := ⁅D.sourceOrbit,localResidual L U⁆
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = Q ∧
          U ⊔ ⁅D.sourceOrbit,localResidual L U⁆ = D.sourceOrbit ∧
          Q.characteristicNormalizerClosure ≤ normalizer (L : Set G) ∧
          Nonempty (inducedAutomizer D.sourceOrbit (centralizer (U : Set G)) ≃* Equiv.Perm (Fin 3)) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              pPrimeCore 2 H = ⊥ ∧ D.sourceOrbit ⊓ centralizer (K : Set G) = U ∧
              ∃ hAN : A ≤ normalizer (K : Set G),
                A ⊓ centralizer (K : Set G) = ⊥ ∧ Nat.card (inducedAutomizer K A) = 16 ∧
                ∃ j : A →* K ⧸ center K, Function.Injective j ∧
                  (∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                    K.normalizerMonoidHom (inclusion hAN a)) ∧
                  Nat.card j.range = 16 ∧ IsElementaryAbelian 2 j.range ∧
                  ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype ≤ S₀ ∧
                    let R := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
                    j.range ≤ (R : Subgroup _) ∧
                    ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
                      (R : Subgroup _)).index ≤ 2 ∧
              ((∃ n : ℕ, 2 ≤ n ∧
                Triality.Standard.IsTrialityGroupAt (2^n) (K ⧸ center K)) ∨
              ∃ m : ℕ, 1 ≤ m ∧ Chapter1.Section02.LocalModels.IsReeF4At (K ⧸ center K) m)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hgen,hctl,hquot,hcomp⟩ :=
    D.sourceOrbit_binary_pairedPlane_g2_placement_with_marking h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let A := ⁅D.sourceOrbit,localResidual L U⁆
  let B := localBase L (T : Subgroup G) U
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hAW : A ≤ D.sourceOrbit := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes))
  have hUW := ambientPlane_le_orbit D.sourceOrbit E v f
  have hQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hU : U ≠ ⊥ := by
    intro he
    have hh := DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv
    change Nat.card U = 4 at hh
    rw [he,Subgroup.card_bot] at hh
    omega
  have hQne : Q ≠ ⊥ := by
    intro hh
    have hUQ : U ≤ Q := hUW.trans (D.sourceOrbit_core_normalizer h).1
    exact hU (le_bot_iff.mp (hh ▸ hUQ))
  have hNQ : normalizer (Q : Set G) ≤ normalizer (D.sourceOrbit : Set G) := by
    rw [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]
    exact (normalizer_le_characteristicNormalizerClosure_self Q hQne).trans hctl
  have hQW : Q ≤ centralizer (D.sourceOrbit : Set G) := by
    rw [←hQ]
    exact inf_le_right
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hgen,hctl,hquot,?_⟩
  intro H hBH hHC K hK
  obtain ⟨hodd,hfix,hAN,hker,horder,j,hj,hjact,hjcard,hje,P,hPS,hQj,hC,hg2,hmodels⟩ :=
    hcomp H hBH hHC K hK
  refine ⟨hodd,hfix,hAN,hker,horder,j,hj,hjact,hjcard,hje,P,hPS,hQj,hC,?_⟩
  rcases hmodels with ⟨n,hn,hm | hm⟩ | hm
  · obtain ⟨_,_,hnormal,_,hPQ,_⟩ := hg2 n hn hm
    have hQH : Q ≤ H := by
      rw [←hQ]
      exact (inf_le_inf_left _ (centralizer_le hUW)).trans (le_sup_right.trans hBH)
    have hQN : Q ≤ normalizer (K : Set G) := hQH.trans
      ((normal_subgroupOf_iff_le_normalizer hK.1).mp hnormal)
    let := hK.quasisimple
    exact (g2_exclusion D.sourceOrbit U K A Q hAW (hK.1.trans hHC) hAN hQN hQW
      (isPGroup_pCoreIn 2 _) hNQ hquot j hjcard hjact P hPQ hQj hC hn hm).elim
  · exact Or.inl ⟨n,hn,hm⟩
  · exact Or.inr hm

/-- Original interface, retaining all mathematical conclusions. -/
theorem sourceOrbit_binary_pairedPlane_twisted_components
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
          let U := ambientPlane D.sourceOrbit E v f
          let B := localBase L (T : Subgroup G) U
          let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
          let S₀ := (T : Subgroup G) ⊓ centralizer (U : Set G)
          let A := ⁅D.sourceOrbit,localResidual L U⁆
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = Q ∧
          U ⊔ ⁅D.sourceOrbit,localResidual L U⁆ = D.sourceOrbit ∧
          Q.characteristicNormalizerClosure ≤ normalizer (L : Set G) ∧
          Nonempty (inducedAutomizer D.sourceOrbit (centralizer (U : Set G)) ≃* Equiv.Perm (Fin 3)) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              pPrimeCore 2 H = ⊥ ∧ D.sourceOrbit ⊓ centralizer (K : Set G) = U ∧
              ∃ hAN : A ≤ normalizer (K : Set G),
                A ⊓ centralizer (K : Set G) = ⊥ ∧ Nat.card (inducedAutomizer K A) = 16 ∧
                ∃ j : A →* K ⧸ center K, Function.Injective j ∧
                  (∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                    K.normalizerMonoidHom (inclusion hAN a)) ∧
                  Nat.card j.range = 16 ∧ IsElementaryAbelian 2 j.range ∧
                  ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype ≤ S₀ ∧
                    let R := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
                    j.range ≤ (R : Subgroup _) ∧
                    ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
                      (R : Subgroup _)).index ≤ 2 ∧
              ((∃ n : ℕ, 2 ≤ n ∧
                Triality.Standard.IsTrialityGroupAt (2^n) (K ⧸ center K)) ∨
              ∃ m : ℕ, 1 ≤ m ∧ Chapter1.Section02.LocalModels.IsReeF4At (K ⧸ center K) m)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,_,hrest⟩ :=
    D.sourceOrbit_binary_pairedPlane_twisted_components_with_marking h hd hnon F hF hmodel
  exact ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hrest⟩


end CFSG.Quasithin.Chapter12.Section02.ChosenModule

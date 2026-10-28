module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryRootCentralization

/-!
# The actual component Sylow normalizer escapes M

On the original chosen doubled orbit, the classical and Bender Cartan
calculations force centralizer index greater than six in the canonical
quotient Sylow normalizer. The original component Sylow normalizer
therefore cannot be contained in M=N_G(L): otherwise the paired-plane
S₃ action on the whole orbit would give index at most six. This uses the
literal inner-action map and the original component Sylow, including its
ambient placement. Both seed axes, field parameters and conjugator are
preserved.

Source: Aschbacher–Smith, proof of 7.7.6, printed p.706,
refs/quasithin.pdf. The local C(G,T) argument establishing the opposite
containment, exceptional Lie rows and final ambient paired-plane
containment remain with qt-d-1222-nonff-doubled.
-/

public noncomputable section

open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore
open DoubledBinaryInnerAction DoubledBinarySylowFixed DoubledBinaryComponentModels
open DoubledBinaryComponentSylow DoubledBinaryRootCentralization DoubledBinaryCartan
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every Bender or classical component forces the original Sylow normalizer
outside M, retaining all the earlier data on the same original paired plane. -/
theorem sourceOrbit_binary_pairedPlane_cartan_with_marking
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
          let S₀ := (T : Subgroup G) ⊓ centralizer (U : Set G)
          let A := ⁅D.sourceOrbit,localResidual L U⁆
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          Disjoint U A ∧ Nat.card A = 16 ∧
          Nonempty (inducedAutomizer D.sourceOrbit (centralizer (U : Set G)) ≃*
            Equiv.Perm (Fin 3)) ∧
          S₀ ≤ normalizer (A : Set G) ∧
          ((centralizer (D.sourceOrbit : Set G)).subgroupOf S₀).index ≤ 2 ∧
          4 ≤ Nat.card ((centralizer (S₀ : Set G)).subgroupOf A) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              D.sourceOrbit ⊓ centralizer (K : Set G) = U ∧
              ∃ hAN : A ≤ normalizer (K : Set G),
                A ⊓ centralizer (K : Set G) = ⊥ ∧
                Nat.card (inducedAutomizer K A) = 16 ∧
                (∀ a : A, K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K) ∧
                (∃ j : A →* K ⧸ center K, Function.Injective j ∧
                  (∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                    K.normalizerMonoidHom (inclusion hAN a)) ∧
                  Nat.card j.range = 16 ∧ IsElementaryAbelian 2 j.range ∧
                  ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype ≤ S₀ ∧
                    let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
                    j.range ≤ (Q : Subgroup _) ∧
                    ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
                      (Q : Subgroup _)).index ≤ 2 ∧
                    (ClassificationModels.IsBenderModel (K ⧸ center K) →
                      j.range ≤ (center Q).map (Q : Subgroup _).subtype) ∧
                    (∀ n : ℕ, 2 ≤ n → ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n) →
                      j.range ≤ (center Q).map (Q : Subgroup _).subtype ∧ 4 ≤ n) ∧
                    (∀ n : ℕ, 2 ≤ n → ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n) →
                      j.range ≤ (center Q).map (Q : Subgroup _).subtype) ∧
                    (∀ n : ℕ, 2 ≤ n → ClassicalGroup.IsPSL (K ⧸ center K) 2 (2 ^ n) → 4 ≤ n) ∧
                    (∀ n : ℕ, 2 ≤ n → ClassicalGroup.IsPSU (K ⧸ center K) 3 (2 ^ n) → 4 ≤ n) ∧
                    (∀ m : ℕ, 1 ≤ m → Nonempty ((K ⧸ center K) ≃*
                      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) → 2 ≤ m) ∧
                    (ClassificationModels.IsBenderModel (K ⧸ center K) ∨
                      (∃ n : ℕ, 2 ≤ n ∧ (ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n) ∨
                        ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n))) →
                      6 < ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
                        (normalizer (Q : Set (K ⧸ center K)))).index ∧
                      ¬ (normalizer (P : Set K)).map K.subtype ≤ normalizer (L : Set G))) ∧
                4 ≤ primeRank 2 (K ⧸ center K) ∧
                (∃ P : Sylow 2 (K ⧸ center K), ¬ IsCyclic (center P)) ∧
                NonbinaryLieModel (K ⧸ center K)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hdis,hcard,hquot,hn,hi,hfixed,hcomp⟩ :=
    D.sourceOrbit_binary_pairedPlane_rootCentralization_with_marking h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let R := localResidual L U
  let A := ⁅D.sourceOrbit,R⁆
  have hRW : R ≤ normalizer (D.sourceOrbit : Set G) :=
    (map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes)
  have hAW : A ≤ D.sourceOrbit := le_normalizer_iff_commutator_le_left.mp hRW
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hdis,hcard,hquot,hn,hi,hfixed,?_⟩
  intro H hBH hHC K hK
  obtain ⟨hfix,hAN,hker,horder,hinner,
    ⟨j,hj,hjact,hjcard,hje,P,hPS,hQ,hC,hb,hl,hsp,hltwo,hu,hsz⟩,
    hr,hcenter,hm⟩ := hcomp H hBH hHC K hK
  let := hje
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
  refine ⟨hfix,hAN,hker,horder,hinner,
    ⟨j,hj,hjact,hjcard,hje,P,hPS,hQ,hC,hb,hl,hsp,hltwo,hu,hsz,?_⟩,
    hr,hcenter,hm⟩
  intro hclass
  have hlarge : 6 < ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
      (normalizer (Q : Set (K ⧸ center K)))).index := by
    rcases hclass with hclass | ⟨n,hn,hm | hm⟩
    · have hh := bender_normalizer_index hclass Q j.range hQ hjcard
      omega
    · have hh := linear_normalizer_index hn hm Q j.range hQ hjcard hC
      omega
    · have hh := symplectic_normalizer_index hn hm Q j.range hQ hjcard hC
      omega
  refine ⟨hlarge,?_⟩
  have hescape := normalizer_escape D.sourceOrbit U K A hAW (hK.1.trans hHC)
    hAN hquot j hjact P hlarge
  rwa [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd] at hescape

/-- Original interface, retaining all mathematical conclusions. -/
theorem sourceOrbit_binary_pairedPlane_cartan
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
          let S₀ := (T : Subgroup G) ⊓ centralizer (U : Set G)
          let A := ⁅D.sourceOrbit,localResidual L U⁆
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          Disjoint U A ∧ Nat.card A = 16 ∧
          Nonempty (inducedAutomizer D.sourceOrbit (centralizer (U : Set G)) ≃*
            Equiv.Perm (Fin 3)) ∧
          S₀ ≤ normalizer (A : Set G) ∧
          ((centralizer (D.sourceOrbit : Set G)).subgroupOf S₀).index ≤ 2 ∧
          4 ≤ Nat.card ((centralizer (S₀ : Set G)).subgroupOf A) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              D.sourceOrbit ⊓ centralizer (K : Set G) = U ∧
              ∃ hAN : A ≤ normalizer (K : Set G),
                A ⊓ centralizer (K : Set G) = ⊥ ∧
                Nat.card (inducedAutomizer K A) = 16 ∧
                (∀ a : A, K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K) ∧
                (∃ j : A →* K ⧸ center K, Function.Injective j ∧
                  (∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                    K.normalizerMonoidHom (inclusion hAN a)) ∧
                  Nat.card j.range = 16 ∧ IsElementaryAbelian 2 j.range ∧
                  ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype ≤ S₀ ∧
                    let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
                    j.range ≤ (Q : Subgroup _) ∧
                    ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
                      (Q : Subgroup _)).index ≤ 2 ∧
                    (ClassificationModels.IsBenderModel (K ⧸ center K) →
                      j.range ≤ (center Q).map (Q : Subgroup _).subtype) ∧
                    (∀ n : ℕ, 2 ≤ n → ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n) →
                      j.range ≤ (center Q).map (Q : Subgroup _).subtype ∧ 4 ≤ n) ∧
                    (∀ n : ℕ, 2 ≤ n → ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n) →
                      j.range ≤ (center Q).map (Q : Subgroup _).subtype) ∧
                    (∀ n : ℕ, 2 ≤ n → ClassicalGroup.IsPSL (K ⧸ center K) 2 (2 ^ n) → 4 ≤ n) ∧
                    (∀ n : ℕ, 2 ≤ n → ClassicalGroup.IsPSU (K ⧸ center K) 3 (2 ^ n) → 4 ≤ n) ∧
                    (∀ m : ℕ, 1 ≤ m → Nonempty ((K ⧸ center K) ≃*
                      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) → 2 ≤ m) ∧
                    (ClassificationModels.IsBenderModel (K ⧸ center K) ∨
                      (∃ n : ℕ, 2 ≤ n ∧ (ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n) ∨
                        ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n))) →
                      6 < ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
                        (normalizer (Q : Set (K ⧸ center K)))).index ∧
                      ¬ (normalizer (P : Set K)).map K.subtype ≤ normalizer (L : Set G))) ∧
                4 ≤ primeRank 2 (K ⧸ center K) ∧
                (∃ P : Sylow 2 (K ⧸ center K), ¬ IsCyclic (center P)) ∧
                NonbinaryLieModel (K ⧸ center K)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,_,hrest⟩ :=
    D.sourceOrbit_binary_pairedPlane_cartan_with_marking h hd hnon F hF hmodel
  exact ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hrest⟩


end CFSG.Quasithin.Chapter12.Section02.ChosenModule

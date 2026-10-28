module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryRootCentralization
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryComponentSylow

/-!
# Root centralization on the original paired plane

The projected moving sixteen centralizes the actual quotient Sylow in
each Bender, linear and symplectic row. The same original field degree is
at least four in the linear and unitary rows, and the Suzuki parameter is
at least two. All maps, seed axes, the conjugator and the local base are
those supplied by the original chosen-module construction.

These are the classical root-group deductions in 7.7.6, printed p.706,
refs/quasithin.pdf. The exceptional rows, central-cover lifting and ambient
Cartan placement remain with qt-d-1222-nonff-doubled.
-/

public noncomputable section

open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore
open DoubledBinaryInnerAction DoubledBinarySylowFixed DoubledBinaryComponentModels
open DoubledBinaryComponentSylow DoubledBinaryRootCentralization
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The source moving sixteen is central in its specified quotient Sylow
for the Bender and classical rows, with the original parameters restricted. -/
theorem sourceOrbit_binary_pairedPlane_rootCentralization_with_marking
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
                      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) → 2 ≤ m)) ∧
                4 ≤ primeRank 2 (K ⧸ center K) ∧
                (∃ P : Sylow 2 (K ⧸ center K), ¬ IsCyclic (center P)) ∧
                NonbinaryLieModel (K ⧸ center K)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hdis,hcard,hquot,hn,hi,hfixed,hcomp⟩ :=
    D.sourceOrbit_binary_pairedPlane_componentSylow_with_marking h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hdis,hcard,hquot,hn,hi,hfixed,?_⟩
  intro H hBH hHC K hK
  obtain ⟨hfix,hAN,hker,horder,hinner,⟨j,hj,hjact,hjcard,hje,P,hPS,hQ,hC⟩,
    hr,hcenter,hm⟩ := hcomp H hBH hHC K hK
  let := hje
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
  refine ⟨hfix,hAN,hker,horder,hinner,⟨j,hj,hjact,hjcard,hje,P,hPS,hQ,hC,?_,?_,?_,?_,?_,?_⟩,
    hr,hcenter,hm⟩
  · exact fun hb => bender_centralizes hb Q j.range hQ
  · intro n hn hm
    exact ⟨linear_centralizes hn hm Q j.range hQ hC,
      linear_degree_ge_four hn hm Q j.range hQ hjcard hC⟩
  · exact fun n hn hm => symplectic_centralizes hn hm Q j.range hQ hC
  · exact fun n hn hm => linearTwo_degree_ge_four hn hm Q j.range hQ hjcard
  · exact fun n hn hm => unitary_degree_ge_four hn hm Q j.range hQ hjcard
  · exact fun m hm he => suzuki_parameter_ge_two hm he Q j.range hQ hjcard

/-- Original interface, retaining all mathematical conclusions. -/
theorem sourceOrbit_binary_pairedPlane_rootCentralization
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
                      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) → 2 ≤ m)) ∧
                4 ≤ primeRank 2 (K ⧸ center K) ∧
                (∃ P : Sylow 2 (K ⧸ center K), ¬ IsCyclic (center P)) ∧
                NonbinaryLieModel (K ⧸ center K)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,_,hrest⟩ :=
    D.sourceOrbit_binary_pairedPlane_rootCentralization_with_marking h hd hnon F hF hmodel
  exact ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hrest⟩


end CFSG.Quasithin.Chapter12.Section02.ChosenModule

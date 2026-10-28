module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCoverPlacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryCartan

open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
/-!
# Original component Sylows and characteristic-normalizer control

On the same marked paired plane, the covering calculations lift the moving
sixteen's centralization to each original Bender or classical component
Sylow. The plane and moving sixteen span the original orbit W, so the
component Sylow lies in the actual Q=O₂(LT)=C_T(W). Component conjugacy
makes Q Sylow in KQ. Uniqueness for LT controls every nontrivial
characteristic subgroup of Q and hence C(G,Q); that control restricts to
the literal KQ join. The previously proved Cartan normalizer escape is
retained on the same component Sylow.

The exceptional rows, the opposite Borel containment, ambient paired-plane
containment and final non-FF contradiction remain with
qt-d-1222-nonff-doubled. No local C theorem conclusion is assumed here.
Source: Aschbacher–Smith, proof of 7.7.6, printed p.706, refs/quasithin.pdf.
-/
public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore
open DoubledBinaryCoverPlacement
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

include D in
/-- The actual Q=O₂(LT) has full ambient characteristic-normalizer control. -/
theorem sourceOrbit_core_characteristic_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).characteristicNormalizerClosure ≤
      normalizer (L : Set G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hnorm : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro C hC hne
  let := hC
  exact D.normal_subgroup_normalizer_le h.toHypothesis1221
    ((map_subtype_le C).trans (pCoreIn_le 2 _))
    (fun he => hne ((C.map_eq_bot_iff_of_injective Q.subtype_injective).mp he))
    (hnorm.trans (normalizer_le_normalizer_characteristic_image Q C))

/-- On one original Sylow-placed paired plane, every surviving Bender or
classical component has its original Sylow in Q and an escaping Sylow
normalizer. Q is Sylow in its actual join with the component; C of that
join is controlled by M. No abstract sixteen is treated as a Sylow. -/
theorem sourceOrbit_binary_pairedPlane_coverPlacement
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
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = Q ∧
          U ⊔ ⁅D.sourceOrbit,localResidual L U⁆ = D.sourceOrbit ∧
          Q.characteristicNormalizerClosure ≤ normalizer (L : Set G) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              (ClassificationModels.IsBenderModel (K ⧸ center K) ∨
                (∃ n : ℕ, 2 ≤ n ∧ (ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n) ∨
                  ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n)))) →
              Odd (Nat.card (center K)) ∧
              (∀ n : ℕ, 2 ≤ n → ClassicalGroup.IsPSL (K ⧸ center K) 2 (2 ^ n) → 4 ≤ n) ∧
              (∀ m : ℕ, 1 ≤ m → Nonempty ((K ⧸ center K) ≃*
                BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) → 2 ≤ m) ∧
              (∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype ≤ Q ∧
                ¬ (normalizer (P : Set K)).map K.subtype ≤ normalizer (L : Set G)) ∧
              ∃ S : Sylow 2 (K ⊔ Q : Subgroup G),
                (S : Subgroup _).map (K ⊔ Q).subtype = Q ∧
                (S : Subgroup _).characteristicNormalizerClosure ≤
                  (normalizer (L : Set G)).subgroupOf (K ⊔ Q)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hS,hbase,hcore,hdis,hcard,hquot,hn,hi,hfixed,hcomp⟩ :=
    D.sourceOrbit_binary_pairedPlane_cartan h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let R := localResidual L U
  let A := ⁅D.sourceOrbit,R⁆
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hAW : A ≤ D.sourceOrbit := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes))
  have hUW := ambientPlane_le_orbit D.sourceOrbit E v f
  have hgen : U ⊔ A = D.sourceOrbit := by
    apply eq_of_le_of_card_ge (sup_le hUW hAW)
    have hnorm : A ≤ normalizer (U : Set G) := hAW.trans
      (((le_centralizer D.sourceOrbit).trans (centralizer_le hUW)).trans
        (Subgroup.centralizer_le_normalizer _))
    have hW : Nat.card D.sourceOrbit = 64 := by
      change Nat.card (Additive D.sourceOrbit) = 64
      rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2)]
      norm_num [NaturalDual.Space,Module.finrank_prod,BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    rw [card_sup_eq_mul_of_normalizes_of_disjoint U A hnorm hdis,hcard,hW,
      DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv]
  have hQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hctl := D.sourceOrbit_core_characteristic_control h
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hS,hbase,hcore,hgen,hctl,?_⟩
  intro H hBH hHC K hK hclass
  let := hK.quasisimple
  obtain ⟨hfix,hAN,hker,horder,hinner,
    ⟨j,hj,hjact,hjcard,hje,P,hPS,hQj,hC,hb,hl,hsp,hltwo,hu,hsz,he⟩,
    hr,hcenter,hm⟩ := hcomp H hBH hHC K hK
  have ho : Odd (Nat.card (center K)) := by
    rcases hclass with hclass | ⟨n,hn,hm | hm⟩
    · cases hclass with
      | linear n hn hm => exact linearTwo_odd_center (hltwo n hn hm) hm
      | unitary n hn hm => exact unitary_odd_center hn hm
      | suzuki m hm he => exact suzuki_odd_center (hsz m hm he) he
    · exact linearThree_odd_center (hl n hn hm).2 hm
    · exact symplectic_odd_center hn hm
  have hcentral : j.range ≤ (center (P.mapSurjective
      (QuotientGroup.mk'_surjective (center K)))).map
      (P.mapSurjective (QuotientGroup.mk'_surjective (center K)) : Subgroup _).subtype := by
    rcases hclass with hclass | ⟨n,hn,hm | hm⟩
    · exact hb hclass
    · exact (hl n hn hm).1
    · exact hsp n hn hm
  have hPC := centralizes_original_sylow K A ho hAN j hjact P hcentral
  have hPQ : (P : Subgroup K).map K.subtype ≤ Q :=
    original_sylow_le_core K A U D.sourceOrbit (T : Subgroup G) Q hgen hQ
      (hK.1.trans hHC) P (hPS.trans inf_le_left) hPC
  have hQH : Q ≤ H := by
    rw [←hQ]
    exact (inf_le_inf_left _ (centralizer_le hUW)).trans (le_sup_right.trans hBH)
  obtain ⟨S,hS⟩ := core_sylow_join H K Q hK hQH (isPGroup_pCoreIn 2 _) P hPQ
  refine ⟨ho,hltwo,hsz,⟨P,hPQ,(he hclass).2⟩,S,hS,?_⟩
  have hSq : (S : Subgroup (K ⊔ Q : Subgroup G)) = Q.subgroupOf (K ⊔ Q) := by
    apply map_injective (K ⊔ Q).subtype_injective
    rw [hS,map_subgroupOf_eq_of_le (show Q ≤ K ⊔ Q from le_sup_right)]
  rw [hSq]
  exact characteristicNormalizerClosure_subgroupOf_le le_sup_right hctl
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

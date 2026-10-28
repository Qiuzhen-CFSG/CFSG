module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryInnerAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryIntersection

/-!
# Inner component action on the original binary doubled orbit

For the same Sylow-placed paired plane and original local residual L₀,
every ordinary component K of a local-base overgroup admits the faithful
inner action of A=[W,L₀]. The full source SQTK hypotheses supply the model
inspection, and residual commutator idempotence kills A's outer image.

The literal embedding A → K/Z(K) retains its normalizer conjugation action.
Since A is elementary abelian of order sixteen, the actual central quotient
has two-rank at least four. Both seed axes, the original conjugator, the
Sylow placement, and Q=O₂(L₀T₀) remain part of the conclusion.

This supplies the innerness and rank bound in the proof of 7.7.6. The
component exclusion continues with the Sylow-center and root-group argument.
Source: Aschbacher–Smith, printed pp.705–706, refs/quasithin.pdf.
-/

public noncomputable section

open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore
open DoubledBinaryInnerAction
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- On the original doubled orbit, the order-sixteen residual moving subgroup
acts faithfully by inner automorphisms on every ordinary component of a
paired-plane overgroup. Its actual projective embedding gives two-rank at
least four. The original conjugator and both seed axes are retained. -/
theorem sourceOrbit_binary_pairedPlane_innerAction
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
          let A := ⁅D.sourceOrbit,localResidual L U⁆
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          Disjoint U A ∧ Nat.card A = 16 ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              D.sourceOrbit ⊓ centralizer (K : Set G) = U ∧
              ∃ hAN : A ≤ normalizer (K : Set G),
                A ⊓ centralizer (K : Set G) = ⊥ ∧
                Nat.card (inducedAutomizer K A) = 16 ∧
                (∀ a : A, K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K) ∧
                (∃ j : A →* K ⧸ center K, Function.Injective j ∧
                  ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                    K.normalizerMonoidHom (inclusion hAN a)) ∧
                4 ≤ primeRank 2 (K ⧸ center K)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hS,hbase,hcore,hdis,hcard,_,hcomp⟩ :=
    D.sourceOrbit_binary_pairedPlane_intersections h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := localResidual L U
  let A := ⁅D.sourceOrbit,R⁆
  have hWQ := (D.sourceOrbit_core_normalizer h).1
  have hQB : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ B := hcore ▸ pCoreIn_le 2 B
  have hRW : R ≤ normalizer (D.sourceOrbit : Set G) :=
    (map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes)
  have hAW : A ≤ D.sourceOrbit := le_normalizer_iff_commutator_le_left.mp hRW
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (inclusion hAW) (inclusion_injective hAW)
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hS,hbase,hcore,hdis,hcard,?_⟩
  intro H hBH hHC K hK
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le
    (ambientPlane_le_orbit D.sourceOrbit E v f)
  have hU : U ≠ ⊥ := by
    intro he
    have hh := DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv
    change Nat.card U = 4 at hh
    rw [he,Subgroup.card_bot] at hh
    omega
  have hHN : H ≤ normalizer (U : Set G) := hHC.trans (Subgroup.centralizer_le_normalizer _)
  have hs := (h.simpleQTKE.twoLocal_sqtk (show IsTwoLocal (normalizer (U : Set G)) from
    ⟨U,hU,hp,rfl⟩)).subgroup (H.subgroupOf (normalizer (U : Set G)))
  have hSQ : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp hs
  obtain ⟨hfix,hAN,hker,horder⟩ := hcomp H hBH hHC K hK
  obtain ⟨hAN',hi⟩ := component_movement_inner H D.sourceOrbit R K hSQ hK
    (hWQ.trans (hQB.trans hBH)) (le_sup_left.trans hBH)
    (IsElementaryAbelian.isPGroup 2 D.sourceOrbit)
    (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G))) hRW
  obtain ⟨j,hj,hjact⟩ := faithful_inner_centralQuotient K A hAN' hker hi
  exact ⟨hfix,hAN',hker,horder,hi,⟨j,hj,hjact⟩,
    four_le_rank_centralQuotient K A hcard j hj⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryBenderExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryCoverPlacement

/-!
# Excluding linear-two and Suzuki components on the original paired plane

The actual component Sylow lies in Q. The intrinsic Borel theorem puts its
normalizer in N_G(J(Q)); non-FF Thompson heredity identifies J(Q)=J(T), whose
ambient normalizer is controlled by M. This contradicts the Cartan escape
on exactly the same Sylow and excludes the PSL₂ and Suzuki rows, with their
original field parameters. Strong quasithinness supplies the component-orbit
bound inside the actual plane-centralizer overgroup.

The unitary, linear-three, symplectic and exceptional component rows, ambient
paired-plane containment, and final non-FF contradiction remain with
qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith 7.7.6, printed p.706, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore
open DoubledBinaryBenderExclusion
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Neither a binary linear-two nor a Suzuki ordinary component can occur
above the actual local base on this original Sylow-placed paired plane. -/
theorem sourceOrbit_binary_pairedPlane_no_linearTwo_suzuki
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
              (¬ ∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSL (K ⧸ center K) 2 (2 ^ n)) ∧
              (¬ ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((K ⧸ center K) ≃*
                BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hS,hbase,hcore,hgen,hctl,hcomp⟩ :=
    D.sourceOrbit_binary_pairedPlane_coverPlacement h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hUW := ambientPlane_le_orbit D.sourceOrbit E v f
  have hQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q := by
    rw [←hQ]
    exact le_inf (sSup_le fun _ hA => hA.1)
      (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
  have hJ := (D.sourceOrbit_nonFF_thompson_normalizers h hnon).2 Q
    (isPGroup_pCoreIn 2 _) hJQ
  have hNJ : normalizer (elementaryAbelianMaxJ Q : Set G) ≤ normalizer (L : Set G) := by
    rw [hJ.1]
    exact (D.sourceOrbit_nonFF_thompson_normalizers h hnon).1
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hS,hbase,hcore,hgen,hctl,?_⟩
  intro H hBH hHC K hK
  have hQH : Q ≤ H := by
    rw [←hQ]
    exact (inf_le_inf_left _ (centralizer_le hUW)).trans (le_sup_right.trans hBH)
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW
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
  have hi := component_normalizer_index H K Q hSQ.stronglyQuasithin hK hQH
  constructor
  · rintro ⟨n,hn,hm⟩
    obtain ⟨_,hdegree,_,⟨P,hPQ,hout⟩,_⟩ := hcomp H hBH hHC K hK
      (Or.inl (ClassificationModels.IsBenderModel.linear n hn hm))
    exact hout ((linearTwo_normalizer_thompson H K Q hK hQH
      (isPGroup_pCoreIn 2 _) hi P hPQ (hdegree n hn hm) hm).trans hNJ)
  · rintro ⟨m,hm,he⟩
    obtain ⟨_,_,hparameter,⟨P,hPQ,hout⟩,_⟩ := hcomp H hBH hHC K hK
      (Or.inl (ClassificationModels.IsBenderModel.suzuki m hm he))
    exact hout ((suzuki_normalizer_thompson H K Q hK hQH
      (isPGroup_pCoreIn 2 _) hi P hPQ (hparameter m hm he) he).trans hNJ)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

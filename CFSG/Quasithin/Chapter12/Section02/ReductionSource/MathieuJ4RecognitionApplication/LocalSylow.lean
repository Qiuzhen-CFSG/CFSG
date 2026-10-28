module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.LocalSylow

/-!
# The original Mathieu application of the source line core and Sylow subgroup

The original marked M24 data and full cubic quotient supply the constructed
three-space Z. Its normalizer has literal two-core R and the relative factor
quotients required for the line group. An ambient Sylow subgroup lies in both
C_G(z) and N_G(Z), contains the original extraspecial core and R, and maps to
a Sylow subgroup under the original Aut(Z) times S5 marking.

This supplies the line-core and compatible Sylow portion of the earlier
algebra required by `SourceIncidence.LocalData`. The construction of its
E=J(T), Todd subgroup, overlaps, and section 8 comparison remains separate.
No additional premise is imposed on the original Mathieu inputs.

Source: Aschbacher--Segev, *The uniqueness of groups of type J4*, Invent.
Math. 105 (1991), (4.4)--(4.7), pp.597--598, DOI 10.1007/BF01232280;
original Aschbacher--Smith 8.2.12--14 application.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal line two-core and relative factor quotients. -/
theorem sourceOrbit_m24_three_space_line_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G))))) :
    ∃ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (d : ThreeSpaceData (z : G) cubic X),
      let N := normalizer (d.space : Set G)
      d.R = N.pCoreIn 2 ∧
      Nat.card (pCore 2 N) = 2^15 ∧
      commutator (pCore 2 N) = center (pCore 2 N) ∧
      frattini (pCore 2 N) = center (pCore 2 N) ∧
      IsElementaryAbelian 2 (center (pCore 2 N)) ∧
      Nat.card (center (pCore 2 N)) = 8 ∧
      d.K.subgroupOf N ⊓ d.S.subgroupOf N = pCore 2 N ∧
      (∀ n : N, ∃ k : d.K.subgroupOf N, ∃ s : d.S.subgroupOf N,
        (k : N) * (s : N) = n) ∧
      Nonempty (((d.K.subgroupOf N) ⧸ (pCore 2 N).subgroupOf (d.K.subgroupOf N)) ≃*
        Matrix.PSL3Two.PSL) ∧
      Nonempty (((d.S.subgroupOf N) ⧸ (pCore 2 N).subgroupOf (d.S.subgroupOf N)) ≃*
        Equiv.Perm (Fin 5)) := by
  let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,⟨d⟩⟩ := source_three_space_data_exists ht
  exact ⟨cubic,X,d,d.R_eq_normalizer_twoCore ht,d.normalizer_core_card ht,
    d.normalizer_core_derived_eq_center ht,d.normalizer_core_frattini_eq_center ht,
    d.normalizer_core_center_elementary ht,d.normalizer_core_center_card ht,
    d.normalizer_factors_inf ht,d.normalizer_factors_product ht,
    d.normalizer_K_quotient_PSL ht,⟨d.normalizerSQuotientEquiv ht⟩⟩

/-- A full ambient Sylow subgroup in the original plane-line intersection. -/
theorem sourceOrbit_m24_three_space_line_sylow
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G))))) :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∃ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (d : ThreeSpaceData (z : G) cubic X),
      ∃ (U : Sylow 2 G) (W : Sylow 2 (MulAut d.space × Equiv.Perm (Fin 5))),
        (U : Subgroup G) ≤ centralizer ({(z : G)} : Set G) ⊓ normalizer (d.space : Set G) ∧
        Recognition.JankoFour.ambientCore (z : G) ≤ (U : Subgroup G) ∧
        d.R ≤ (U : Subgroup G) ∧ d.space ≤ (U : Subgroup G) ∧
        Nat.card U = 2^21 ∧
        (center (U : Subgroup G)).map (U : Subgroup G).subtype = zpowers (z : G) ∧
        ((U : Subgroup G).subgroupOf (normalizer (d.space : Set G))).map
          (d.normalizerProjection ht) = (W : Subgroup (MulAut d.space × Equiv.Perm (Fin 5))) ∧
        (W : Subgroup (MulAut d.space × Equiv.Perm (Fin 5))) =
          ((W : Subgroup (MulAut d.space × Equiv.Perm (Fin 5))).map (MonoidHom.fst _ _)).prod
          ((W : Subgroup (MulAut d.space × Equiv.Perm (Fin 5))).map (MonoidHom.snd _ _)) := by
  let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,⟨d⟩⟩ := source_three_space_data_exists ht
  obtain ⟨U,hU,hQ,hR,hZ,hcard,hcenter⟩ := d.exists_common_sylow_structure ht
  let hUN := hU.trans inf_le_right
  exact ⟨cubic,X,d,U,d.markedSylow ht U hUN,hU,hQ,hR,hZ,hcard,hcenter,
    (d.markedSylow_image ht U hUN).symm,d.markedSylow_eq_prod ht U hUN⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
end

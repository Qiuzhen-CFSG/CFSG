module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Tensor

/-!
# The five-actor consequence for the original cocode pair

An order-five subgroup X of the original H which normalizes I and
centralizes I's image in H/O2(H) centralizes I itself. First X fixes the
original three-space U. The component commutator bound and quotient
centralization put [RI,X] in O2(RI). The proved joint commutant bound
therefore gives [P,X] <= U, exactly the layer premise in the unitary
exclusion. Two coprime-layer applications then give [I,X]=1.

All quotients and inclusions belong to the same chosen pair; I is not
assumed normal in H. The final owner qt-d-1222-nonff-mathieu retains
construction and placement of the unitary five-torus, the later normalizer
contradiction, T-normalization and ambient J4 recognition.
Source: Aschbacher--Smith, 8.2.9, cocode paragraph, printed p.720,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped IsMulCommutative commutatorElement
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

open Chapter8.Section02.Normalizer.ParabolicReduction

/-- The actual order-five actor in the source H quotient centralizes I.
The twelve-dimensional layer premise is discharged from the same cocode pair. -/
theorem sourceOrbit_m24_pair_five_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S)
    (hUZ : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hHU : H ≤ normalizer ((D.sourceOrbit ⊓ centralizer
      (offenderNormalizer D.sourceOrbit g : Set G) : Subgroup G) : Set G))
    (X : Subgroup G) (hXH : X ≤ H) (hX : Nat.card X = 5)
    (hXI : X ≤ normalizer (I : Set G))
    (hXC : (X.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≤
      centralizer ((I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H))) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    ⁅I.pCoreIn 2,X⁆ ≤ U ∧ X ≤ centralizer (I : Set G) := by
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
  let R := localResidual L U
  let Y := R ⊔ I
  let P := I.pCoreIn 2
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (p := 2)
    (show U ≤ D.sourceOrbit from inf_le_left)
  obtain ⟨_,_,_,_,_,_,_,_,hu,_⟩ :=
    D.sourceOrbit_m24_cocode_geometry_of_many h hmany hV hq hnon a E hE hg
  have hU : Nat.card U = 8 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
    change rank U = 3 at hu
    rw [rank,hn,Nat.log_pow Nat.one_lt_two] at hu
    rw [hn,hu]
    rfl
  have hXU := UnitaryExclusion.five_centralizes_eight X U hX hU (hXH.trans hHU)
  have hIX : ⁅I,X⁆ ≤ P :=
    MathieuPair.relative_pair_commutator H I X s.family.le_ambient hXH hXI hXC
  obtain ⟨_,_,_,_,_,hc,_⟩ :=
    D.sourceOrbit_m24_fixedPlane_component_recognition h hmany hV hq hnon a E hE hg hAT
  have hRX : ⁅R,X⁆ ≤ R.pCoreIn 2 := (commutator_mono le_rfl hXU).trans hc
  obtain ⟨hYP,hYU,hUP,hker,hcore,_,_,_,_⟩ :=
    D.sourceOrbit_m24_pair_joint_section h hmany hV hq hnon a E hE hg hAT s hUZ
  let := hUP
  have hfive := D.sourceOrbit_m24_pair_joint_no_five
    h hmany hV hq hnon a E hE hg hAT s hUZ hYP hYU
  have hYPc : Y ≤ normalizer (Y.pCoreIn 2 : Set G) :=
    Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hYX : ⁅Y,X⁆ ≤ Y.pCoreIn 2 :=
    commutator_sup_le_of_relative_normal Y R I X (Y.pCoreIn 2) hYPc le_sup_left le_sup_right
      (hRX.trans (hcore.symm ▸ le_sup_right)) (hIX.trans (hcore.symm ▸ le_sup_left))
  have hXP : X ≤ normalizer (P : Set G) :=
    hXI.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hPX : ⁅P,X⁆ ≤ U := MathieuPair.section_five_layer Y X P U hYP hYU hXP
    (hXH.trans hHU) hX hker hYX hfive
  have hcop : Nat.Coprime 2 (Nat.card X) := by rw [hX]; decide
  have hXPfix := le_centralizer_of_fixed_coprime_prime_layer X P U
    (IsElementaryAbelian.isPGroup 2 U) hcop hXU hPX
  exact ⟨hPX,le_centralizer_of_fixed_coprime_prime_layer X I P
    (isPGroup_pCoreIn 2 I) hcop hXPfix hIX⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

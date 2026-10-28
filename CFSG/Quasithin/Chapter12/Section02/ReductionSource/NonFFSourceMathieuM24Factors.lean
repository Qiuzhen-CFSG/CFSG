module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Commutator
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetFactors
public import Theory.Representation.BinaryConjugationSection.InvariantImages
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers

/-!
# The original M24 cocode residual sections

Restricting the original cocode marking to V_z and quotienting by the original
central involution line constructs the actual six-dimensional dual-hexacode
section. The quotient V/V_z is marked by the four-dimensional natural
permutation quotient on the six tetrads of the same sextet. Both actions are
irreducible for the original L_z, and the kernel of the middle action is exactly
O₂(L_z). Thus its faithful actor retains the full nonsplit 3.A₆, including its
cubic center.

These are the original module-factor assertions in source 8.2.11. The companion
NonFFSourceMathieuM24Closure applies middle irreducibility to the literal
normal closure in C_G(z). The earlier whole-cocode marking remains explicit;
its construction, the remaining centralizer geometry, other Mathieu branches
and ambient J4 recognition stay with qt-d-1222-nonff-mathieu.
Source: Aschbacher–Smith H.15.3 and 8.2.11–12, printed pp.400,722,
refs/quasithin.pdf. The imported native model retains its ATLAS attribution.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.SextetLayers.CoordinateTransport
open CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Stellmacher
open Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The literal original sections V_z/⟨z⟩ and V/V_z carry the native
six-dimensional and four-dimensional residual actions. Both are irreducible;
the kernel of the middle action is exactly the original O₂(L_z). -/
theorem sourceOrbit_m24_centralizer_factors
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ (S : Sextet) (r : localResidual L z →* sextetStabilizer S),
      E (Additive.ofMul z) = sextetVector S ∧
      r.range = solvableResidual (sextetStabilizer S) ∧
      Nonempty (BinaryConjugationSection (localResidual L z)
        (commutatorSpace L D.sourceOrbit z) (zpowers (z : G))
        (MathieuSextet.middleAction S r)) ∧
      Nonempty (BinaryConjugationSection (localResidual L z)
        D.sourceOrbit (commutatorSpace L D.sourceOrbit z)
        (MathieuSextet.topAction S r)) ∧
      IsIrreducible (MathieuSextet.middleAction S r) ∧
      IsIrreducible (MathieuSextet.topAction S r) ∧
      (MathieuSextet.middleAction S r).ker = pCore 2 (localResidual L z) := by
  obtain ⟨S,r,hS,hr,hker,hcore,hrval⟩ :=
    D.sourceOrbit_m24_centralizer_core_action h hmany hV hq hnon a E hE z hz hne
  obtain ⟨S',hS',hpair,hline⟩ :=
    D.sourceOrbit_m24_centralizer_commutator_marking h hmany hV hq hnon a E hE z hz hne
  have hSS : S' = S := sextetVector_injective (hS'.symm.trans hS)
  have hpairS (w : D.sourceOrbit) : (w : G) ∈ commutatorSpace L D.sourceOrbit z ↔
      E (Additive.ofMul w) ∈ sextetPairSpace S := by
    rw [←hSS]
    exact hpair w
  have hlineS (w : D.sourceOrbit) :
      (w : G) ∈ ⁅commutatorSpace L D.sourceOrbit z,localTwoCore L z⁆ ↔
        E (Additive.ofMul w) ∈ sextetTetradLine S := by
    rw [←hSS]
    exact hline w
  clear hpair hline hS' hSS S'
  obtain ⟨_,hWR,hWQ⟩ := D.sourceOrbit_m24_le_centralizer_residual h hmany hV hq hnon a E hE z hz hne
  obtain ⟨_,_,hcomm,hZU,_⟩ :=
    D.sourceOrbit_m24_centralizer_commutator_series h hmany hV hq hnon a E hE z hz hne
  have hRU := (show localResidual L z ≤ localResidual L z ⊔ (T : Subgroup G) from le_sup_left).trans
    (D.sourceOrbit_m24_centralizer_series_normalized h hmany hV hq hnon a E hE z hz hne).2
  have hRL := (localResidual_le L (z : G)).trans inf_le_left
  have hRW := hRL.trans D.sourceOrbit_component_normalizes
  have hUW := commutatorSpace_le L D.sourceOrbit (z : G) D.sourceOrbit_component_normalizes
  have hF (x : localResidual L z) (w : D.sourceOrbit) :
      E (Additive.ofMul (D.sourceOrbit.normalizerMonoidHom ⟨x,hRW x.property⟩ w)) =
        cocodeRepresentation (r x).val (E (Additive.ofMul w)) := by
    rw [hrval]
    exact hE (D.mathieuComponentAutomizer ⟨x,hRL x.property⟩) (Additive.ofMul w)
  have hZ (w : D.sourceOrbit) : (w : G) ∈ zpowers (z : G) ↔
      E (Additive.ofMul w) ∈ sextetTetradLine S := by
    rw [←hcomm]
    exact hlineS w
  obtain ⟨dmid,dtop⟩ := MathieuSextet.marked_factor_sections S
    (localResidual L z) D.sourceOrbit (commutatorSpace L D.sourceOrbit z) (zpowers (z : G))
    hWR hRW hUW hZU.le hRU r E hF hpairS hZ
  refine ⟨S,r,hS,hr,dmid,dtop,MathieuSextet.middle_residual_irreducible S r hr,
    MathieuSextet.top_residual_irreducible S r hr,?_⟩
  rw [MathieuSextet.middleAction_kernel,←hcore]
  apply comap_map_eq_self
  rw [hker]
  intro x hx
  obtain ⟨y,hy,hyx⟩ := hWQ hx
  exact (show y = x from Subtype.ext hyx) ▸ hy

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

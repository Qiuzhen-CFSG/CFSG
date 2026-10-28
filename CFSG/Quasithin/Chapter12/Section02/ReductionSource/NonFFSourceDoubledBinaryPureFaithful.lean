module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureFaithful
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPureIntersection

/-!
# Faithful rank-four action on the actual pure-line component

For the same offender line and minimal H1 component, the marked
singular-free fixed subgroup has order at most four. The actual E.6.11
moving-element theorem proves this bound; no normal-seven hypothesis is
added. The plane-residual kernel is normalized, disjoint from the line,
and too small to admit its nontrivial cubic action, hence it is trivial.

The original inner action therefore gives an injective homomorphism from
[W,O²(C_L(U))], of order sixteen, into the same K/Z(K). Its literal
normalizer action equation and two-rank at least four are retained,
along with the actual offender, both axes, the selected pure line,
minimal H, original Sylow placement and all previous intersection facts.
The hypothesis w ≤ 1 is still explicit. The subsequent H1 Sylow-center,
root and Cartan exclusion, the bound on w and the other doubled rows are
not asserted here.

Source: Aschbacher–Smith, the H1 component argument in 7.7.3,
printed pp.705–706, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open DoubledBinaryLocalCore DoubledBinaryPureFaithful DoubledBinaryInnerAction
open DoubledBinaryPlanes DoubledBinaryIntersection BinaryLinearThree
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- At the original pure line, the selected component fixes at most four
points of the orbit and the adapted plane movement acts faithfully on it. -/
theorem sourceOrbit_binary_pureLine_component_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G))
    (Z : Subgroup G) (hZ : Nat.card Z = 2)
    (hpure : Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom)
    (S : Sylow 2 (centralizer (Z : Set G)))
    (hS : (S : Subgroup _).map (centralizer (Z : Set G)).subtype =
      (T : Subgroup G) ⊓ centralizer (Z : Set G))
    (H : Subgroup G) (hBH : localBase L (T : Subgroup G) Z ≤ H)
    (hHC : H ≤ centralizer (Z : Set G)) (K : Subgroup G) (hK : IsComponentIn K H)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space)
    (hV : ∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V)
    (hVt : ∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom)
    (hmark : DoubledBinaryOmega.HasMarking D.sourceOrbit L E)
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1)
    (hZU : Z ≤ ambientPlane D.sourceOrbit E v f) :
    Nat.card (D.sourceOrbit ⊓ centralizer (K : Set G) : Subgroup G) ≤ 4 ∧
      ⁅D.sourceOrbit,localResidual L (ambientPlane D.sourceOrbit E v f)⁆ ⊓
        centralizer (K : Set G) = ⊥ := by
  obtain ⟨hLN,q,hq,a,hE,ha,hcov⟩ := hmark
  have hno := D.sourceOrbit_binary_pureLine_component_no_twoCentral_fixed
    h hd F hF hmodel hnon t ht hnt Z hZ hpure S hS H hBH hHC K hK
  have hsing (w : Additive D.sourceOrbit) (hw : (w.toMul : G) ∈ centralizer (K : Set G)) :
      ¬ DoubledBinaryComponentGeometry.IsSingular (E w) := by
    intro hs
    have hneq : w ≠ 0 := by
      intro he
      exact hs.1 (by rw [he,map_zero]; rfl)
    exact hno w hneq (DoubledBinaryComponentGeometry.ambient_singular_sylow
      D.sourceOrbit L T D.sourceOrbit_weakClosure_setup.normalizes hLN q hq E hE a hcov w hs) hw
  have hp : (∀ w : Additive D.sourceOrbit, (w.toMul : G) ∈ Z → (E w).2 = 0) ∨
      (∀ w : Additive D.sourceOrbit, (w.toMul : G) ∈ Z → (E w).1 = 0) := by
    rcases hpure with hh | hh
    · exact Or.inl (fun w hw => (hV w).mpr (hh hw))
    · exact Or.inr (fun w hw => (hVt w).mpr (hh hw))
  obtain ⟨hSQ,hMH,hodd⟩ := D.sourceOrbit_binary_pureLine_overgroup_structure
    h hd F hF hmodel hnon t ht hnt Z hZ hpure H hBH hHC
  have hKM : ¬ K ≤ normalizer (L : Set G) := by
    intro hh
    exact not_isComponent_of_twoCore hMH _ (hK.restrict (le_inf hK.1 hh) inf_le_left).2
  have hZne : Z ≠ ⊥ := by intro he; rw [he,card_bot] at hZ; omega
  have hZK : Z ≤ centralizer (K : Set G) := le_centralizer_iff.mpr (hK.1.trans hHC)
  have hsmall := component_fixed_card_le_four D.sourceOrbit Z (normalizer (L : Set G)) K T
    (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd)
    (lt_of_lt_of_le (by decide : (1 : ℕ∞) < 3)
      (D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel))
    E a hcov (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge
    (hZU.trans (ambientPlane_le_orbit D.sourceOrbit E v f)) hZK hZne hp hsing hKM
  exact ⟨hsmall,pairedPlane_component_faithful D.sourceOrbit L Z H K hLN q hq E hE
    v f hfv hZU hZ hZK (le_sup_left.trans hBH) hSQ hK hsmall⟩

/-- The original offender and minimal H1 component carry a faithful inner
rank-four actor, with its literal embedding in the same central quotient. -/
theorem sourceOrbit_binary_exists_pureLine_faithful_component_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit T g ∧
      ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
        let Z := ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆
        let C := centralizer (Z : Set G)
        let B := localBase L (T : Subgroup G) Z
        Nat.card Z = 2 ∧ (Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom) ∧
        Z ≤ D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ∧
        D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ C ∧
        (∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = (T : Subgroup G) ⊓ C) ∧
        pPrimeCore 2 C = ⊥ ∧
        ∃ H : Subgroup G, B ≤ H ∧ H ≤ C ∧ ¬ HasCharacteristicTwo H ∧
          (∀ J : Subgroup G, B ≤ J → J < H → HasCharacteristicTwo J) ∧
          IsSQTK KnownSimple.IsKnownSimple H ∧
          HasCharacteristicTwo (H ⊓ normalizer (L : Set G) : Subgroup G) ∧
          pPrimeCore 2 H = ⊥ ∧ Z ≤ H.pCoreIn 2 ∧
          (∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ C) ∧
          ∃ K : Subgroup G, IsComponentIn K H ∧ ¬ K ≤ normalizer (L : Set G) ∧
            H = K ⊔ B ∧
            Nat.card (D.sourceOrbit ⊓ centralizer (K : Set G) : Subgroup G) ≤ 4 ∧
            ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
              (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
              (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
              DoubledBinaryOmega.HasMarking D.sourceOrbit L E ∧
              (∀ w : Additive D.sourceOrbit, w ≠ 0 →
                (∃ P : Sylow 2 G,
                  (P : Subgroup G) ≤ centralizer ({(w.toMul : G)} : Set G)) →
                (w.toMul : G) ∉ centralizer (K : Set G)) ∧
              (∀ w : Additive D.sourceOrbit, (w.toMul : G) ∈ centralizer (K : Set G) →
                ¬ DoubledBinaryComponentGeometry.IsSingular (E w)) ∧
              ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
                let U := ambientPlane D.sourceOrbit E v f
                let A := ⁅D.sourceOrbit,localResidual L U⁆
                Z ≤ U ∧ Disjoint U A ∧ Nat.card A = 16 ∧
                  A ≤ ⁅D.sourceOrbit,localResidual L Z⁆ ∧
                  Nat.card (Z ⊔ A : Subgroup G) = 32 ∧
                  subgroupCorank D.sourceOrbit (Z ⊔ A) = 1 ∧
                  centralizer ((Z ⊔ A : Subgroup G) : Set G) ≤ normalizer (L : Set G) ∧
                  ¬ A ≤ centralizer (K : Set G) ∧
                  ∃ hAN : A ≤ normalizer (K : Set G),
                    A ⊓ centralizer (K : Set G) = ⊥ ∧
                    (∀ a : A, K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K) ∧
                    (∃ j : A →* K ⧸ center K, Function.Injective j ∧
                      ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                        K.normalizerMonoidHom (inclusion hAN a)) ∧
                    4 ≤ primeRank 2 (K ⧸ center K) := by
  obtain ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,⟨P,hP⟩,hoddC,
    H,hBH,hHC,hNH,hmin,hSQ,hMH,hoddH,hcore,hSyl,K,hK,hKM,hgen,
    E,hV,hVt,hmark,hno,hsing,v,f,hfv,hZU,hdis,hcard,hmove,hhyper,hcorank,hCM,hact,hAN,hi⟩ :=
    D.sourceOrbit_binary_exists_pureLine_component_action h hd F hF hmodel hnon hw
  let Z := ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆
  let U := ambientPlane D.sourceOrbit E v f
  let A := ⁅D.sourceOrbit,localResidual L U⁆
  obtain ⟨hsmall,hker⟩ := D.sourceOrbit_binary_pureLine_component_kernel
    h hd F hF hmodel hnon t ht hnt Z hZ hpure P hP H hBH hHC K hK
    E hV hVt hmark v f hfv hZU
  obtain ⟨j,hj,hjact⟩ := faithful_inner_centralQuotient K A hAN hker hi
  have hAW : A ≤ D.sourceOrbit := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes))
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (inclusion hAW) (inclusion_injective hAW)
  exact ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,⟨P,hP⟩,hoddC,
    H,hBH,hHC,hNH,hmin,hSQ,hMH,hoddH,hcore,hSyl,K,hK,hKM,hgen,hsmall,
    E,hV,hVt,hmark,hno,hsing,v,f,hfv,hZU,hdis,hcard,hmove,hhyper,hcorank,hCM,hact,
    hAN,hker,hi,⟨j,hj,hjact⟩,four_le_rank_centralQuotient K A hcard j hj⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

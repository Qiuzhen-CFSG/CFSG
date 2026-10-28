module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureIntersection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPureOddCore

/-!
# The actual H1 intersections and the rank-four component actor

For the same pure line selected by the original offender, the marked
action factors its local point fixer through the original component. Its
literal centralizer Sylow and Thompson normalizer control then place the
double-centralizer two-core inside L₁T₁. Source 1.1.4(4) proves 7.7.5 for
every L₁T₁ ≤ H ≤ C_G(Z₁). Consequently no two-central involution of W
centralizes an ordinary component K of this H.

Choose a paired plane U through this very line, retaining the original
seed conjugator and both marked axes. Its moved subgroup [W,O²(C_L(U))]
has order sixteen and acts inner on the same K. The original line joined
to this actor has order thirty-two and centralizer in M; since K escapes
M, the actor acts nontrivially on K. The final application combines these
facts on the original minimal H1 witness and excludes every singular
diagonal vector from its component fixed subgroup.

H only centralizes Z₁: no centralization of U is imposed. The rank-four
actor is contained in the full pure-line residual movement, not identified
with it. Faithfulness, the rank-three kernel argument, component exclusion,
w ≤ 1, and the other doubled rows remain with the original task.

Source: Aschbacher–Smith 7.7.5 and the H1 argument in 7.7.3,
printed pp.704–706, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open DoubledBinaryLocalCore DoubledBinaryPureFactors DoubledBinaryPureIntersection
open DoubledBinaryPlanes DoubledBinaryIntersection BinaryLinearThree
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Source 7.7.5 at the selected pure line, with its actual centralizer Sylow. -/
theorem sourceOrbit_binary_pureLine_intersections
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G))
    (Z : Subgroup G) (hZ : Nat.card Z = 2)
    (hpure : Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom)
    (S : Sylow 2 (centralizer (Z : Set G)))
    (hS : (S : Subgroup _).map (centralizer (Z : Set G)).subtype =
      (T : Subgroup G) ⊓ centralizer (Z : Set G)) :
    ∀ H : Subgroup G, localBase L (T : Subgroup G) Z ≤ H →
      H ≤ centralizer (Z : Set G) →
      ∀ w : Additive D.sourceOrbit, w ≠ 0 →
        (∃ P : Sylow 2 G, (P : Subgroup G) ≤ centralizer ({(w.toMul : G)} : Set G)) →
        H ⊓ centralizer ({(w.toMul : G)} : Set G) ∈ Chapter1.He G := by
  let W := D.sourceOrbit
  let Vt := V.map (MulAut.conj t).toMonoidHom
  let M := normalizer (L : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let B := localBase L (T : Subgroup G) Z
  have hVW : V ≤ W := by
    change V ≤ D.sourceOrbit
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  have hVtW : Vt ≤ W := (map_mono hVW).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (D.sourceOrbit_weakClosure_setup.normalizes ht))
  have hZW : Z ≤ W := hpure.elim (fun hh => hh.trans hVW) (fun hh => hh.trans hVtW)
  obtain ⟨t₀,_,_,q,hq,E,a,hE,ha,hinner,hcov,hV,hVt₀⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  let tN : normalizer (W : Set G) := ⟨t,D.sourceOrbit_weakClosure_setup.normalizes ht⟩
  have hother : Vt = V.map (MulAut.conj t₀).toMonoidHom :=
    outer_conjugate_eq W V _ hVW
      (card_map_of_injective (MulAut.conj t₀).injective).symm E a hcov hV hVt₀ tN
      (fun hi => hnt ((hinner tN).mp hi))
  have hVt (w : Additive W) : (E w).1 = 0 ↔ (w.toMul : G) ∈ Vt := by
    rw [hother]
    exact hVt₀ w
  have hZne : Z ≠ ⊥ := by intro he; rw [he,card_bot] at hZ; omega
  have hpres := pureLine_normalizes_factors W V Vt Z hVW hVtW E a hcov hV hVt hZne hpure
  have hbase : B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (Z : Set G) :=
    DoubledBinarySylow.localBase_eq_centralizer L Z T D.sylow_normalizes_component S hS
  have hfactor := factor_of_inner_action W L Z B M hZW D.sourceOrbit_component_normalizes
    (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge q hq a ha
    (fun n hn => (hinner n).mpr (hpres ⟨n.property,hn⟩).1)
    (by rw [hbase]; exact inf_le_inf_right _ (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))
  have hQ : (T : Subgroup G) ⊓ centralizer (W : Set G) = Q := by
    dsimp only [W,Q]
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hJQ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ Q := by
    rw [← hQ]
    exact le_inf (sSup_le fun _ hA => hA.1)
      (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
  have hZB : Z ≤ B := (le_inf (hZW.trans D.sourceOrbit_weakClosure_setup.le_sylow)
    (hZW.trans ((le_centralizer W).trans (centralizer_le hZW)))).trans le_sup_right
  intro H hBH hHC w hw hSyl
  have hcore := doubleCentralizer_core_le_base W Z B M Q T hZW
    D.sylow_normalizes_component (isPGroup_pCoreIn 2 _)
    (hQ.symm.trans_le inf_le_right) hJQ
    (fun R hp hJR => R.le_normalizer.trans
      ((D.sourceOrbit_nonFF_thompson_normalizers h hnon).2 R hp hJR).2)
    S hS le_sup_right hfactor (w.toMul : G) w.toMul.property
  obtain ⟨P,hP⟩ := hSyl
  have hw1 : (w.toMul : G) ≠ 1 := by
    intro he
    exact hw (Additive.toMul.injective (Subtype.ext he))
  have ho : orderOf (w.toMul : G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (w.toMul : G) w.toMul.property) hw1
  have hp : IsPGroup 2 (zpowers (w.toMul : G)) :=
    (IsElementaryAbelian.isPGroup 2 W).to_le (zpowers_le.mpr w.toMul.property)
  have hz : zpowers (w.toMul : G) ≠ ⊥ := by
    intro he
    exact hw1 (mem_bot.mp (he ▸ mem_zpowers (w.toMul : G)))
  have hc : centralizer ({(w.toMul : G)} : Set G) ∈ Chapter1.He G :=
    Chapter1.twoLocal_mem_He_of_sylow_le P (h.simpleQTKE.evenCharacteristic P)
      ⟨zpowers (w.toMul : G),hz,hp,
        (normalizer_zpowers_eq_centralizer_of_order_two (w.toMul : G) ho).symm⟩ hP
  exact intersection_characteristicTwo Z H (w.toMul : G)
    ((IsElementaryAbelian.isPGroup 2 W).to_le hZW) (hZB.trans hBH) hHC
    (hZW.trans ((le_centralizer W).trans
      (centralizer_le (Set.singleton_subset_iff.mpr w.toMul.property)))) hc (hcore.trans hBH)

/-- No two-central involution of the original orbit centralizes the same component. -/
theorem sourceOrbit_binary_pureLine_component_no_twoCentral_fixed
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
    (hHC : H ≤ centralizer (Z : Set G)) (K : Subgroup G) (hK : IsComponentIn K H) :
    ∀ w : Additive D.sourceOrbit, w ≠ 0 →
      (∃ P : Sylow 2 G, (P : Subgroup G) ≤ centralizer ({(w.toMul : G)} : Set G)) →
      (w.toMul : G) ∉ centralizer (K : Set G) := by
  intro w hw hSyl hfix
  have hc := D.sourceOrbit_binary_pureLine_intersections
    h hd F hF hmodel hnon t ht hnt Z hZ hpure S hS H hBH hHC w hw hSyl
  have hKw : K ≤ centralizer ({(w.toMul : G)} : Set G) := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr (hfix k hk)
  exact not_isComponent_of_twoCore (Chapter1.mem_He_iff.mp hc) _
    (hK.restrict (le_inf hK.1 hKw) inf_le_left).2

/-- Construct the rank-four source actor through the same pure line and component.
The actor is inner and nontrivial on K; no faithful-action premise is assumed. -/
theorem sourceOrbit_binary_pureLine_pairedPlane_component_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G))
    (Z : Subgroup G) (hZ : Nat.card Z = 2)
    (hpure : Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom)
    (H : Subgroup G) (hBH : localBase L (T : Subgroup G) Z ≤ H)
    (hHC : H ≤ centralizer (Z : Set G)) (K : Subgroup G) (hK : IsComponentIn K H) :
    ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
      (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
      (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
      DoubledBinaryOmega.HasMarking D.sourceOrbit L E ∧
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
            ∀ a : A, K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K := by
  let W := D.sourceOrbit
  let Vt := V.map (MulAut.conj t).toMonoidHom
  have hVW : V ≤ W := by
    change V ≤ D.sourceOrbit
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  have hVtW : Vt ≤ W := (map_mono hVW).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (D.sourceOrbit_weakClosure_setup.normalizes ht))
  have hZW : Z ≤ W := hpure.elim (fun hh => hh.trans hVW) (fun hh => hh.trans hVtW)
  obtain ⟨t₀,_,_,q,hq,E,a,hE,ha,hinner,hcov,hV,hVt₀⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  let tN : normalizer (W : Set G) := ⟨t,D.sourceOrbit_weakClosure_setup.normalizes ht⟩
  have hother : Vt = V.map (MulAut.conj t₀).toMonoidHom :=
    outer_conjugate_eq W V _ hVW
      (card_map_of_injective (MulAut.conj t₀).injective).symm E a hcov hV hVt₀ tN
      (fun hi => hnt ((hinner tN).mp hi))
  have hVt (w : Additive W) : (E w).1 = 0 ↔ (w.toMul : G) ∈ Vt := by
    rw [hother]
    exact hVt₀ w
  have hp : (∀ w : Additive W, (w.toMul : G) ∈ Z → (E w).2 = 0) ∨
      (∀ w : Additive W, (w.toMul : G) ∈ Z → (E w).1 = 0) := by
    rcases hpure with hh | hh
    · exact Or.inl (fun w hw => (hV w).mpr (hh hw))
    · exact Or.inr (fun w hw => (hVt w).mpr (hh hw))
  obtain ⟨v,f,hfv,hZU⟩ := exists_pairedPlane_over_pureLine W Z E hZW hZ hp
  let U := ambientPlane W E v f
  let A := ⁅W,localResidual L U⁆
  obtain ⟨hSQ,hMH,hodd⟩ := D.sourceOrbit_binary_pureLine_overgroup_structure
    h hd F hF hmodel hnon t ht hnt Z hZ hpure H hBH hHC
  have hWH : W ≤ H := (le_inf D.sourceOrbit_weakClosure_setup.le_sylow
    ((le_centralizer W).trans (centralizer_le hZW))).trans (le_sup_right.trans hBH)
  obtain ⟨hdis,hcard,hmove,hAN,hi⟩ := pairedPlane_component_inner W L Z H K
    D.sourceOrbit_component_normalizes q hq E hE v f hfv hZU hWH (le_sup_left.trans hBH) hSQ hK
  have hAW : A ≤ W := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes))
  have hW : Nat.card W = 64 := by
    change Nat.card (Additive W) = 64
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2)]
    norm_num [NaturalDual.Space,Module.finrank_prod,BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  obtain ⟨hhyper,hcorank⟩ := pureLine_movement_corank W Z U A hZW hZU hAW hZ hcard hW hdis
  have hCM : centralizer ((Z ⊔ A : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
    rw [← D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]
    apply centralizer_le_normalizer_of_corank_lt_globalR (sup_le hZW hAW)
    rw [hcorank]
    exact lt_of_lt_of_le (by decide : (1 : ℕ∞) < 3)
      (D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel)
  have hKM : ¬ K ≤ normalizer (L : Set G) := by
    intro hh
    exact not_isComponent_of_twoCore hMH _ (hK.restrict (le_inf hK.1 hh) inf_le_left).2
  have hnot : ¬ A ≤ centralizer (K : Set G) := by
    intro hh
    apply hKM
    apply le_trans _ hCM
    exact le_centralizer_iff.mp (sup_le (le_centralizer_iff.mpr (hK.1.trans hHC)) hh)
  refine ⟨E,hV,hVt,⟨D.sourceOrbit_component_normalizes,q,hq,a,hE,ha,hcov⟩,
    v,f,hfv,hZU,hdis,hcard,hmove,hhyper,hcorank,hCM,?_,hAN,hi⟩
  exact hnot

/-- The original offender and minimal H1 component carry the actual paired-plane
actor, the source hyperplane, and the two-central fixed-point exclusion together. -/
theorem sourceOrbit_binary_exists_pureLine_component_action
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
                    ∀ a : A, K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K := by
  obtain ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,⟨P,hP⟩,hoddC,
    H,hBH,hHC,hNH,hmin,hSQ,hMH,hoddH,hcore,hSyl,K,hK,hKM,hgen,hnorm,hnot⟩ :=
    D.sourceOrbit_binary_exists_pureLine_minimal_component h hd F hF hmodel hnon hw
  let Z := ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆
  obtain ⟨E,hV,hVt,hmark,v,f,hfv,hZU,hdis,hcard,hmove,hhyper,hcorank,hCM,hact,hAN,hi⟩ :=
    D.sourceOrbit_binary_pureLine_pairedPlane_component_action
      h hd F hF hmodel hnon t ht hnt Z hZ hpure H hBH hHC K hK
  have hno := D.sourceOrbit_binary_pureLine_component_no_twoCentral_fixed
    h hd F hF hmodel hnon t ht hnt Z hZ hpure P hP H hBH hHC K hK
  have hsing (w : Additive D.sourceOrbit) (hw : (w.toMul : G) ∈ centralizer (K : Set G)) :
      ¬ DoubledBinaryComponentGeometry.IsSingular (E w) := by
    intro hs
    obtain ⟨hLN,q,hq,a,hE,ha,hcov⟩ := hmark
    have hneq : w ≠ 0 := by
      intro he
      exact hs.1 (by rw [he,map_zero]; rfl)
    exact hno w hneq (DoubledBinaryComponentGeometry.ambient_singular_sylow
      D.sourceOrbit L T D.sourceOrbit_weakClosure_setup.normalizes hLN q hq E hE a hcov w hs) hw
  exact ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,⟨P,hP⟩,hoddC,
    H,hBH,hHC,hNH,hmin,hSQ,hMH,hoddH,hcore,hSyl,K,hK,hKM,hgen,
    E,hV,hVt,hmark,hno,hsing,v,f,hfv,hZU,hdis,hcard,hmove,hhyper,hcorank,hCM,hact,hAN,hi⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

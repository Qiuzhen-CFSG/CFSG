module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOmega
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryIntersection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryComponentGeometry
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion

/-!
# The source point-centralizer intersection and faithful component action

On one Sylow-placed paired plane U of the original doubled orbit W, the
base B=L₀T₀ has the original core Q. Thompson normalizer control and the
literal paired-plane action put O₂(C_G(U,w)) in B. Source 1.1.4(4) then
makes H ∩ C_G(w) characteristic two for every B ≤ H ≤ C_G(U) and every
two-central nonidentity w in W.

If an ordinary component K of H fixed more than U on W, the singular-point
geometry would put K in a characteristic-two point centralizer inside H,
which excludes components. Thus C_W(K)=U. The residual moving subgroup
[W,L₀] is disjoint from U and has order sixteen. The component orbit bound
makes it normalize K, so its literal action has trivial kernel and induced
automizer of order sixteen. The original seed axes and conjugator are retained.

This proves the paired-plane case of 7.7.5 and the faithfulness paragraph of
7.7.6. Innerness of the component action, component elimination, ambient
C_G(U) ≤ M, the binary endgame, and the other non-FF rows remain with
qt-d-1222-nonff-doubled. The printed 7.7.5 display names F*(C_G(w)), but
its proof and its use in 7.7.6 concern F*(C_H(w))=O₂(C_H(w)).
Source: Aschbacher–Smith, printed pp.704–706, refs/quasithin.pdf.
-/

open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore DoubledBinarySylow
open DoubledBinaryComponentGeometry DoubledBinaryIntersection
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Source 7.7.5 for the actual local-base overgroups and their two-central
points. An ordinary component of any such overgroup fixes exactly the paired
plane on the original doubled orbit. -/
theorem sourceOrbit_binary_pairedPlane_intersections_with_action_with_marking
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
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          Disjoint U ⁅D.sourceOrbit,localResidual L U⁆ ∧
          Nat.card (⁅D.sourceOrbit,localResidual L U⁆ : Subgroup G) = 16 ∧
          Nonempty (inducedAutomizer D.sourceOrbit (centralizer (U : Set G)) ≃*
            Equiv.Perm (Fin 3)) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ w : Additive D.sourceOrbit, w ≠ 0 →
              (∃ S : Sylow 2 G,
                (S : Subgroup G) ≤ centralizer ({(w.toMul : G)} : Set G)) →
              H ⊓ centralizer ({(w.toMul : G)} : Set G) ∈ Chapter1.He G) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              D.sourceOrbit ⊓ centralizer (K : Set G) = U ∧
                ⁅D.sourceOrbit,localResidual L U⁆ ≤ normalizer (K : Set G) ∧
                ⁅D.sourceOrbit,localResidual L U⁆ ⊓ centralizer (K : Set G) = ⊥ ∧
                Nat.card (inducedAutomizer K ⁅D.sourceOrbit,localResidual L U⁆) = 16) := by
  obtain ⟨t,ht,hnt,q,hq,E,a,hE,ha,_,hcov,hV,hVt⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  have hmark : DoubledBinaryOmega.HasMarking D.sourceOrbit L E :=
    ⟨D.sourceOrbit_component_normalizes,q,hq,a,hE,ha,hcov⟩
  let M := normalizer (L : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
  have hMW : M ≤ normalizer (D.sourceOrbit : Set G) :=
    (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge
  have hJ := D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon
  have hcontrol := D.sourceOrbit_nonFF_thompson_normalizers h hnon
  obtain ⟨v,f,hfv,S,hS⟩ := exists_pairedPlane_sylow D.sourceOrbit M T hTM hMW hJ hcontrol.1 E a hcov
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  have hQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hcore : B.pCoreIn 2 = Q := pairedPlane_localBase_core D.sourceOrbit L T
    D.sylow_normalizes_component D.sourceOrbit_component_normalizes
    D.sourceOrbit_weakClosure_setup.normalizes hQ q hq E hE a ha hcov v f hfv
  have hbase : B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) :=
    localBase_eq_centralizer L U T D.sylow_normalizes_component S hS
  have hUW : U ≤ D.sourceOrbit := ambientPlane_le_orbit D.sourceOrbit E v f
  have hWQ : D.sourceOrbit ≤ Q := (D.sourceOrbit_core_normalizer h).1
  have hQB : Q ≤ B := hcore ▸ pCoreIn_le 2 B
  have hUB : U ≤ B := hUW.trans (hWQ.trans hQB)
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q := by
    rw [← hQ]
    exact le_inf (sSup_le fun _ hA => hA.1) hJ
  have hfactor := pairedPlane_factor D.sourceOrbit L B M
    D.sourceOrbit_component_normalizes hMW q hq E a ha hcov v f hfv
    (by rw [hbase]; exact inf_le_inf_right _ (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))
  have hdouble (w : Additive D.sourceOrbit) :
      (centralizer (U : Set G) ⊓ centralizer ({(w.toMul : G)} : Set G)).pCoreIn 2 ≤ B :=
    doubleCentralizer_core_le_base D.sourceOrbit U B M Q T hUW hTM
      (isPGroup_pCoreIn 2 _) (hQ.symm.trans_le inf_le_right) hJQ
      (fun R hp hJR => R.le_normalizer.trans (hcontrol.2 R hp hJR).2)
      S hS le_sup_right hfactor w.toMul w.toMul.property
  have hinter (H : Subgroup G) (hBH : B ≤ H) (hHC : H ≤ centralizer (U : Set G))
      (w : Additive D.sourceOrbit) (hw : w ≠ 0)
      (hs : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({(w.toMul : G)} : Set G)) :
      H ⊓ centralizer ({(w.toMul : G)} : Set G) ∈ Chapter1.He G := by
    obtain ⟨P,hP⟩ := hs
    have hw1 : (w.toMul : G) ≠ 1 := by
      intro he
      exact hw (Additive.toMul.injective (Subtype.ext he))
    have ho : orderOf (w.toMul : G) = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (w.toMul : G) w.toMul.property) hw1
    have hp : IsPGroup 2 (zpowers (w.toMul : G)) :=
      (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le (zpowers_le.mpr w.toMul.property)
    have hz : zpowers (w.toMul : G) ≠ ⊥ := by
      intro he
      exact hw1 (mem_bot.mp (he ▸ mem_zpowers (w.toMul : G)))
    have hc : centralizer ({(w.toMul : G)} : Set G) ∈ Chapter1.He G :=
      Chapter1.twoLocal_mem_He_of_sylow_le P (h.simpleQTKE.evenCharacteristic P)
        ⟨zpowers (w.toMul : G),hz,hp,
          (normalizer_zpowers_eq_centralizer_of_order_two (w.toMul : G) ho).symm⟩ hP
    apply intersection_characteristicTwo U H (w.toMul : G)
      ((IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW) (hUB.trans hBH) hHC
      (hUW.trans ((le_centralizer D.sourceOrbit).trans
        (centralizer_le (Set.singleton_subset_iff.mpr w.toMul.property)))) hc
    exact (hdouble w).trans hBH
  have hgen := DoubledBinaryOddCore.pairedPlane_residual_supplement D.sourceOrbit L
    D.sourceOrbit_component_normalizes q hq E hE v f hfv
  have hdis := pairedPlane_residual_disjoint D.sourceOrbit L
    D.sourceOrbit_component_normalizes q E hE v f hfv
  have hcard := pairedPlane_residual_card D.sourceOrbit L
    D.sourceOrbit_component_normalizes q E hE v f hfv hgen
  have hAW : ⁅D.sourceOrbit,localResidual L U⁆ ≤ D.sourceOrbit :=
    le_normalizer_iff_commutator_le_left.mp
      ((map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes))
  have hfixed (H : Subgroup G) (hBH : B ≤ H) (hHC : H ≤ centralizer (U : Set G))
      (K : Subgroup G) (hK : IsComponentIn K H) :
      D.sourceOrbit ⊓ centralizer (K : Set G) = U := by
    have hUK : U ≤ D.sourceOrbit ⊓ centralizer (K : Set G) :=
      le_inf hUW (le_centralizer_iff.mp (hK.1.trans hHC))
    apply le_antisymm _ hUK
    by_contra hn
    have hlt := lt_of_le_not_ge hUK hn
    obtain ⟨w,hwK,hwv,hwf,hwp⟩ := ambientPlane_lt_singular D.sourceOrbit E v f hfv
      (centralizer (K : Set G)) hlt
    have hw : w ≠ 0 := by
      intro he
      exact hwv (by rw [he,map_zero]; rfl)
    have hs := ambient_singular_sylow D.sourceOrbit L T
      D.sourceOrbit_weakClosure_setup.normalizes D.sourceOrbit_component_normalizes
      q hq E hE a hcov w ⟨hwv,hwf,hwp⟩
    have hc := hinter H hBH hHC w hw hs
    have hKw : K ≤ centralizer ({(w.toMul : G)} : Set G) := by
      intro k hk
      exact mem_centralizer_singleton_iff.mpr (hwK k hk)
    exact not_isComponent_of_twoCore (Chapter1.mem_He_iff.mp hc) _
      (hK.restrict (le_inf hK.1 hKw) inf_le_left).2

  have hquot := DoubledBinaryPlaneQuotient.ambientPlane_equiv D.sourceOrbit L
    D.sourceOrbit_component_normalizes q hq E hE a ha hcov v f hfv
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,⟨S,hS⟩,hbase,hcore,hdis,hcard,hquot,hinter,?_⟩
  intro H hBH hHC K hK
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW
  have hU : U ≠ ⊥ := by
    intro hz
    have hu := DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv
    change Nat.card U = 4 at hu
    rw [hz,Subgroup.card_bot] at hu
    omega
  have hHN : H ≤ normalizer (U : Set G) := hHC.trans (Subgroup.centralizer_le_normalizer _)
  have hs := (h.simpleQTKE.twoLocal_sqtk (show IsTwoLocal (normalizer (U : Set G)) from
    ⟨U,hU,hp,rfl⟩)).subgroup (H.subgroupOf (normalizer (U : Set G)))
  have hSQ : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp hs
  have hAN := residual_movement_normalizes_component H D.sourceOrbit (localResidual L U) K
    hSQ.stronglyQuasithin hK (hWQ.trans (hQB.trans hBH)) (le_sup_left.trans hBH)
    (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G)))
  have hker : ⁅D.sourceOrbit,localResidual L U⁆ ⊓ centralizer (K : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxU : x ∈ U := hfixed H hBH hHC K hK ▸ ⟨hAW hx.1,hx.2⟩
    exact hdis.le_bot ⟨hxU,hx.1⟩
  exact ⟨hfixed H hBH hHC K hK,hAN,hker,
    (faithful_inducedAutomizer_card K _ hAN hker).trans hcard⟩

/-- Original interface, retaining all mathematical conclusions. -/
theorem sourceOrbit_binary_pairedPlane_intersections_with_action
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
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          Disjoint U ⁅D.sourceOrbit,localResidual L U⁆ ∧
          Nat.card (⁅D.sourceOrbit,localResidual L U⁆ : Subgroup G) = 16 ∧
          Nonempty (inducedAutomizer D.sourceOrbit (centralizer (U : Set G)) ≃*
            Equiv.Perm (Fin 3)) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ w : Additive D.sourceOrbit, w ≠ 0 →
              (∃ S : Sylow 2 G,
                (S : Subgroup G) ≤ centralizer ({(w.toMul : G)} : Set G)) →
              H ⊓ centralizer ({(w.toMul : G)} : Set G) ∈ Chapter1.He G) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              D.sourceOrbit ⊓ centralizer (K : Set G) = U ∧
                ⁅D.sourceOrbit,localResidual L U⁆ ≤ normalizer (K : Set G) ∧
                ⁅D.sourceOrbit,localResidual L U⁆ ⊓ centralizer (K : Set G) = ⊥ ∧
                Nat.card (inducedAutomizer K ⁅D.sourceOrbit,localResidual L U⁆) = 16) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,_,hrest⟩ :=
    D.sourceOrbit_binary_pairedPlane_intersections_with_action_with_marking h hd hnon F hF hmodel
  exact ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hrest⟩


/-- The original intersection interface, retaining its public statement. The
richer theorem also supplies the literal paired-plane action on this same plane. -/
theorem sourceOrbit_binary_pairedPlane_intersections
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
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          Disjoint U ⁅D.sourceOrbit,localResidual L U⁆ ∧
          Nat.card (⁅D.sourceOrbit,localResidual L U⁆ : Subgroup G) = 16 ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ w : Additive D.sourceOrbit, w ≠ 0 →
              (∃ S : Sylow 2 G,
                (S : Subgroup G) ≤ centralizer ({(w.toMul : G)} : Set G)) →
              H ⊓ centralizer ({(w.toMul : G)} : Set G) ∈ Chapter1.He G) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              D.sourceOrbit ⊓ centralizer (K : Set G) = U ∧
                ⁅D.sourceOrbit,localResidual L U⁆ ≤ normalizer (K : Set G) ∧
                ⁅D.sourceOrbit,localResidual L U⁆ ⊓ centralizer (K : Set G) = ⊥ ∧
                Nat.card (inducedAutomizer K ⁅D.sourceOrbit,localResidual L U⁆) = 16) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hS,hbase,hcore,hdis,hcard,_,hinter,hcomp⟩ :=
    D.sourceOrbit_binary_pairedPlane_intersections_with_action h hd hnon F hF hmodel
  exact ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hS,hbase,hcore,hdis,hcard,hinter,hcomp⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

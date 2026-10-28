module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureUnitary
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryUnitaryExclusion
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureCartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPurePlacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPointCentralizers
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction.Transport

/-!
# Pure-line Cartan reduction on the original binary doubled orbit

Both original marked axes have point-centralizer action of order dividing
24; the second is transported by the actual conjugator. The original
component Sylow lies in C_T(W), so its normalizer has odd image on W,
of order dividing three. This contradicts its large marked Cartan action
whenever model theory places that normalizer in M.

The existing Thompson and core-normalizer results therefore eliminate
linear-two, Suzuki, linear-three, symplectic-four, and Ree-F4 components.
For unitary-three, its fixed-field torus gives the corresponding direct
contradiction without a whole-Borel normalization assumption. The same
component, Sylow, inner sixteen, quotient map, and both axes survive the
reduction to actual G₂ and triality models.

The hypothesis w ≤ 1 remains explicit. The two exceptional component
exclusions and the final non-FF doubled contradiction remain open.
Source: Aschbacher–Smith 7.7.3 H1 argument, printed pp.705–706,
and 7.7.4, printed p.704, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE BinaryLinearThree
open Stellmacher DoubledBinaryLocalCore DoubledBinaryPlanes
open DoubledBinaryBenderExclusion DoubledBinaryClassicalExclusion
open DoubledBinaryRootCentralization DoubledBinaryReePlacement
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
private theorem induced_inter_normalizer (W A : Subgroup G) :
    inducedAutomizer W (normalizer (W : Set G) ⊓ A) = inducedAutomizer W A := by
  unfold inducedAutomizer
  congr 1
  ext n
  exact and_iff_right n.property

/-- The pure-line image has order dividing 24 on either original marked axis.
Conjugation transports the second axis without identifying it with the seed. -/
theorem sourceOrbit_binary_pureLine_image_card_dvd
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (t : G) (ht : t ∈ (T : Subgroup G)) (Z : Subgroup G)
    (hZ : Z ≠ ⊥) (hpure : Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom) :
    Nat.card (inducedAutomizer D.sourceOrbit (centralizer (Z : Set G))) ∣ 24 := by
  obtain ⟨z,hz,hzne⟩ := Z.bot_or_exists_ne_one.resolve_left hZ
  have point (x : G) (hx : x ∈ V) (hxne : x ≠ 1) :
      Nat.card (inducedAutomizer D.sourceOrbit (centralizer ({x} : Set G))) = 24 := by
    obtain ⟨e⟩ := (D.sourceOrbit_binary_point_centralizer h hd F hF hmodel x hx hxne).1
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    rfl
  rcases hpure with hZV | hZVt
  · have hc : centralizer (Z : Set G) ≤ centralizer ({z} : Set G) :=
      centralizer_le (Set.singleton_subset_iff.mpr hz)
    exact (point z (hZV hz) hzne) ▸ card_dvd_of_le (map_mono (comap_mono hc))
  · obtain ⟨y,hy,hyt⟩ := hZVt hz
    let e := MulAut.conj t
    have hty : e y = z := hyt
    have hyne : y ≠ 1 := by intro he; exact hzne (by rw [←hty,he,map_one])
    let W := D.sourceOrbit
    let B := normalizer (W : Set G) ⊓ centralizer (Z : Set G)
    have htW : t ∈ normalizer (W : Set G) :=
      (D.sourceOrbit_weakClosure_setup.normalizes) ht
    have hW : W.map e.symm.toMonoidHom = W := by
      rw [map_equiv_eq_comap_symm']
      ext x
      change e x ∈ W ↔ x ∈ W
      exact (mem_normalizer_iff.mp htW x).symm
    obtain ⟨a⟩ := Section06.Components.LieSieve.RankOne.UnitaryAction.exists_actionMapEquiv
      W B inf_le_left e.symm.toMonoidHom e.symm.injective
    have hc : B.map e.symm.toMonoidHom ≤ centralizer ({y} : Set G) := by
      rintro _ ⟨b,hb,rfl⟩ x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      have hh := congrArg e.symm (hb.2 z hz)
      simpa only [map_mul,←hty,e.symm_apply_apply,MulEquiv.coe_toMonoidHom] using hh
    have hi : Nat.card (inducedAutomizer W (B.map e.symm.toMonoidHom)) ∣
        Nat.card (inducedAutomizer W (centralizer ({y} : Set G))) :=
      card_dvd_of_le (map_mono (comap_mono hc))
    have ha := Nat.card_congr a.toEquiv
    rw [hW] at ha
    rw [←ha] at hi
    change Nat.card (inducedAutomizer W (normalizer (W : Set G) ⊓ centralizer (Z : Set G))) ∣ _ at hi
    rw [induced_inter_normalizer] at hi
    exact (point y hy hyne) ▸ hi

/-- The original H1 witness has an escaping Sylow normalizer and an actual
G₂ or triality component quotient. All other surviving Lie rows are excluded
on this same component, with no new local exclusion premise. -/
theorem sourceOrbit_binary_exists_pureLine_component_cartan_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit T g ∧
      ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
        let Z := ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆
        let C := centralizer (Z : Set G)
        let B := localBase L (T : Subgroup G) Z
        let Q₀ := (L ⊔ (T : Subgroup G)).pCoreIn 2
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
                  ((T : Subgroup G) ⊓ C) ≤ normalizer ((Z ⊔ A : Subgroup G) : Set G) ∧
                  (∃ N : Subgroup ((T : Subgroup G) ⊓ C : Subgroup G), N.index ≤ 2 ∧
                    ⁅N.map ((T : Subgroup G) ⊓ C).subtype,Z ⊔ A⁆ ≤ Z) ∧
                  subgroupCorank D.sourceOrbit (Z ⊔ A) = 1 ∧
                  centralizer ((Z ⊔ A : Subgroup G) : Set G) ≤ normalizer (L : Set G) ∧
                  ¬ A ≤ centralizer (K : Set G) ∧
                  ∃ hAN : A ≤ normalizer (K : Set G),
                    A ⊓ centralizer (K : Set G) = ⊥ ∧
                    (∀ a : A, K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K) ∧
                    (∃ j : A →* K ⧸ center K, Function.Injective j ∧
                      (∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                        K.normalizerMonoidHom (inclusion hAN a)) ∧
                      Nat.card j.range = 16 ∧ IsElementaryAbelian 2 j.range ∧
                      ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = K ⊓ ((T : Subgroup G) ⊓ C) ∧
                        let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
                        j.range ≤ (Q : Subgroup _) ∧
                        (Q : Subgroup _) ≤ normalizer (j.range : Set (K ⧸ center K)) ∧
                        ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf (Q : Subgroup _)).index ≤ 2 ∧
                        ¬ IsCyclic (center Q) ∧
                        center K = ⊥ ∧
                        j.range ≤ (center Q).map (Q : Subgroup _).subtype ∧
                        6 < ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
                          (normalizer (Q : Set (K ⧸ center K)))).index ∧
                        (¬ (normalizer (P : Set K)).map K.subtype ≤ normalizer (L : Set G)) ∧
                        (P : Subgroup K).map K.subtype ≤ centralizer ((Z ⊔ A : Subgroup G) : Set G) ∧
                        (T : Subgroup G) ⊓ centralizer ((Z ⊔ A : Subgroup G) : Set G) = Q₀ ∧
                        (P : Subgroup K).map K.subtype ≤ Q₀ ∧
                        (∃ S : Sylow 2 (K ⊔ Q₀ : Subgroup G),
                          (S : Subgroup _).map (K ⊔ Q₀).subtype = Q₀)) ∧
                    4 ≤ primeRank 2 (K ⧸ center K) ∧
                    (∃ n : ℕ, 2 ≤ n ∧
                      (ClassificationModels.IsG2At (K ⧸ center K) (2^n) ∨
                        Triality.Standard.IsTrialityGroupAt (2^n) (K ⧸ center K))) := by
  obtain ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,hPC,hoddC,
    H,hBH,hHC,hNH,hmin,hSQ,hMH,hoddH,hcore,hPH,K,hK,hKM,hgen,hsmall,
    E,hV,hVt,hmark,hno,hsing,v,f,hfv,hZU,hdis,hcard,hmove,hhyper,
    hnorm,hN,hcorank,hCM,hact,hAN,hker,hi,
    ⟨j,hj,hjact,hjcard,hje,P,hPactual,hAQ,hQN,hindex,hcyc,hzK,hjcent,hlarge,
      hPjoin,hQ,hPQ,hS⟩,hrank,hmodelK⟩ :=
    D.sourceOrbit_binary_exists_pureLine_component_core_placement h hd F hF hmodel hnon hw
  let W₀ := D.sourceOrbit
  let Z := ⁅offenderNormalizer W₀ g,offenderFixedSpan W₀ g⁆
  let C := centralizer (Z : Set G)
  let B := localBase L (T : Subgroup G) Z
  let Q₀ := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let U := ambientPlane W₀ E v f
  let A := ⁅W₀,localResidual L U⁆
  let := hje
  let := hK.quasisimple
  have hZW : Z ≤ W₀ := hpair.trans inf_le_left
  have hAW : A ≤ W₀ := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (inf_le_left.trans hmark.1))
  have hQW : (T : Subgroup G) ⊓ centralizer (W₀ : Set G) = Q₀ := by
    simpa only [W₀,Q₀,D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hQH : Q₀ ≤ H := by
    rw [←hQW]
    exact (inf_le_inf_left _ (centralizer_le hZW)).trans (le_sup_right.trans hBH)
  have hZne : Z ≠ ⊥ := by
    intro he
    have hh : Nat.card Z = 2 := hZ
    rw [he,card_bot] at hh
    omega
  have hpoint := D.sourceOrbit_binary_pureLine_image_card_dvd h hd F hF hmodel
    t ht Z hZne hpure
  have hPW : (P : Subgroup K).map K.subtype ≤ centralizer (W₀ : Set G) := by
    have hQC : Q₀ ≤ centralizer (W₀ : Set G) := by rw [←hQW]; exact inf_le_right
    exact hPQ.trans hQC
  have hout : ¬ (normalizer (P : Set K)).map K.subtype ≤ normalizer (L : Set G) := by
    rw [←D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]
    exact DoubledBinaryPureCartan.normalizer_escape W₀ Z K A hAW (hK.1.trans hHC)
      hAN hpoint j hjact P hPW (lt_trans (by decide) hlarge)
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q₀ := by
    rw [←hQW]
    exact le_inf (sSup_le fun _ hA => hA.1)
      (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
  have hJ := (D.sourceOrbit_nonFF_thompson_normalizers h hnon).2 Q₀
    (isPGroup_pCoreIn 2 _) hJQ
  have hNJ : normalizer (elementaryAbelianMaxJ Q₀ : Set G) ≤ normalizer (L : Set G) := by
    rw [hJ.1]
    exact (D.sourceOrbit_nonFF_thompson_normalizers h hnon).1
  have hNQ := (D.sourceOrbit_core_normalizer h).2
  have horbit := component_normalizer_index H K Q₀ hSQ.stronglyQuasithin hK hQH
  have hmodels : ∃ n : ℕ, 2 ≤ n ∧
      (ClassificationModels.IsG2At (K ⧸ center K) (2^n) ∨
        Triality.Standard.IsTrialityGroupAt (2^n) (K ⧸ center K)) := by
    rcases hmodelK with hm | ⟨n,hn,hm | hm | hm | hm⟩ | ⟨m,hm,he⟩
    · cases hm with
      | linear n hn hm =>
        exact (hout ((DoubledBinaryBenderExclusion.linearTwo_normalizer_thompson H K Q₀
          hK hQH (isPGroup_pCoreIn 2 _) horbit P hPQ
          (linearTwo_degree_ge_four hn hm _ j.range hAQ hjcard) hm).trans hNJ)).elim
      | unitary n hn hm =>
        have hnK := DoubledBinaryUnitaryExclusion.unitary_normal H K hK
          hSQ.stronglyQuasithin hzK hn hm
        have hQN : Q₀ ≤ normalizer (K : Set G) :=
          hQH.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hnK)
        have hNW : normalizer (elementaryAbelianMaxJ Q₀ : Set G) ≤
            normalizer (W₀ : Set G) := by
          rw [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]
          exact hNJ
        exact (DoubledBinaryPureUnitary.unitary_exclusion W₀ Z K A Q₀ hAW
          (hK.1.trans hHC) hAN hzK (isPGroup_pCoreIn 2 _) hQN hNW hpoint j hjcard
          hjact P hPQ hAQ (unitary_degree_ge_four hn hm _ j.range hAQ hjcard) hm).elim
      | suzuki m hm he =>
        exact (hout ((suzuki_normalizer_thompson H K Q₀ hK hQH
          (isPGroup_pCoreIn 2 _) horbit P hPQ
          (suzuki_parameter_ge_two hm he _ j.range hAQ hjcard) he).trans hNJ)).elim
    · exact (hout ((linear_normalizer_thompson H K Q₀ hK hQH (isPGroup_pCoreIn 2 _)
        hSQ.stronglyQuasithin hzK P hPQ hn hm).trans hNJ)).elim
    · exact (hout ((symplectic_normalizer_thompson H K Q₀ hK hQH (isPGroup_pCoreIn 2 _)
        hSQ.stronglyQuasithin hzK P hPQ hn hm).trans hNJ)).elim
    · exact ⟨n,hn,Or.inl hm⟩
    · exact ⟨n,hn,Or.inr hm⟩
    · have hnK := ree_component_normal H K hK hSQ.stronglyQuasithin hzK hm he
      have hQN : Q₀ ≤ normalizer (K : Set G) :=
        hQH.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hnK)
      exact (hout ((ree_normalizer_le_core_normalizer K Q₀ (isPGroup_pCoreIn 2 _)
        hQN P hPQ hm he).trans hNQ)).elim
  exact ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,hPC,hoddC,
    H,hBH,hHC,hNH,hmin,hSQ,hMH,hoddH,hcore,hPH,K,hK,hKM,hgen,hsmall,
    E,hV,hVt,hmark,hno,hsing,v,f,hfv,hZU,hdis,hcard,hmove,hhyper,
    hnorm,hN,hcorank,hCM,hact,hAN,hker,hi,
    ⟨j,hj,hjact,hjcard,hje,P,hPactual,hAQ,hQN,hindex,hcyc,hzK,hjcent,hlarge,hout,
      hPjoin,hQ,hPQ,hS⟩,hrank,hmodels⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

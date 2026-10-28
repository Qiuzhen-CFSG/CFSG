module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryInvariantCover
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.UniqueLocalResidualKernel

/-!
# Escape of the original invariant factor

Suppose the original two-generated span P = ⟨E^I⟩ lies in M. Every conjugate
of E then normalizes the natural layer and centralizes Z_S, so its commutator
with the layer lies in Z_S. This extends to P. Consequently O²(P) centralizes
the layer. Its original T-invariance, normality in I and the natural action
make LT normalize O²(P). Uniqueness over LT and characteristic two in the
escaping I force O²(P) = 1, contrary to the three-divisibility of each actual
S₃, L₃(2), or S₅ quotient model.

This proves escape for the same marked P, its full N_G(Z_S)-invariant cover,
and PT without asserting that P itself is T-invariant. In the S₃ row, the
checked Sylow index three proves that PT is in the literal H-star family.
The same original W/Z_S action and both quotient maps are retained.

Source: Aschbacher–Smith 6.1.19, printed pp.674–675, the escaping-factor and
invariant-parabolic step. The S₅ and L₃(2) parabolic selections, the amalgam
contradiction, initial 6.1.4–5 and remaining geometry belong to
qt-d-1222-rankone-recognition-natural, which retains final 6.1.27 assembly.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

private theorem contained_span_commutator
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (E : Subgroup G) (hEtwo : IsPGroup 2 E)
    (hEI : E ≤ Escape.I (T : Subgroup G) L R)
    (hPM : conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ≤ M) :
    ⁅conjugateSpanBy E (Escape.I (T : Subgroup G) L R),layer L R⁆ ≤
      ZS (T : Subgroup G) L R := by
  let I := Escape.I (T : Subgroup G) L R
  let B := layer L R
  let Z := ZS (T : Subgroup G) L R
  let P := conjugateSpanBy E I
  have hPI : P ≤ I := conjugateSpanBy_le_self hEI
  have hPB : P ≤ normalizer (B : Set G) :=
    (le_inf hPM hPI).trans (hE.localCentralizer_le_normalizer h.ZS_ne_bot inf_le_left)
  have hpre : P ≤ commutatorPreimage I B Z := by
    simp only [P,conjugateSpanBy_eq_iSup_conj]
    apply iSup_le
    intro i
    let A := E.map (MulAut.conj (i : G)).toMonoidHom
    have hAP : A ≤ P := by
      simp only [P,conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun j : I => E.map (MulAut.conj (j : G)).toMonoidHom) i
    apply le_commutatorPreimage (hAP.trans hPI)
    rw [commutator_comm]
    by_cases hz : ⁅B,A⁆ = ⊥
    · exact hz.le.trans bot_le
    · exact (NaturalEscapeGraph.commutator_eq_line h hnat hs
        (hEtwo.map (MulAut.conj (i : G)).toMonoidHom)
        (hAP.trans hPB) (hAP.trans hPI) hz).le
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le I B Z (Subgroup.centralizer_le_normalizer _))

/-- An invariant original residual makes a non-two-group conjugate span
escape M. Only normalization of O²(P), rather than of P, is required. -/
theorem natural_escape_span_not_le_of_residual_invariant
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hI : ¬ Escape.I (T : Subgroup G) L R ≤ M)
    (E : Subgroup G) (hEtwo : IsPGroup 2 E)
    (hEI : E ≤ Escape.I (T : Subgroup G) L R)
    (hTY : let P := conjugateSpanBy E (Escape.I (T : Subgroup G) L R)
      (T : Subgroup G) ≤ normalizer ((pResidual 2 P).map P.subtype : Set G))
    (hPtwo : ¬ IsPGroup 2 (conjugateSpanBy E (Escape.I (T : Subgroup G) L R))) :
    ¬ conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ≤ M := by
  intro hPM
  let I := Escape.I (T : Subgroup G) L R
  let P := conjugateSpanBy E I
  let B := layer L R
  let Z := ZS (T : Subgroup G) L R
  let Y := (pResidual 2 P).map P.subtype
  have hPI : P ≤ I := conjugateSpanBy_le_self hEI
  have hIP : I ≤ normalizer (P : Set G) := le_normalizer_conjugateSpanBy E I
  have hYC : Y ≤ centralizer (B : Set G) := residual_centralizes_of_two_layer P B Z
    (T.isPGroup'.to_le h.ZS_le_T) hPI (contained_span_commutator h hnat hE hs E hEtwo hEI hPM)
  have hIY : I ≤ normalizer (Y : Set G) := hIP.trans
    (normalizer_le_normalizer_characteristic_image P (pResidual 2 P))
  have hNL : normalizer (B : Set G) ≤ normalizer (L : Set G) :=
    hE.normalizer_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)
  have hLN : L ≤ normalizer (B : Set G) := normalizer_commutator_ge_right R L
  have hLC : ⁅L,centralizer (B : Set G)⁆ ≤ L.pCoreIn 2 := by
    apply le_trans (le_inf ?_ ?_) (natural_centralizer_eq_core hnat).le
    · exact le_normalizer_iff_commutator_le_left.mp
        ((Subgroup.centralizer_le_normalizer _).trans hNL)
    · exact le_normalizer_iff_commutator_le_right.mp
        (hLN.trans (normalizer_le_normalizer_centralizer B))
  have hLQ : L ≤ normalizer (L.pCoreIn 2 : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hQI : L.pCoreIn 2 ≤ I :=
    ((natural_centralizer_eq_core hnat).ge.trans inf_le_right).trans
      (centralizer_le (show Z ≤ B from inf_le_left))
  have hLY : L ≤ normalizer (Y : Set G) := normalizes_residual_of_commutator_le_two
    L I P (L.pCoreIn 2) hIP hQI (isPGroup_pCoreIn 2 L) hLQ
      ((commutator_mono le_rfl hYC).trans hLC)
  have hstar : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.prop,?_⟩
    intro J hJ hLJ
    exact le_antisymm (h.local_mem.1.2 hJ hLJ) hLJ
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.simpleQTKE T hstar
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl h.sylow_normalizes_L)
      (le_componentOrbit L T)
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M := by
    intro N hN hLN
    have h1 := hu.normalizer_unique N hN
    have h2 := hu.normalizer_unique M h.maximal
    rw [horbit] at h1 h2
    exact (h1 hLN).trans (h2 (sup_le h.L_le h.sylow_le)).symm
  have hYbot : Y = ⊥ := normal_eq_bot_of_unique_core (L ⊔ (T : Subgroup G)) I M Y
    huniq hI h.ZS_centralizer_mem_He ((map_subtype_le _).trans hPI) hIY (sup_le hLY hTY)
  have hres : pResidual 2 P = ⊥ :=
    (map_eq_bot_iff_of_injective _ P.subtype_injective).mp hYbot
  apply hPtwo
  exact (isPGroup_quotient_pResidual (G := P) 2).of_injective
    (QuotientGroup.mk' (pResidual 2 P)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk',hres])

private theorem cubic_overgroup_mem_HStar
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hHN : H ≤ Escape.H (T : Subgroup G) L R)
    (hHM : ¬ H ≤ M) (hi : (T : Subgroup G).relIndex H = 3) :
    H ∈ Chapter3.HStar (T : Subgroup G) M := by
  have hN : Escape.H (T : Subgroup G) L R ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨ZS (T : Subgroup G) L R,h.ZS_ne_bot,
      T.isPGroup'.to_le h.ZS_le_T,rfl⟩,h.sylow_normalizes_ZS⟩
  refine ⟨⟨Chapter3.mem_HOver_of_sylow_interval T hTH hHN hN,hHM⟩,?_⟩
  intro X hX hXH
  have hd : X.relIndex H ∣ 3 := hi ▸ relIndex_dvd_of_le_left H hX.1.2
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact relIndex_eq_one.mp h1
  · have hh := relIndex_mul_relIndex (T : Subgroup G) X H hX.1.2 hXH
    rw [h3,hi] at hh
    have hx : (T : Subgroup G).relIndex X = 1 := by omega
    exact False.elim (hX.2 ((relIndex_eq_one.mp hx).trans h.sylow_le))

/-- Escape of the same marked factor and its full cover; in the cubic row,
the actual Sylow extension is a minimal outside overgroup. -/
@[expose] def NaturalEscapingCoverData (T : Sylow 2 G) (P N M : Subgroup G) : Prop :=
  let K := P ⊔ N.pCoreIn 2
  let H := P ⊔ (T : Subgroup G)
  (¬ P ≤ M) ∧ (¬ K ≤ M) ∧ (¬ H ≤ M) ∧ H ≤ N ∧
    N ⊓ normalizer (T : Set G) ≤ normalizer (H : Set G) ∧
    (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) →
      H ∈ Chapter3.HStar (T : Subgroup G) M ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∧
      (T : Subgroup G).relIndex H = 3)

namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d

/-- The same original factor escapes M. Its invariant cover and Sylow extension
escape as well; the S₃ row yields an actual minimal outside parabolic. -/
theorem exists_ambient_escaping_cover
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (_hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      let := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        let := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
            (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) ∧
            ((pResidual 2 P).map P.subtype = (primeToResidual 3 I).map I.subtype) ∧
            (N ≤ Subgroup.normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
            NaturalInvariantCoverData T P I N σ hPI ∧
            NaturalEscapingCoverData T P N M := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover⟩ :=
    d.exists_ambient_invariant_cover h hnat hE hs hNS hab
  let := hZ
  let := hX
  let I := Escape.I (T : Subgroup G) L R
  let N := Escape.H (T : Subgroup G) L R
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let P := conjugateSpanBy E I
  let K := P ⊔ N.pCoreIn 2
  let H := P ⊔ (T : Subgroup G)
  have hIout : ¬ I ≤ M := fun hc =>
    d.hstar.1.2 (d.overgroup.trans (sup_le hc h.sylow_le))
  have hPtwo : ¬ IsPGroup 2 P := by
    intro hp
    have hd := (NaturalCanonicalResidual.model_facts hmodels).1
    obtain ⟨k,hk⟩ := (hp.to_quotient (pCore 2 P)).exists_card_eq
    rw [hk] at hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hPout : ¬ P ≤ M := natural_escape_span_not_le_of_residual_invariant h hnat hE hs
    hIout E ((T.isPGroup'.to_le h.layer_le_T).map (MulAut.conj a).toMonoidHom)
    hEI (h.sylow_normalizes_ZS.trans hnormal) hPtwo
  have hcoverSaved := hcover
  obtain ⟨hKI,hNK,hTK,hcore,eK,hrange,hker,hS3⟩ := hcover
  have hKout : ¬ K ≤ M := fun hc => hPout (le_sup_left.trans hc)
  have hHout : ¬ H ≤ M := fun hc => hPout (le_sup_left.trans hc)
  have hHN : H ≤ N := sup_le hPN h.sylow_normalizes_ZS
  have hQT : N.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hTN : (T : Subgroup G) ≤ N := h.sylow_normalizes_ZS
    have hh := pCoreIn_le_sylow N (T.subtype hTN)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN] at hh
  have hHK : H = K ⊔ (T : Subgroup G) := by
    exact le_antisymm (sup_le_sup le_sup_left le_rfl)
      (sup_le (sup_le le_sup_left (hQT.trans le_sup_right)) le_sup_right)
  have hNH : N ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (H : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hHK,Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp (hNK hx.1),
      mem_normalizer_iff_map_conj_eq.mp hx.2]
  have hstar : Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) →
      H ∈ Chapter3.HStar (T : Subgroup G) M ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∧
      (T : Subgroup G).relIndex H = 3 := by
    intro he
    obtain ⟨hq,hi⟩ := hS3 he
    exact ⟨cubic_overgroup_mem_HStar h H le_sup_right hHN hHout hi,hq,hi⟩
  exact ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcoverSaved,
    hPout,hKout,hHout,hHN,hNH,hstar⟩

end NaturalEscapeGraph.OddConfiguration
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

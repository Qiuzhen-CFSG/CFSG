module
public import Stellmacher.SectionFiveToSeven.SixThreeOmegaEquality
public import Stellmacher.SectionFiveToSeven.SixThreeCoreFreePair
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Stellmacher.SectionFiveToSeven.Result6_2
public import Stellmacher.SectionFiveToSeven.SixThreeSelectedFactor

/-!
# The native intermediate quotients in Stellmacher (6.3)

Under Hypothesis Two with nontrivial P2 action on Omega_1(Z(S)), the Baumann
subgroup is all of S and both original local groups have nested SL2(2)
Frattini quotients. This retains an intermediate conclusion of (6.3) needed
for choosing a generating Sylow subgroup in the opening of (8.2).

Thompson noncontainment from (6.2) permits selection on each actual Baumann
omega module. The selected local groups have four-element omega/residual
commutators and fixed index two. A suitable S-conjugate forms a core-free
pair; the small fixed-hyperplane argument gives Omega_1(Z(B))=Omega_1(Z(S)).
Conjugation transports the exact commutators, normalization and indices.
Since Omega_1(Z(J(S))) lies in Omega_1(Z(B)), S centralizes that subgroup
and B=S. Each selected factor contains S and generates its original Pi
with S, so it equals Pi. Core and Frattini quotient equivalences transport
the selected native SL2 quotient to that literal original local group.

Source: Stellmacher (6.3), Journal of Algebra 190 (1997), p.31,
refs/latex/stellmacher-n-group.tex. The ordinary dihedral quotient statement
is assembled separately in Result6_3. No conclusion of (8.2) is used.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

private theorem fixed_subgroup_map {G : Type*} [Group G]
    (A E : Subgroup G) (e : G ≃* G) :
    (A ⊓ Subgroup.centralizer (E : Set G)).map e.toMonoidHom =
      A.map e.toMonoidHom ⊓ Subgroup.centralizer (E.map e.toMonoidHom : Set G) := by
  ext z
  constructor
  · rintro ⟨a, ⟨haA, haC⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ haA, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg e (Subgroup.mem_centralizer_iff.mp haC x hx)
  · rintro ⟨⟨a, haA, rfl⟩, haC⟩
    refine ⟨a, ⟨haA, Subgroup.mem_centralizer_iff.mpr ?_⟩, rfl⟩
    intro x hx
    apply e.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      Subgroup.mem_centralizer_iff.mp haC (e x) (Subgroup.mem_map_of_mem _ hx)

private theorem omega_eq_of_selected_pair
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) (hcomm : ⁅P2, omegaOneCenter S⁆ ≠ ⊥)
    (E F W1 M : Subgroup H)
    (hE : E ∈ PFamily (⊤ : Subgroup H) (baumannIn S))
    (hF : F ∈ PFamily (⊤ : Subgroup H) (baumannIn S))
    (hEL : E ≤ sectionSixL (baumannIn S) P1)
    (hgenE : E ⊔ S = P1) (hgenF : F ⊔ S = P2)
    (hW1 : W1 = ⁅omegaOneCenter (baumannIn S), twoResidualIn E⁆)
    (hW1ne : W1 ≠ ⊥) (hW1B : W1 ≤ baumannIn S)
    (hLW1 : sectionSixL (baumannIn S) P1 ≤ Subgroup.normalizer (W1 : Set H))
    (hM : IsMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (hidxE : (omegaOneCenter (baumannIn S) ⊓ Subgroup.centralizer (E : Set H)).relIndex
      (omegaOneCenter (baumannIn S)) = 2)
    (hidxF : (omegaOneCenter (baumannIn S) ⊓ Subgroup.centralizer (F : Set H)).relIndex
      (omegaOneCenter (baumannIn S)) = 2) :
    omegaOneCenter (baumannIn S) = omegaOneCenter S := by
  obtain ⟨s, hs, hcore⟩ := sixThree_exists_core_free_pair S0 S P1 P2 h E F W1 M
    hE hF hEL hgenE hgenF hW1 hW1ne hW1B hLW1 hM
  let B := baumannIn S
  let A := omegaOneCenter B
  let L := sectionSixL B P1
  let e := MulAut.conj s
  have hSP1 : S ≤ P1 := by rw [← hgenE]; exact le_sup_right
  have hSB : S ≤ Subgroup.normalizer (B : Set H) :=
    S.le_normalizer.trans (normalizer_le_normalizer_baumann S)
  have hBm : B.map e.toMonoidHom = B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSB hs)
  have hAm : A.map e.toMonoidHom = A := by
    change (omegaOneCenterAmbient B).map e.toMonoidHom = omegaOneCenterAmbient B
    rw [← omegaOneCenterAmbient_map_injective _ e.injective, hBm]
  have hSm : S.map e.toMonoidHom = S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hs)
  have hPm : P1.map e.toMonoidHom = P1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (P1.le_normalizer (hSP1 hs))
  have hP1L : P1 ≤ Subgroup.normalizer (L : Set H) := by
    rw [show L = conjugateClosure B P1 from rfl, conjugateClosure,
      Subgroup.le_normalizer_closure_iff]
    intro p hp x hx
    obtain ⟨q, b, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨⟨p * (q : H), P1.mul_mem hp q.property⟩, b, ?_⟩
    change p * ((q : H) * (b : H) * (q : H)⁻¹) * p⁻¹ =
      (p * (q : H)) * (b : H) * (p * (q : H))⁻¹
    group
  have hLm : L.map e.toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hP1L (hSP1 hs))
  have hEsfamily : conjugateBy E s ∈ PFamily (⊤ : Subgroup H) B :=
    (conjugateBy_mem_pFamily_iff B E s (hSB hs)).mpr hE
  have hEsL : conjugateBy E s ≤ L := by
    have hm := Subgroup.map_mono (f := e.toMonoidHom) hEL
    change conjugateBy E s ≤ L.map e.toMonoidHom at hm
    rwa [hLm] at hm
  have hEsgen : conjugateBy E s ⊔ S = P1 := by
    have hm := congrArg (Subgroup.map e.toMonoidHom) hgenE
    rwa [Subgroup.map_sup, hSm, hPm] at hm
  have hWsB : conjugateBy W1 s ≤ B := by
    have hm := Subgroup.map_mono (f := e.toMonoidHom) hW1B
    rwa [hBm] at hm
  have hWsne : conjugateBy W1 s ≠ ⊥ := by
    exact fun hb => hW1ne ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hb)
  have hWs : conjugateBy W1 s = ⁅omegaOneCenter B, twoResidualIn (conjugateBy E s)⁆ := by
    have hRm : (twoResidualIn E).map e.toMonoidHom = twoResidualIn (conjugateBy E s) :=
      map_twoResidualAmbient_of_subgroup_image E e.toMonoidHom _ rfl
    change W1.map e.toMonoidHom = _
    rw [hW1, Subgroup.map_commutator]
    change ⁅A.map e.toMonoidHom, (twoResidualIn E).map e.toMonoidHom⁆ = _
    rw [hAm, hRm]
  have hLWs : L ≤ Subgroup.normalizer (conjugateBy W1 s : Set H) := by
    have hm := Subgroup.map_mono (f := e.toMonoidHom) hLW1
    change L.map e.toMonoidHom ≤ _ at hm
    rwa [Subgroup.map_equiv_normalizer_eq, hLm] at hm
  have hidxEs : (A ⊓ Subgroup.centralizer (conjugateBy E s : Set H)).relIndex A = 2 := by
    have hf := fixed_subgroup_map A E e
    rw [hAm] at hf
    change (A ⊓ Subgroup.centralizer (E.map e.toMonoidHom : Set H)).relIndex A = 2
    have hi : (A ⊓ Subgroup.centralizer (E : Set H)).relIndex A = 2 := hidxE
    rw [← Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) _ _ e.injective] at hi
    rwa [hf, hAm] at hi
  exact sixThree_omega_eq S0 S P1 P2 h hcomm (conjugateBy E s) F (conjugateBy W1 s) M
    hEsfamily hF hEsL hEsgen hgenF hWs hWsne hWsB hLWs hM hcore hidxEs hidxF

private theorem baumann_eq_of_omega_eq {H : Type*} [Group H]
    (S : Subgroup H) (hOmega : omegaOneCenter (baumannIn S) = omegaOneCenter S) :
    baumannIn S = S := by
  let J := elementaryAbelianMaxJ S
  let Z := omegaOneCenter J
  have hJS : J ≤ S := sSup_le fun _ hA => hA.1
  have hZJ : Z ≤ J := Subgroup.map_subtype_le _
  have hJB : J ≤ baumannIn S := by
    refine le_inf hJS ?_
    exact Subgroup.le_centralizer_iff.mp (fun z hz =>
      Subgroup.mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff J z).mp hz).2.2)
  have hZO : Z ≤ omegaOneCenter (baumannIn S) := by
    intro z hz
    apply (mem_omegaOneCenterAmbient_iff (baumannIn S) z).mpr
    refine ⟨hJB (hZJ hz), ((mem_omegaOneCenterAmbient_iff J z).mp hz).2.1, ?_⟩
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp hb.2 z hz).symm
  apply le_antisymm inf_le_left
  refine le_inf le_rfl ?_
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzO : z ∈ omegaOneCenter S := hOmega ▸ hZO hz
  exact ((mem_omegaOneCenterAmbient_iff S z).mp hzO).2.2 s hs |>.symm

private theorem nested_of_selected
    {H : Type u} [Group H] [Finite H]
    (P S : Subgroup H) (K : Subgroup P)
    (hSE : S ≤ (P.subtype.comp K.subtype).range)
    (hgen : (P.subtype.comp K.subtype).range ⊔ S = P)
    (hA : IsSL2Two ((K ⧸ pCore 2 K) ⧸ frattini (K ⧸ pCore 2 K))) :
    IsSL2Two ((P ⧸ pCore 2 P) ⧸ frattini (P ⧸ pCore 2 P)) := by
  have hEP : (P.subtype.comp K.subtype).range = P := by
    rwa [sup_eq_left.mpr hSE] at hgen
  have hKt : K = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simpa only [MonoidHom.range_comp, Subgroup.range_subtype] using hEP
  let eK : K ≃* P := (MulEquiv.subgroupCongr hKt).trans Subgroup.topEquiv
  let eQ : (K ⧸ pCore 2 K) ≃* (P ⧸ pCore 2 P) :=
    QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  have hPhi : (frattini (K ⧸ pCore 2 K)).map eQ.toMonoidHom =
      frattini (P ⧸ pCore 2 P) := by
    apply le_antisymm
    · exact Subgroup.map_le_iff_le_comap.mpr
        (frattini_le_comap_frattini_of_surjective eQ.surjective)
    · intro y hy
      have hy' : eQ.symm y ∈ frattini (K ⧸ pCore 2 K) :=
        frattini_le_comap_frattini_of_surjective
          (φ := eQ.symm.toMonoidHom) eQ.symm.surjective hy
      exact ⟨eQ.symm y, hy', eQ.apply_symm_apply y⟩
  let ePhi := QuotientGroup.congr _ _ eQ hPhi
  obtain ⟨eSL⟩ := hA
  exact ⟨ePhi.symm.trans eSL⟩

public theorem sixThree_native_quotients
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ ≠ ⊥) :
    baumannIn S = S ∧
      IsSL2Two ((P1 ⧸ pCore 2 P1) ⧸ frattini (P1 ⧸ pCore 2 P1)) ∧
      IsSL2Two ((P2 ⧸ pCore 2 P2) ⧸ frattini (P2 ⧸ pCore 2 P2)) := by
  obtain ⟨hJ1, hJ2⟩ := lemma_six_two S0 S P1 P2 h hcomm
  have hswap := h.swap_of_commutator_ne_bot S0 S P1 P2 hcomm
  obtain ⟨K1, T1, _hT1, hEL1, hgen1, hA1, hFam1, hcard1, hWB1, hLW1, hidx1⟩ :=
    sixThree_selected_factor S0 S P1 P2 h hJ1
  obtain ⟨K2, T2, _hT2, _hEL2, hgen2, hA2, hFam2, _hcard2, _hWB2, _hLW2, hidx2⟩ :=
    sixThree_selected_factor S0 S P2 P1 hswap hJ2
  let f1 : K1 →* H := P1.subtype.comp K1.subtype
  let f2 : K2 →* H := P2.subtype.comp K2.subtype
  let W := ⁅omegaOneCenter (baumannIn S), twoResidualIn f1.range⁆
  have hWne : W ≠ ⊥ := by
    intro hb
    have hc1 : Nat.card W = 1 := Subgroup.card_eq_one.mpr hb
    have hc4 : Nat.card W = 4 := hcard1
    omega
  have hS0ne : (S0 : Subgroup H) ≠ ⊥ := by
    intro hb
    exact h.fiveOne.S_nontrivial (le_bot_iff.mp (h.fiveOne.S_le_S0.trans_eq hb))
  let N := Subgroup.normalizer (S0 : Set H)
  have hNlocal : IsTwoLocal N := ⟨(S0 : Subgroup H), hS0ne, S0.isPGroup', rfl⟩
  obtain ⟨M, hNM, hMmax⟩ := Finite.exists_le_maximal hNlocal
  have hM : IsMaximalTwoLocalContaining (S0 : Subgroup H) M :=
    ⟨hMmax, (S0 : Subgroup H).le_normalizer.trans hNM⟩
  have hOmega := omega_eq_of_selected_pair S0 S P1 P2 h hcomm f1.range f2.range W M
    hFam1 hFam2 hEL1 hgen1 hgen2 rfl hWne hWB1 hLW1 hM hidx1 hidx2
  have hBS := baumann_eq_of_omega_eq S hOmega
  have hSE1 : S ≤ f1.range := hBS ▸ hFam1.1.2.1.1
  have hSE2 : S ≤ f2.range := hBS ▸ hFam2.1.2.1.1
  exact ⟨hBS, nested_of_selected P1 S K1 hSE1 hgen1 hA1,
    nested_of_selected P2 S K2 hSE2 hgen2 hA2⟩

end Stellmacher.SectionsFiveToSeven

module

public import Stellmacher.SectionThree.LemmaThreeThree

/-!
# Stellmacher's Lemma 3.4

For a solvable member `P` of `PSet` and a subgroup `T` normal in its Sylow
2-subgroup `S`, either `T` lies in `O₂(P)` or it acts nontrivially enough on
`O²(P)` to satisfy `[O²(P), T] = O²(P)`.

Following Stellmacher's proof (Journal of Algebra 190 (1997), Lemma (3.4),
p. 22), apply Lemma 3.3 to the image of `[O²(P),T]` modulo the normal core
of the distinguished maximal subgroup.  Irreducibility makes that image
either trivial or the full residual.  In the first case normality and the
odd-prime Frattini description force `T ≤ O₂(P)`.  In the second case the
Frattini nongenerating property, followed by the minimal characterization of
the 2-residual, gives `[O²(P),T] = O²(P)`.

The local residual conversion reconciles the section's index-based definition
of `O²` with the quotient-based `hktPResidual` API; the imported residual API
supplies its quotient-map property.
-/

namespace Stellmacher.SectionThree

universe u

open scoped commutatorElement

private theorem twoResidualSubgroup_eq_hktPResidual
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    twoResidualSubgroup H = BenderSuzuki.External.hktPResidual 2 H := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRnormal : (BenderSuzuki.External.hktPResidual 2 H).Normal :=
    BenderSuzuki.External.hktPResidual_normal
  let _ : (BenderSuzuki.External.hktPResidual 2 H).Normal := hRnormal
  apply le_antisymm
  · rw [twoResidualSubgroup]
    apply sInf_le
    refine ⟨hRnormal, ?_⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp
      (BenderSuzuki.External.hktPResidual_quotient_isPGroup (q := 2) (Q := H))
    exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  · intro x hx
    rw [twoResidualSubgroup, Subgroup.mem_sInf]
    intro N hN
    let _ : N.Normal := hN.1
    apply BenderSuzuki.External.hktPResidual_le N hN.1 ?_ hx
    rw [IsPGroup.iff_card]
    obtain ⟨n, hn⟩ := hN.2
    exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩

private theorem le_normalizer_commutator_of_le_normalizers
    {G : Type u} [Group G] {H K N : Subgroup G}
    (hNH : N ≤ Subgroup.normalizer H)
    (hNK : N ≤ Subgroup.normalizer K) :
    N ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.commutator_def, Subgroup.le_normalizer_closure_iff]
  intro n hn x hx
  obtain ⟨h, hh, k, hk, rfl⟩ := hx
  rw [conjugate_commutatorElement]
  apply Subgroup.commutator_mem_commutator
  · exact (Subgroup.mem_normalizer_iff.mp (hNH hn) h).mp hh
  · exact (Subgroup.mem_normalizer_iff.mp (hNK hn) k).mp hk

public theorem lemma_three_four
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (T : Subgroup G)
    (hT : T ≤ S ∧ (T.subgroupOf S).Normal)
    (hsolv : Group.IsSolvable P) :
    T ≤ twoCoreAmbient P ∨
      ⁅twoResidualAmbient P, T⁆ = twoResidualAmbient P := by
  classical
  have hSleP : S ≤ P := by
    obtain ⟨SP, hSP⟩ := hP.1.2.1
    rw [← hSP]
    exact Subgroup.map_subtype_le (SP : Subgroup P)
  have hTleP : T ≤ P := hT.1.trans hSleP
  let SP : Subgroup P := S.subgroupOf P
  let TP : Subgroup P := T.subgroupOf P
  have hSPmap : SP.map P.subtype = S := by
    exact Subgroup.map_subgroupOf_eq_of_le hSleP
  have hTPmap : TP.map P.subtype = T := by
    exact Subgroup.map_subgroupOf_eq_of_le hTleP
  obtain ⟨B, hBcoatom, hSB, hBuniq⟩ := hP.2
  have hSPB : SP ≤ B := by
    intro x hx
    have hxS : (x : G) ∈ S := hx
    have hxmap : (x : G) ∈ B.map P.subtype := hSB hxS
    obtain ⟨b, hb, hbx⟩ := hxmap
    have hbeq : b = x := P.subtype_injective hbx
    simpa [hbeq] using hb
  have hBuniq' : ∀ B' : Subgroup P, IsCoatom B' → SP ≤ B' → B' = B := by
    intro B' hB' hSPB'
    apply hBuniq B' hB'
    intro s hs
    obtain ⟨x, hx, rfl⟩ : ∃ x : P, x ∈ SP ∧ (x : G) = s := by
      exact ⟨⟨s, hSleP hs⟩, hs, rfl⟩
    exact Subgroup.mem_map_of_mem P.subtype (hSPB' hx)
  let P₀ : Subgroup P := B.normalCore
  have hP₀data : P₀ ≤ B ∧ P₀.Normal ∧
      ∀ N : Subgroup P, N.Normal → N ≤ B → N ≤ P₀ := by
    refine ⟨B.normalCore_le, inferInstance, ?_⟩
    intro N hN hNB
    exact @Subgroup.normal_le_normalCore P _ B N hN |>.mpr hNB
  have h33 := lemma_three_three S h P hP B P₀
    ⟨hBcoatom, hSPB, hBuniq'⟩ hP₀data hsolv
  have hResidualEq : twoResidualSubgroup P =
      BenderSuzuki.External.hktPResidual 2 P := by
    exact twoResidualSubgroup_eq_hktPResidual P
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₂, hS₂map⟩ := hP.1.2.1
  have hS₂eq : (S₂ : Subgroup P) = SP := by
    apply Subgroup.map_injective_of_ker_le P.subtype (by simp) (by simp)
    rw [hS₂map, hSPmap]
  have hSPp : IsPGroup 2 SP := by
    rw [← hS₂eq]
    exact S₂.isPGroup'
  have hTPleSP : TP ≤ SP := by
    intro t ht
    exact hT.1 ht
  have hTPp : IsPGroup 2 TP := IsPGroup.to_le hSPp hTPleSP
  have hSPnormTP : SP ≤ Subgroup.normalizer (TP : Set P) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs t ht
    have hSnormT : S ≤ Subgroup.normalizer (T : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hT.1).mp hT.2
    have hsS : (s : G) ∈ S := hs
    have htT : (t : G) ∈ T := ht
    exact (Subgroup.mem_normalizer_iff.mp (hSnormT hsS) (t : G)).mp htT
  let R : Subgroup P := BenderSuzuki.External.hktPResidual 2 P
  have hRnormal : R.Normal :=
    BenderSuzuki.External.hktPResidual_normal
  let _ : R.Normal := hRnormal
  let O : Subgroup P := pCore 2 P
  have hOleSP : O ≤ SP := by
    rw [← hS₂eq]
    exact IsPGroup.le_sylow_of_normal (pCore_isPGroup (G := P) (p := 2)) S₂
  have hRSPtop : R ⊔ SP = ⊤ := by
    let qR : P →* P ⧸ R := QuotientGroup.mk' R
    have hquotR : IsPGroup 2 (P ⧸ R) :=
      BenderSuzuki.External.hktPResidual_quotient_isPGroup
    let Sbar : Sylow 2 (P ⧸ R) :=
      S₂.mapSurjective (QuotientGroup.mk'_surjective R)
    have hSbarTop : (Sbar : Subgroup (P ⧸ R)) = ⊤ := by
      symm
      exact Sbar.is_maximal' (hquotR.to_subgroup ⊤) le_top
    have hmapSP : SP.map qR = ⊤ := by
      rw [← hS₂eq]
      simpa [Sbar, qR] using hSbarTop
    rw [sup_comm]
    calc
      SP ⊔ R = SP ⊔ qR.ker := by rw [QuotientGroup.ker_mk']
      _ = (SP.map qR).comap qR := (Subgroup.comap_map_eq qR SP).symm
      _ = ⊤ := by rw [hmapSP]; simp
  let C : Subgroup P := ⁅R, TP⁆
  have hCleR : C ≤ R := by
    exact Subgroup.commutator_le_left R TP
  have hSPnormR : SP ≤ Subgroup.normalizer (R : Set P) :=
    Subgroup.le_normalizer_of_normal
  have hSPnormC : SP ≤ Subgroup.normalizer (C : Set P) := by
    exact le_normalizer_commutator_of_le_normalizers hSPnormR hSPnormTP
  have hRnormC : R ≤ Subgroup.normalizer (C : Set P) := by
    exact Subgroup.normalizer_commutator_ge_left R TP
  have hCnormal : C.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hRSPtop]
    exact sup_le hRnormC hSPnormC
  let _ : C.Normal := hCnormal
  obtain ⟨hP₀normal, hIrred⟩ := h33.part_b
  let _ : P₀.Normal := hP₀normal
  let q₀ : P →* P ⧸ P₀ := QuotientGroup.mk' P₀
  let R₀ : Subgroup (P ⧸ P₀) :=
    twoResidualAmbient (⊤ : Subgroup (P ⧸ P₀))
  let C₀ : Subgroup (P ⧸ P₀) := C.map q₀
  have hR₀map : R.map q₀ = R₀ := by
    calc
      R.map q₀ = BenderSuzuki.External.hktPResidual 2 (P ⧸ P₀) := by
        simpa [R, q₀] using map_hktPResidual_quotient 2 P₀
      _ = R₀ := by
        simpa [R₀] using
          (twoResidualAmbient_top_eq_hktPResidual (Q := P ⧸ P₀)).symm
  have hC₀le : C₀ ≤ R₀ := by
    rw [← hR₀map]
    exact Subgroup.map_mono hCleR
  have hC₀normal : C₀.Normal :=
    hCnormal.map q₀ (QuotientGroup.mk'_surjective P₀)
  have hC₀inv : IsConjugateInvariantBy C₀ (SP.map q₀) := by
    intro s c hc
    exact hC₀normal.conj_mem c hc s
  have hC₀cases : C₀ = ⊥ ∨ C₀ = R₀ :=
    hIrred.2.2 C₀ bot_le hC₀le hC₀inv
  rcases hC₀cases with hC₀bot | hC₀top
  · have hCleP₀ : C ≤ P₀ := by
      rw [← QuotientGroup.ker_mk' P₀]
      exact (Subgroup.map_eq_bot_iff C).mp hC₀bot
    let D : Subgroup P := P₀ ⊔ TP
    have hDB : D ≤ B := by
      exact sup_le hP₀data.1 (hTPleSP.trans hSPB)
    have hSPnormP₀ : SP ≤ Subgroup.normalizer (P₀ : Set P) :=
      Subgroup.le_normalizer_of_normal
    have hSPnormD : SP ≤ Subgroup.normalizer (D : Set P) := by
      exact (le_inf hSPnormP₀ hSPnormTP).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup P₀ TP)
    have hRnormD : R ≤ Subgroup.normalizer (D : Set P) := by
      rw [Subgroup.le_normalizer_iff]
      intro r hr d hd
      obtain ⟨p₀, hp₀, t, ht, rfl⟩ :=
        Subgroup.mem_sup_of_normal_left.mp hd
      have hconjp₀ : r * p₀ * r⁻¹ ∈ P₀ := hP₀normal.conj_mem p₀ hp₀ r
      have hcomm : ⁅r, t⁆ ∈ C := by
        apply Subgroup.commutator_mem_commutator
        · exact hr
        · exact ht
      have hcommP₀ : ⁅r, t⁆ ∈ P₀ := hCleP₀ hcomm
      have hconjt : r * t * r⁻¹ ∈ D := by
        have hprod : ⁅r, t⁆ * t ∈ D :=
          D.mul_mem
            (show ⁅r, t⁆ ∈ D from
              (le_sup_left : P₀ ≤ D) hcommP₀)
            (show t ∈ D from (le_sup_right : TP ≤ D) ht)
        simpa [commutatorElement_def, mul_assoc] using hprod
      have hfactor : r * (p₀ * t) * r⁻¹ =
          (r * p₀ * r⁻¹) * (r * t * r⁻¹) := by group
      rw [hfactor]
      exact D.mul_mem ((le_sup_left : P₀ ≤ D) hconjp₀) hconjt
    have hDnormal : D.Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      apply top_unique
      rw [← hRSPtop]
      exact sup_le hRnormD hSPnormD
    have hDleP₀ : D ≤ P₀ := hP₀data.2.2 D hDnormal hDB
    have hTPleP₀ : TP ≤ P₀ := le_sup_right.trans hDleP₀
    let qO : P →* P ⧸ O := QuotientGroup.mk' O
    let Rbar : Subgroup (P ⧸ O) :=
      twoResidualAmbient (⊤ : Subgroup (P ⧸ O))
    obtain ⟨p, hp, hpodd, hRbarp⟩ := h33.part_a
    let _ : Fact p.Prime := ⟨hp⟩
    have hP₀bar : P₀.map qO = frattiniAmbient Rbar := by
      simpa [qO, Rbar, O] using h33.part_c
    have hP₀barle : P₀.map qO ≤ Rbar := by
      rw [hP₀bar]
      exact Subgroup.map_subtype_le (frattini Rbar)
    have hP₀barp : IsPGroup p (P₀.map qO) :=
      IsPGroup.to_le hRbarp hP₀barle
    have hTPbarp : IsPGroup 2 (TP.map qO) := IsPGroup.map hTPp qO
    have hTPbarle : TP.map qO ≤ P₀.map qO :=
      Subgroup.map_mono hTPleP₀
    have hp2 : p ≠ 2 := hpodd.ne_two_of_dvd_nat dvd_rfl
    have hdisj : Disjoint (TP.map qO) (P₀.map qO) :=
      IsPGroup.disjoint_of_ne 2 p hp2.symm _ _ hTPbarp hP₀barp
    have hTPbarbot : TP.map qO = ⊥ := hdisj.eq_bot_of_le hTPbarle
    have hTPleO : TP ≤ O := by
      rw [← QuotientGroup.ker_mk' O]
      exact (Subgroup.map_eq_bot_iff TP).mp hTPbarbot
    left
    calc
      T = TP.map P.subtype := hTPmap.symm
      _ ≤ O.map P.subtype := Subgroup.map_mono hTPleO
      _ = twoCoreAmbient P := rfl
  · have hsupP₀ : C ⊔ P₀ = R ⊔ P₀ := by
      apply Subgroup.map_injective_of_ker_le q₀
      · simp [q₀, QuotientGroup.ker_mk']
      · simp [q₀, QuotientGroup.ker_mk']
      simp [Subgroup.map_sup, C₀, hC₀top, hR₀map, q₀]
    have hRleCP₀ : R ≤ C ⊔ P₀ := by
      rw [hsupP₀]
      exact le_sup_left
    let qO : P →* P ⧸ O := QuotientGroup.mk' O
    let Rbar : Subgroup (P ⧸ O) :=
      twoResidualAmbient (⊤ : Subgroup (P ⧸ O))
    have hRbarMap : R.map qO = Rbar := by
      calc
        R.map qO = BenderSuzuki.External.hktPResidual 2 (P ⧸ O) := by
          simpa [R, qO] using map_hktPResidual_quotient 2 O
        _ = Rbar := by
          simpa [Rbar] using
            (twoResidualAmbient_top_eq_hktPResidual (Q := P ⧸ O)).symm
    have hCbarle : C.map qO ≤ Rbar := by
      rw [← hRbarMap]
      exact Subgroup.map_mono hCleR
    have hP₀bar : P₀.map qO = frattiniAmbient Rbar := by
      simpa [qO, Rbar, O] using h33.part_c
    have hP₀barle : P₀.map qO ≤ Rbar := by
      rw [hP₀bar]
      exact Subgroup.map_subtype_le (frattini Rbar)
    have hRbarle : Rbar ≤ C.map qO ⊔ P₀.map qO := by
      rw [← hRbarMap, ← Subgroup.map_sup]
      exact Subgroup.map_mono hRleCP₀
    have hsupbar : C.map qO ⊔ P₀.map qO = Rbar :=
      le_antisymm (sup_le hCbarle hP₀barle) hRbarle
    let CR : Subgroup Rbar := (C.map qO).subgroupOf Rbar
    have hCRmap : CR.map Rbar.subtype = C.map qO :=
      Subgroup.map_subgroupOf_eq_of_le hCbarle
    have hPhiMap : (frattini Rbar).map Rbar.subtype = P₀.map qO := by
      simpa [frattiniAmbient] using hP₀bar.symm
    have hInternalSup : CR ⊔ frattini Rbar = ⊤ := by
      apply Subgroup.map_injective_of_ker_le Rbar.subtype (by simp) (by simp)
      rw [Subgroup.map_sup, hCRmap, hPhiMap, hsupbar]
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hCRtop : CR = ⊤ := frattini_nongenerating hInternalSup
    have hCbarEq : C.map qO = Rbar := by
      rw [← hCRmap, hCRtop]
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hsupO : C ⊔ O = R ⊔ O := by
      apply Subgroup.map_injective_of_ker_le qO
      · simp [qO, QuotientGroup.ker_mk']
      · simp [qO, QuotientGroup.ker_mk']
      simp [Subgroup.map_sup, hCbarEq, hRbarMap, qO]
    have hRleCO : R ≤ C ⊔ O := by
      rw [hsupO]
      exact le_sup_left
    have hCSPtop : C ⊔ SP = ⊤ := by
      apply top_unique
      rw [← hRSPtop]
      exact sup_le
        (hRleCO.trans (sup_le_sup le_rfl hOleSP))
        le_sup_right
    let qC : P →* P ⧸ C := QuotientGroup.mk' C
    have hmapSP : SP.map qC = ⊤ := by
      have hmapped := congrArg (fun H : Subgroup P ↦ H.map qC) hCSPtop
      simpa [Subgroup.map_sup, qC,
        Subgroup.map_top_of_surjective qC (QuotientGroup.mk'_surjective C)] using hmapped
    let f : SP →* P ⧸ C := qC.comp SP.subtype
    have hfsurj : Function.Surjective f := by
      intro y
      have hy : y ∈ SP.map qC := by rw [hmapSP]; trivial
      obtain ⟨s, hs, hsy⟩ := hy
      exact ⟨⟨s, hs⟩, by simpa [f] using hsy⟩
    have hquotC : IsPGroup 2 (P ⧸ C) := hSPp.of_surjective f hfsurj
    have hRleC : R ≤ C :=
      BenderSuzuki.External.hktPResidual_le C hCnormal hquotC
    have hCeqR : C = R := le_antisymm hCleR hRleC
    right
    calc
      ⁅twoResidualAmbient P, T⁆ =
          ⁅R.map P.subtype, TP.map P.subtype⁆ := by
            rw [hTPmap]
            change ⁅(twoResidualSubgroup P).map P.subtype, T⁆ =
              ⁅R.map P.subtype, T⁆
            rw [hResidualEq]
      _ = C.map P.subtype := by
        symm
        exact Subgroup.map_commutator R TP P.subtype
      _ = R.map P.subtype := by rw [hCeqR]
      _ = twoResidualAmbient P := by
        change R.map P.subtype = (twoResidualSubgroup P).map P.subtype
        rw [hResidualEq]

end Stellmacher.SectionThree

module

public import Stellmacher.SectionTwo.LemmaTwoThree
public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# Transporting the local pushing-up bound into the Section 2 module

This is the local-to-ambient bridge suppressed in the proof of Stellmacher
(2.4), Journal of Algebra 190 (1997), p. 20.  The subgroup occurring in the
cited pushing-up theorem is the normal closure of the center of a Sylow
subgroup of the chosen local group; it must not be identified with the
ambient subgroup `V` by notation alone.

The local omega center maps into `Ω₁(Z(B))`.  Since it lies in the ambient
Sylow subgroup and centralizes `J(S)`, the maximal-elementary argument puts it
in `Z = Ω₁(Z(J(S)))`.  Its local normal closure therefore maps into the
normal supplement `W = Z ⊔ V` supplied by (2.3).  The same supplement gives
`[W,E] ≤ V`; the Baumann subgroup centralizes `Z`, so after passing to the
quotient by `V` this extends to `[W,L] ≤ V`.  Mapping the cited local
commutator then yields the desired containment in the ambient `V`.
-/

namespace Stellmacher.SectionTwo

universe u

/-- The local pushing-up commutator maps into the Section 2 subgroup `V`. -/
public theorem two_four_local_bound_maps_to_v
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcore : pCore 2 G =
      (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G))
    (hnot : ¬ vSubgroup S ≤
      Subgroup.centralizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G))
    (B L L₁ : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient
        (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (hL : L =
      Subgroup.normalClosure
          (elementaryAbelianMaxJ (S : Subgroup G) : Set G) ⊔ B)
    (hL₁L : L₁ ≤ L)
    (P : Sylow 2 L₁) (hPmap : P.map L₁.subtype = B)
    (hlocal :
      ⁅pCore 2 L₁, twoResidualAmbient (⊤ : Subgroup L₁)⁆ ≤
        ⁅Subgroup.normalClosure
            (omegaOneCenterAmbient (P : Subgroup L₁) : Set L₁),
          (⊤ : Subgroup L₁)⁆) :
    (⁅pCore 2 L₁, twoResidualAmbient (⊤ : Subgroup L₁)⁆).map
        L₁.subtype ≤ vSubgroup S := by
  classical
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let E := Subgroup.normalClosure (J : Set G)
  let Z := omegaOneCenterAmbient J
  let V := vSubgroup S
  let W := Z ⊔ V
  let _ : V.Normal := Subgroup.normalClosure_normal
  obtain ⟨_hWelem, hWE, hEnormW, hWEcomm, _hfixed⟩ :=
    two_three_omega_normal_supplement h S hcore hnot
  have hBS : B ≤ (S : Subgroup G) := hB ▸ inf_le_left
  have hJB : J ≤ B := by
    rw [hB]
    refine le_inf (sSup_le fun _ hA => hA.1) ?_
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff J z).mp hz).2.2 j hj |>.symm
  let OmegaB := omegaOneCenterAmbient B
  let _ : IsElementaryAbelian 2 OmegaB :=
    omegaOneCenterAmbient_elementaryAbelian B
  have hOmegaBS : OmegaB ≤ (S : Subgroup G) :=
    (Subgroup.map_subtype_le _).trans hBS
  have hOmegaBC : OmegaB ≤ Subgroup.centralizer (J : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact ((mem_omegaOneCenterAmbient_iff B z).mp hz).2.2 j (hJB hj)
  have hOmegaBZ : OmegaB ≤ Z :=
    elementary_centralizer_maxJ_le_omegaCenter
      (S : Subgroup G) OmegaB hOmegaBS hOmegaBC
  let OmegaLocal := omegaOneCenterAmbient (P : Subgroup L₁)
  have hOmegaMap : OmegaLocal.map L₁.subtype = OmegaB := by
    calc
      OmegaLocal.map L₁.subtype =
          omegaOneCenterAmbient ((P : Subgroup L₁).map L₁.subtype) :=
        (omegaOneCenterAmbient_map_injective L₁.subtype
          L₁.subtype_injective (P : Subgroup L₁)).symm
      _ = OmegaB := by rw [hPmap]
  have hBnormZ : B ≤ Subgroup.normalizer (Z : Set G) := by
    dsimp only [Z]
    rw [hB]
    exact inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hBnormV : B ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hBnormW : B ≤ Subgroup.normalizer (W : Set G) :=
    (le_inf hBnormZ hBnormV).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup Z V)
  have hLnormW : L ≤ Subgroup.normalizer (W : Set G) := by
    rw [hL]
    exact sup_le hEnormW hBnormW
  have hWLcomm : ⁅W, L⁆ ≤ V := by
    let qV : G →* G ⧸ V := QuotientGroup.mk' V
    have hVmap : V.map qV = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      simp only [qV, QuotientGroup.ker_mk', le_rfl]
    have hEmapCent : E.map qV ≤
        Subgroup.centralizer (W.map qV : Set (G ⧸ V)) := by
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      rw [← Subgroup.map_commutator, Subgroup.commutator_comm]
      apply (Subgroup.map_eq_bot_iff _).mpr
      simpa only [qV, QuotientGroup.ker_mk'] using hWEcomm
    have hBcentZ : B ≤ Subgroup.centralizer (Z : Set G) := by
      rw [hB]
      exact inf_le_right
    have hZcentB : Z ≤ Subgroup.centralizer (B : Set G) :=
      Subgroup.le_centralizer_iff.mp hBcentZ
    have hBmapCent : B.map qV ≤
        Subgroup.centralizer (W.map qV : Set (G ⧸ V)) := by
      apply Subgroup.le_centralizer_iff.mp
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      change ⁅(Z ⊔ V).map qV, B.map qV⁆ = ⊥
      rw [Subgroup.map_sup, hVmap, sup_bot_eq,
        ← Subgroup.map_commutator]
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZcentB,
        Subgroup.map_bot]
    have hLmapCent : L.map qV ≤
        Subgroup.centralizer (W.map qV : Set (G ⧸ V)) := by
      rw [hL, Subgroup.map_sup]
      exact sup_le hEmapCent hBmapCent
    have hzero : (⁅W, L⁆).map qV = ⊥ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff.mp hLmapCent)
    have hker := (Subgroup.map_eq_bot_iff _).mp hzero
    simpa only [qV, QuotientGroup.ker_mk'] using hker
  have hL₁normW : L₁ ≤ Subgroup.normalizer (W : Set G) :=
    hL₁L.trans hLnormW
  let Wlocal : Subgroup L₁ := W.comap L₁.subtype
  have hWlocalNormal : Wlocal.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    have htopNorm : (⊤ : Subgroup L₁) ≤
        (Subgroup.normalizer (W : Set G)).comap L₁.subtype := by
      intro x _
      exact hL₁normW x.property
    exact htopNorm.trans (Subgroup.le_normalizer_comap L₁.subtype)
  let _ : Wlocal.Normal := hWlocalNormal
  have hOmegaLocalW : OmegaLocal ≤ Wlocal := by
    apply Subgroup.map_le_iff_le_comap.mp
    rw [hOmegaMap]
    exact hOmegaBZ.trans le_sup_left
  have hclosureWlocal :
      Subgroup.normalClosure (OmegaLocal : Set L₁) ≤ Wlocal :=
    Subgroup.normalClosure_le_normal hOmegaLocalW
  have hclosureW :
      (Subgroup.normalClosure (OmegaLocal : Set L₁)).map L₁.subtype ≤ W := by
    apply Subgroup.map_le_iff_le_comap.mpr
    exact hclosureWlocal
  have htopMap : (⊤ : Subgroup L₁).map L₁.subtype = L₁ :=
    (MonoidHom.range_eq_map L₁.subtype).symm.trans (Subgroup.range_subtype L₁)
  have hmapped := Subgroup.map_mono (f := L₁.subtype) hlocal
  refine hmapped.trans ?_
  rw [Subgroup.map_commutator]
  simpa only [OmegaLocal, V] using
    (Subgroup.commutator_mono hclosureW (htopMap.le.trans hL₁L)).trans hWLcomm

end Stellmacher.SectionTwo

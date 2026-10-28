module
public import ABG.ChapterII.Section3.QCentralLayerMatrixModel
public import ABG.ChapterII.Section3.QFullLinearSourceData
public import ABG.ChapterII.Section3.LinearFullModelComparison
public import ABG.ChapterII.Section3.UnitaryFullModelComparison
public import ABG.ChapterII.Section2.LinearSemidihedralSylow
public import ABG.ChapterII.Section2.LinearWreathedSylow
public import ABG.ChapterII.Section2.UnitarySemidihedralSylow
public import ABG.ChapterII.Section2.UnitaryWreathedSylow

/-!
# The actual matrix constituent at a fixed Q-group decomposition

Fix the Sylow subgroup R, its field two-part and source extension geometry,
and the original projective map f and linear constituent L. For a finite
core-free enlarged Q-group with supplied normal SL2(GF(p^d)) subgroup L0,
L is an actual linear or unitary determinant level, with the corresponding
valid divisibility retained in the stronger endpoint. Its equivalence preserves
the original SL2 matrix identification, through the explicitly supplied eSU
in the unitary branch. The decomposition and eSU are inputs, so eSU may be
chosen after the odd coefficient image of this same f has been determined.
Neither the Sylow nor the projective decomposition is reselected.

If the central quaternion layer fills R, the local/global index equality
makes L the central join Z(R)L0; apply the same-R central model. Otherwise
restrict the original map and exterior element into L, retaining their
kernel and element equations. Transport the same central model across the
actual subgroup restriction and apply the full model comparison. A
semidihedral extension uses determinant level one with the opposite field
sign, while a wreathed extension uses the full field two-part n with the
same sign. The actual matrix Sylow theorems supply each target shape.
Proper quaternion overgroups and fields of orders three and nine remain.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3(ii), article pp26--27.
This completes the matrix-recognition portion of the proposition from its
proved source decomposition and geometry; the odd field action and final
centralizer description are subsequent steps.
-/

namespace ABG
open GorensteinWalter Matrix.GeneralLinearGroup

public theorem qGroup_constituent_matrix_model_with_level
    {H : Type} [Group H] [Finite H] (hH : IsQGroup H) (hOddCore : pPrimeCore 2 H = ⊥)
    (L0 : Subgroup H) [L0.Normal]
    (p d : ℕ) [Fact p.Prime] (hp : Odd p) (hd : d ≠ 0)
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p d))
    (eSU : (unitaryForm 2 p d hd).specialSubgroup ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField p d))
    (R : Sylow 2 H) (n : ℕ) (hn : 2 ≤ n)
    (hfield : (p ^ d % 4 = 1 ∧ 2 ^ n ∣ p ^ d - 1 ∧ Odd ((p ^ d - 1) / 2 ^ n)) ∨
      (p ^ d % 4 = 3 ∧ 2 ^ n ∣ p ^ d + 1 ∧ Odd ((p ^ d + 1) / 2 ^ n)))
    (hgeo : let A := L0.comap (R : Subgroup H).subtype
      (Subgroup.center R ≤ A ∧ Nat.card (Subgroup.center R) = 2 ∧
        (A = ⊤ ∨ (A.index = 2 ∧ Stellmacher.IsSemidihedralGroup R ∧
          ∃ a : R, a ∉ A ∧ a ^ 2 = 1))) ∨
      (∃ r < n, Nat.card (Subgroup.center R) = 2 ^ (r + 1) ∧
        (A ⊔ Subgroup.center R = ⊤ ∨
          (r = n - 1 ∧ (A ⊔ Subgroup.center R).index = 2 ∧ IsWreathedOfHeight R n ∧
            ∃ a : R, a ∉ A ⊔ Subgroup.center R ∧
              Subgroup.zpowers (a ^ 2) = Subgroup.center R))))
    (L : Subgroup H) (hRL : (R : Subgroup H) ≤ L) (hL0L : L0 ≤ L)
    (f : H →* PGammaL2 (GaloisField p d))
    (hfker : f.ker = subgroupCenter (R : Subgroup H))
    (hlinear : L.map f ≤ pGammaL2PGLRange (GaloisField p d))
    (hcore : L0.map f = pGammaL2PSLRange (GaloisField p d))
    (hfcore : ∀ l : L0, f l.val = SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (sl2ProjectiveProjection (GaloisField p d) (eL0 l))))
    (hindex : (subgroupCenter (R : Subgroup H) ⊔ L0).relIndex L =
      (L0.comap (R : Subgroup H).subtype ⊔ Subgroup.center R).index) :
    ∃ m : ℕ,
      (2 ^ m ∣ p ^ d - 1 ∧ ∃ e : L ≃* determinantTwoPower (GaloisField p d) m,
        ∀ l : L0, (e ⟨l.val, hL0L l.property⟩).val = Matrix.SpecialLinearGroup.toGL (eL0 l)) ∨
      (2 ^ m ∣ p ^ d + 1 ∧ ∃ e : L ≃* SU2Level p d hd m,
        ∀ l : L0, (e ⟨l.val, hL0L l.property⟩).val.val = (eSU.symm (eL0 l)).val) := by
  let F := GaloisField p d
  let Z := subgroupCenter (R : Subgroup H)
  let A := L0.comap (R : Subgroup H).subtype
  let M := L0.subgroupOf L
  let e0 : M ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (Subgroup.subgroupOfEquivOfLe hL0L).trans eL0
  let Lin (m : ℕ) : Prop := 2 ^ m ∣ p ^ d - 1 ∧ ∃ e : L ≃* determinantTwoPower F m,
    ∀ l : L0, (e ⟨l.val, hL0L l.property⟩).val = Matrix.SpecialLinearGroup.toGL (eL0 l)
  let Uni (m : ℕ) : Prop := 2 ^ m ∣ p ^ d + 1 ∧ ∃ e : L ≃* SU2Level p d hd m,
    ∀ l : L0, (e ⟨l.val, hL0L l.property⟩).val.val = (eSU.symm (eL0 l)).val
  change ∃ m, Lin m ∨ Uni m
  have hFc : Nat.card F = p ^ d := GaloisField.card p d hd
  have hF : IsOddPrimePower (Nat.card F) := ⟨p, d, Fact.out, hp, by omega, hFc⟩
  have hZc : Z ≤ Subgroup.center H := by
    have h := qGroup_eq_oddCore_mul_sylowCenterCentralizer hH R
    rw [hOddCore, bot_sup_eq] at h
    exact Subgroup.centralizer_eq_top_iff_subset.mp h
  have hZR : Z ≤ (R : Subgroup H) := Subgroup.map_subtype_le _
  have hZL : Z ≤ L := hZR.trans hRL
  have hBL : Z ⊔ L0 ≤ L := sup_le hZL hL0L
  let eZ := (Subgroup.center R).equivMapOfInjective (R : Subgroup H).subtype
    (R : Subgroup H).subtype_injective
  obtain ⟨hCcyc, hCne, _⟩ := qGroup_sylow_center_quotient_geometry hH R
  have hZcyc : IsCyclic Z := eZ.isCyclic.mp hCcyc
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have hc : 1 < Nat.card (Subgroup.center R) := Finite.one_lt_card_iff_nontrivial.mpr hCne
    have hz := Nat.card_congr eZ.toEquiv
    change Nat.card (Subgroup.center R) = Nat.card Z at hz
    rw [hbot, Subgroup.card_bot] at hz
    omega
  have hZtwo : IsPGroup 2 Z :=
    (R.isPGroup'.to_subgroup (Subgroup.center R)).map (R : Subgroup H).subtype
  have hZcard : Nat.card Z = Nat.card (Subgroup.center R) :=
    Subgroup.card_map_of_injective (R : Subgroup H).subtype_injective
  have proper (r : ℕ) (hc : Nat.card (Subgroup.center R) = 2 ^ (r + 1))
      (hAtop : A ⊔ Subgroup.center R = ⊤)
      (hdiv : 2 ^ (r + 1) ∣ p ^ d - 1 ∨ 2 ^ (r + 1) ∣ p ^ d + 1) :
      Lin r ∨ Uni r := by
    have hbi : (Z ⊔ L0).relIndex L = 1 := by rw [hindex, hAtop, Subgroup.index_top]
    have hLeq : L = Z ⊔ L0 := le_antisymm (Subgroup.relIndex_eq_one.mp hbi) hBL
    obtain ⟨hlin, huni⟩ := qGroup_central_layer_matrix_models_at_sylow
      hH hOddCore L0 p d hp hd eL0 eSU R r (hZcard.trans hc)
    rcases hdiv with hdiv | hdiv
    · obtain ⟨e, he, _⟩ := hlin hdiv
      refine Or.inl ⟨(Nat.pow_dvd_pow 2 (Nat.le_succ r)).trans hdiv,
        (MulEquiv.subgroupCongr hLeq).trans e, ?_⟩
      intro l
      exact he l
    · obtain ⟨e, he, _⟩ := huni hdiv
      refine Or.inr ⟨(Nat.pow_dvd_pow 2 (Nat.le_succ r)).trans hdiv,
        (MulEquiv.subgroupCongr hLeq).trans e, ?_⟩
      intro l
      exact he l
  have linearFull (m : ℕ) (hm : 1 ≤ m) (hdiv : 2 ^ m ∣ p ^ d - 1)
      (ho : Odd ((p ^ d - 1) / 2 ^ m))
      (hc : Nat.card (Subgroup.center R) = 2 ^ m)
      (hbi : (Z ⊔ L0).relIndex L = 2)
      (a : R) (ha : a ∉ A ⊔ Subgroup.center R)
      (hasq : (m = 1 ∧ a ^ 2 = 1) ∨
        (2 ≤ m ∧ Subgroup.zpowers (a ^ 2) = Subgroup.center R))
      (T : Sylow 2 (determinantTwoPower F m))
      (hT : Stellmacher.IsSemidihedralGroup T ∨ IsWreathedGroup T)
      (hTc : (Subgroup.center T).map
        ((determinantTwoPower F m).subtype.comp (T : Subgroup _).subtype) ≤
          Subgroup.center (GL (Fin 2) F)) : Lin m := by
    obtain ⟨φ, hφ, _, hφker, hφc, _, hφne, hφp, _, hφ0, _, aL, _, haL, hs1, hs2⟩ :=
      qGroup_full_linear_source_data hF R Z rfl hZc hZcyc hZne hZtwo L L0 hRL hL0L
        eL0 f hfker hlinear hcore hfcore hbi a ha
    have hpred : m - 1 + 1 = m := Nat.sub_add_cancel hm
    obtain ⟨eB, heB, _⟩ := (qGroup_central_layer_matrix_models_at_sylow
      hH hOddCore L0 p d hp hd eL0 eSU R (m - 1)
        (by rw [hpred]; exact hZcard.trans hc)).1 (by simpa only [hpred] using hdiv)
    have heqB : φ.ker ⊔ M = (Z ⊔ L0).subgroupOf L := by
      rw [hφker, ← Subgroup.subgroupOf_sup hZL hL0L]
    let eB' : (φ.ker ⊔ M : Subgroup L) ≃* determinantTwoPower F (m - 1) :=
      ((MulEquiv.subgroupCongr heqB).trans (Subgroup.subgroupOfEquivOfLe hBL)).trans eB
    have heB' (l : M) :
        (eB' ⟨l.val, (show M ≤ φ.ker ⊔ M from le_sup_right) l.property⟩).val =
          Matrix.SpecialLinearGroup.toGL (e0 l) := heB ⟨l.val.val, l.property⟩
    have hs : (m = 1 ∧ aL ^ 2 = 1) ∨ (2 ≤ m ∧ Subgroup.zpowers (aL ^ 2) = φ.ker) := by
      rcases hasq with ⟨h, hs⟩ | ⟨h, hs⟩
      · exact Or.inl ⟨h, hs1 hs⟩
      · exact Or.inr ⟨h, hs2 hs⟩
    obtain ⟨g, e, _, _, _, _, he, _⟩ := exists_linear_full_model_equiv hF φ hφ hφc hφp hφne
      M e0 hφ0 m hm (hFc ▸ hdiv) (hFc ▸ ho) eB' heB' aL haL hs T hT hTc
    refine ⟨hdiv, e, ?_⟩
    intro l
    exact he ⟨⟨l.val, hL0L l.property⟩, l.property⟩
  have unitaryFull (m : ℕ) (hm : 1 ≤ m) (hdiv : 2 ^ m ∣ p ^ d + 1)
      (ho : Odd ((p ^ d + 1) / 2 ^ m))
      (hc : Nat.card (Subgroup.center R) = 2 ^ m)
      (hbi : (Z ⊔ L0).relIndex L = 2)
      (a : R) (ha : a ∉ A ⊔ Subgroup.center R)
      (hasq : (m = 1 ∧ a ^ 2 = 1) ∨
        (2 ≤ m ∧ Subgroup.zpowers (a ^ 2) = Subgroup.center R))
      (T : Sylow 2 (SU2Level p d hd m))
      (hT : Stellmacher.IsSemidihedralGroup T ∨ IsWreathedGroup T)
      (hTc : (Subgroup.center T).map
        ((SU2Level p d hd m).subtype.comp (T : Subgroup _).subtype) ≤
          Subgroup.center (GU2 p d hd)) : Uni m := by
    obtain ⟨φ, hφ, _, hφker, hφc, _, hφne, hφp, _, hφ0, _, aL, _, haL, hs1, hs2⟩ :=
      qGroup_full_linear_source_data hF R Z rfl hZc hZcyc hZne hZtwo L L0 hRL hL0L
        eL0 f hfker hlinear hcore hfcore hbi a ha
    have hpred : m - 1 + 1 = m := Nat.sub_add_cancel hm
    obtain ⟨eB, heB, _⟩ := (qGroup_central_layer_matrix_models_at_sylow
      hH hOddCore L0 p d hp hd eL0 eSU R (m - 1)
        (by rw [hpred]; exact hZcard.trans hc)).2 (by simpa only [hpred] using hdiv)
    have heqB : φ.ker ⊔ M = (Z ⊔ L0).subgroupOf L := by
      rw [hφker, ← Subgroup.subgroupOf_sup hZL hL0L]
    let eB' : (φ.ker ⊔ M : Subgroup L) ≃* SU2Level p d hd (m - 1) :=
      ((MulEquiv.subgroupCongr heqB).trans (Subgroup.subgroupOfEquivOfLe hBL)).trans eB
    have heB' (l : M) :
        (eB' ⟨l.val, (show M ≤ φ.ker ⊔ M from le_sup_right) l.property⟩).val.val =
          (eSU.symm (e0 l)).val := heB ⟨l.val.val, l.property⟩
    have hs : (m = 1 ∧ aL ^ 2 = 1) ∨ (2 ≤ m ∧ Subgroup.zpowers (aL ^ 2) = φ.ker) := by
      rcases hasq with ⟨h, hs⟩ | ⟨h, hs⟩
      · exact Or.inl ⟨h, hs1 hs⟩
      · exact Or.inr ⟨h, hs2 hs⟩
    obtain ⟨g, e, _, _, _, _, he, _⟩ := exists_unitary_full_model_equiv p d hp hd
      φ hφ hφc hφp hφne M e0 eSU hφ0 m hm hdiv ho eB' heB' aL haL hs T hT hTc
    refine ⟨hdiv, e, ?_⟩
    intro l
    exact he ⟨⟨l.val, hL0L l.property⟩, l.property⟩
  rcases hgeo with ⟨hCA, hc, hgeo⟩ | ⟨r, hr, hc, hgeo⟩
  · have hAC : A ⊔ Subgroup.center R = A := sup_eq_left.mpr hCA
    rcases hgeo with hAtop | ⟨hi, hR, a, ha, hasq⟩
    · refine ⟨0, proper 0 (by simpa using hc) (hAC.trans hAtop) ?_⟩
      left
      have hodd : Odd (p ^ d) := hp.pow
      simpa using even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one)
    · have hbi : (Z ⊔ L0).relIndex L = 2 := by rw [hindex, hAC]; exact hi
      have hout : a ∉ A ⊔ Subgroup.center R := by rw [hAC]; exact ha
      rcases hfield with ⟨hmod, hdiv, ho⟩ | ⟨hmod, hdiv, ho⟩
      · have hd2 : 2 ^ 1 ∣ p ^ d + 1 := ⟨2 * (p ^ d / 4) + 1, by omega⟩
        have ho2 : Odd ((p ^ d + 1) / 2 ^ 1) := ⟨p ^ d / 4, by omega⟩
        obtain ⟨T, _, hT, hTc⟩ := SU2Level_semidihedral_sylow p d hp hd n hn hdiv ho
        exact ⟨1, Or.inr (unitaryFull 1 (by omega) hd2 ho2 (by simpa using hc) hbi a hout
          (Or.inl ⟨rfl, hasq⟩) T (Or.inl hT) hTc)⟩
      · have hd2 : 2 ^ 1 ∣ Nat.card F - 1 := by
          rw [hFc]
          exact ⟨2 * (p ^ d / 4) + 1, by omega⟩
        have ho2 : Odd ((Nat.card F - 1) / 2 ^ 1) := by
          rw [hFc]
          exact ⟨p ^ d / 4, by omega⟩
        obtain ⟨T, _, hT, hTc⟩ := determinantTwoPower_semidihedral_sylow F p n hn
          (hFc ▸ hdiv) (hFc ▸ ho)
        exact ⟨1, Or.inl (linearFull 1 (by omega) (hFc ▸ hd2) (hFc ▸ ho2)
          (by simpa using hc) hbi a hout (Or.inl ⟨rfl, hasq⟩) T (Or.inl hT) hTc)⟩
  · rcases hgeo with hAtop | ⟨hrn, hi, hR, a, ha, hasq⟩
    · have hpow : 2 ^ (r + 1) ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
      refine ⟨r, proper r hc hAtop ?_⟩
      rcases hfield with hminus | hplus
      · exact Or.inl (hpow.trans hminus.2.1)
      · exact Or.inr (hpow.trans hplus.2.1)
    · have hbi : (Z ⊔ L0).relIndex L = 2 := hindex.trans hi
      have hcn : Nat.card (Subgroup.center R) = 2 ^ n := by
        rw [hc, hrn, Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rcases hfield with ⟨hmod, hdiv, ho⟩ | ⟨hmod, hdiv, ho⟩
      · obtain ⟨T, hT, hTc⟩ := determinantTwoPower_wreathed_sylow F n hn (hFc ▸ hdiv) (hFc ▸ ho)
        exact ⟨n, Or.inl (linearFull n (by omega) hdiv ho hcn hbi a ha
          (Or.inr ⟨hn, hasq⟩) T (Or.inr ⟨n, hT⟩) hTc)⟩
      · obtain ⟨T, hT, hTc⟩ := SU2Level_wreathed_sylow p d hp hd n hn hdiv ho
        exact ⟨n, Or.inr (unitaryFull n (by omega) hdiv ho hcn hbi a ha
          (Or.inr ⟨hn, hasq⟩) T (Or.inr ⟨n, hT⟩) hTc)⟩

public theorem qGroup_constituent_matrix_model
    {H : Type} [Group H] [Finite H] (hH : IsQGroup H) (hOddCore : pPrimeCore 2 H = ⊥)
    (L0 : Subgroup H) [L0.Normal]
    (p d : ℕ) [Fact p.Prime] (hp : Odd p) (hd : d ≠ 0)
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p d))
    (eSU : (unitaryForm 2 p d hd).specialSubgroup ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField p d))
    (R : Sylow 2 H) (n : ℕ) (hn : 2 ≤ n)
    (hfield : (p ^ d % 4 = 1 ∧ 2 ^ n ∣ p ^ d - 1 ∧ Odd ((p ^ d - 1) / 2 ^ n)) ∨
      (p ^ d % 4 = 3 ∧ 2 ^ n ∣ p ^ d + 1 ∧ Odd ((p ^ d + 1) / 2 ^ n)))
    (hgeo : let A := L0.comap (R : Subgroup H).subtype
      (Subgroup.center R ≤ A ∧ Nat.card (Subgroup.center R) = 2 ∧
        (A = ⊤ ∨ (A.index = 2 ∧ Stellmacher.IsSemidihedralGroup R ∧
          ∃ a : R, a ∉ A ∧ a ^ 2 = 1))) ∨
      (∃ r < n, Nat.card (Subgroup.center R) = 2 ^ (r + 1) ∧
        (A ⊔ Subgroup.center R = ⊤ ∨
          (r = n - 1 ∧ (A ⊔ Subgroup.center R).index = 2 ∧ IsWreathedOfHeight R n ∧
            ∃ a : R, a ∉ A ⊔ Subgroup.center R ∧
              Subgroup.zpowers (a ^ 2) = Subgroup.center R))))
    (L : Subgroup H) (hRL : (R : Subgroup H) ≤ L) (hL0L : L0 ≤ L)
    (f : H →* PGammaL2 (GaloisField p d))
    (hfker : f.ker = subgroupCenter (R : Subgroup H))
    (hlinear : L.map f ≤ pGammaL2PGLRange (GaloisField p d))
    (hcore : L0.map f = pGammaL2PSLRange (GaloisField p d))
    (hfcore : ∀ l : L0, f l.val = SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (sl2ProjectiveProjection (GaloisField p d) (eL0 l))))
    (hindex : (subgroupCenter (R : Subgroup H) ⊔ L0).relIndex L =
      (L0.comap (R : Subgroup H).subtype ⊔ Subgroup.center R).index) :
    ∃ m : ℕ,
      (∃ e : L ≃* determinantTwoPower (GaloisField p d) m,
        ∀ l : L0, (e ⟨l.val, hL0L l.property⟩).val = Matrix.SpecialLinearGroup.toGL (eL0 l)) ∨
      (∃ e : L ≃* SU2Level p d hd m,
        ∀ l : L0, (e ⟨l.val, hL0L l.property⟩).val.val = (eSU.symm (eL0 l)).val) := by
  obtain ⟨m, hmodel⟩ := qGroup_constituent_matrix_model_with_level hH hOddCore L0 p d hp hd
    eL0 eSU R n hn hfield hgeo L hRL hL0L f hfker hlinear hcore hfcore hindex
  refine ⟨m, ?_⟩
  rcases hmodel with ⟨_, hmodel⟩ | ⟨_, hmodel⟩
  · exact Or.inl hmodel
  · exact Or.inr hmodel


end ABG

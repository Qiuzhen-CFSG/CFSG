module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianNormalizer
public import Theory.GroupTheory.IrreducibleSmallSections

/-!
# The original residual-fixed four-group

The literal irreducible center quotient has order four. An involution fixed
by L₀ therefore lies in its denominator, giving C_I(L₀) ≤ C_I(Z(U)^g).
The restricted parabolic preserves E = V₂C_I(L₀), and the displacement of
its two-residual on E lies in C_I(L₀), because I meets the seed trivially.
That displacement is nonzero and fully moved; it cannot have order two.
The known order-four upper bound now proves equality of the two fixed
subgroups, as well as [E,O²(P)] = C_I(Z(U)^g) and irreducibility there.

The last theorem constructs all these data on the same original flag and
natural constituent. The original I₂ also preserves E and has displacement
inside V₂. Centralization by I₂, normality of its action in the joined
ambient action, and the final contradiction are not asserted here. In
particular, this proof does not use the doubtful equality between the
returning-center commutator and its fixed subgroup.

Source: Aschbacher--Smith, proof of 12.9.4, printed p.860 of
refs/quasithin.pdf; the parabolic is lifted inside the original K₁T.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Every L₀-fixed point of the same chosen constituent is fixed by the
returning center. Irreducibility is used on the literal central quotient. -/
theorem nonabelian_caseFive_planeResidual_fixed_le_returning
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hiZ : I ≤ F.ZU) :
    I ⊓ centralizer (planeCentralizerResidual F L : Set G) ≤
      I ⊓ centralizer (conjugate F.ZU g : Set G) := by
  let := c.elementary
  let K := F.ZU ⊓ centralizer (conjugate F.ZU g : Set G)
  have he := nonabelian_caseFive_center_centralizer h (.inl rfl) earlier F hne g hgP hgH B h5
  have hi := nonabelian_caseFive_center_centralizer_index h (.inl rfl) earlier F hne g hgP hgH B h5
  have hirr : ∀ A : Subgroup G, K ≤ A → A ≤ F.ZU →
      planeCentralizerResidual F L ≤ normalizer (A : Set G) → A = K ∨ A = F.ZU := by
    rw [show K = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 from he]
    exact nonabelian_caseFive_center_quotient_irreducible h (.inl rfl) earlier F hne g hgP hgH B h5
  rintro x ⟨hxi,hxc⟩
  have hxK := fixed_mem_of_irreducible_abelian_section F.ZU K
    (planeCentralizerResidual F L) inf_le_left
    (nonabelian_planeResidual_normalizes_center_centralizer h earlier F g hgP)
    hirr (hiZ hxi) hxc (by decide : 0 < 2)
    (elemPow_eq_one_of_isElementaryAbelian x hxi)
    (by rw [hi]; decide)
  exact ⟨hxi,hxK.2⟩

private theorem plane_extension_inf_constituent
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    (C : ComponentGeometry F L) {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hnatural : NaturalModule c 4) (hiZ : I ≤ F.ZU)
    {A : Subgroup G} (hAI : A ≤ I) : (F.Vi 2 ⊔ A) ⊓ I = A := by
  have hAV : A ≤ normalizer (F.Vi 2 : Set G) :=
    ((hAI.trans hiZ).trans ((centerIn_le_centralizer F.U).trans
      (centralizer_le ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hd := nonabelian_caseFive_chosen_disjoint_seed h F hne C c hnatural hiZ
  apply le_antisymm ?_ (le_inf le_sup_right hAI)
  rintro x ⟨hx,hxi⟩
  have hm : x ∈ (F.Vi 2 : Set G) * (A : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hAV]
    exact hx
  obtain ⟨a,ha,b,hb,he⟩ := hm
  have hai : a ∈ I := by
    have hh := I.mul_mem hxi (I.inv_mem (hAI hb))
    simpa only [←he,mul_inv_cancel_right] using hh
  have ha1 : a = 1 := hd.le_bot ⟨hai,F.le_seed 2 ha⟩
  change a * b = x at he
  rw [ha1,one_mul] at he
  exact he ▸ hb

/-- The L₀-fixed plane extension has nonzero fully moved displacement
inside its fixed constituent. In particular that constituent has order at
least four; an order-two error would be fixed by the whole parabolic. -/
theorem nonabelian_caseFive_planeResidual_fixed_displacement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hnatural : NaturalModule c 4) (hiZ : I ≤ F.ZU) (hi : I = ⁅F.ZU,C.K1⁆) :
    let A := I ⊓ centralizer (planeCentralizerResidual F L : Set G)
    let E := F.Vi 2 ⊔ A
    let R := componentPlaneResidual F C v
    ⁅E,R⁆ ≤ A ∧ ⁅⁅E,R⁆,R⁆ = ⁅E,R⁆ ∧ 4 ≤ Nat.card (⁅E,R⁆ : Subgroup G) := by
  let A := I ⊓ centralizer (planeCentralizerResidual F L : Set G)
  let E := F.Vi 2 ⊔ A
  let P := componentPlanePreimage F C v
  let R := componentPlaneResidual F C v
  let J := ⁅E,R⁆
  change J ≤ A ∧ ⁅J,R⁆ = J ∧ 4 ≤ Nat.card J
  obtain ⟨_,hPA,hPE⟩ := nonabelian_caseFive_component_plane_fixed_nontrivial
    h earlier F hne g hgP hgH B h5 C v hv hline c hiZ hi
  have hRP : R ≤ P := map_subtype_le _
  have hRI : ⁅E,R⁆ ≤ I :=
    (commutator_mono (sup_le_sup_left (show A ≤ I from inf_le_left) _) le_rfl).trans
      (componentPlanePreimage_normalizes_natural_extension h earlier F C v hv hline c hiZ hi).2
  have hJA : J ≤ A := by
    rw [←plane_extension_inf_constituent h F hne C c hnatural hiZ (show A ≤ I from inf_le_left)]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp (hRP.trans hPE)) hRI
  let := (nonabelian_caseFive_plane_extension_card h F hne C c hnatural hiZ
    (show A ≤ I from inf_le_left)).1
  have hid : ⁅J,R⁆ = J := commutator_isPPerfect_idempotent R E
    (isPPerfect_embedded_pResidual 2 P) (IsElementaryAbelian.isPGroup 2 E) (hRP.trans hPE)
  have hPJ : P ≤ normalizer (J : Set G) := by
    have hPR : P ≤ normalizer (R : Set G) := P.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (pResidual 2 P))
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hPE ha),mem_normalizer_iff_map_conj_eq.mp (hPR ha)]
  have hJne : J ≠ ⊥ := by
    intro hz
    apply (nonabelian_caseFive_component_displacement_moves h earlier F hne g hgP hgH
      B h5 C v hv hline hi).1
    exact (commutator_mono (show F.Vi 2 ≤ E from le_sup_left) le_rfl).trans (hz.le.trans bot_le)
  have hcard2 : Nat.card J ≠ 2 := by
    intro hj
    have hc : R ≤ centralizer (J : Set G) :=
      (hRP.trans hPJ).trans (normalizer_le_centralizer_of_card_two J hj)
    exact hJne (hid.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)))
  let := c.elementary
  obtain ⟨k,hk⟩ := ((IsElementaryAbelian.isPGroup 2 I).to_le (hJA.trans inf_le_left)).exists_card_eq
  change Nat.card J = 2 ^ k at hk
  have hlo : 1 < Nat.card J := (one_lt_card_iff_ne_bot J).mpr hJne
  have hk2 : 2 ≤ k := by
    by_contra! hh
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · exact (Nat.ne_of_gt hlo) (by simpa only [pow_zero] using hk)
    · exact hcard2 (by simpa only [pow_one] using hk)
  refine ⟨hJA,hid,?_⟩
  rw [hk]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk2

/-- The original L₀-fixed subgroup is exactly the returning-center fixed
four-group. The proof uses the actual parabolic motion and the literal
irreducible center quotient, without a commutator-equals-fixed-space claim. -/
theorem nonabelian_caseFive_planeResidual_fixed_eq_returning
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hnatural : NaturalModule c 4) (hiZ : I ≤ F.ZU) (hi : I = ⁅F.ZU,C.K1⁆) :
    I ⊓ centralizer (planeCentralizerResidual F L : Set G) =
      I ⊓ centralizer (conjugate F.ZU g : Set G) ∧
    Nat.card (I ⊓ centralizer (planeCentralizerResidual F L : Set G) : Subgroup G) = 4 ∧
    ⁅F.Vi 2 ⊔ (I ⊓ centralizer (conjugate F.ZU g : Set G)),componentPlaneResidual F C v⁆ =
      I ⊓ centralizer (conjugate F.ZU g : Set G) := by
  let A := I ⊓ centralizer (planeCentralizerResidual F L : Set G)
  let D := I ⊓ centralizer (conjugate F.ZU g : Set G)
  let J := ⁅F.Vi 2 ⊔ A,componentPlaneResidual F C v⁆
  have hAD : A ≤ D := nonabelian_caseFive_planeResidual_fixed_le_returning
    h earlier F hne g hgP hgH B h5 C c hiZ
  obtain ⟨hJA,_,h4J⟩ := nonabelian_caseFive_planeResidual_fixed_displacement
    h earlier F hne g hgP hgH B h5 C v hv hline c hnatural hiZ hi
  have hcI : Nat.card I = 16 := by
    let := c.elementary
    obtain ⟨m⟩ := hnatural
    calc
      Nat.card I = Nat.card (Additive I) := rfl
      _ = Nat.card (Fin 4 → ZMod 2) := Nat.card_congr m.coordinates.toEquiv
      _ = 16 := by rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]; decide
  have hcD : Nat.card D = 4 := by
    have hh := (D.subgroupOf I).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show D ≤ I from inf_le_left)).toEquiv] at hh
    change Nat.card D * D.relIndex I = Nat.card I at hh
    rw [nonabelian_caseFive_chosen_centralizer_index h earlier F hne g hgP hgH B h5 C c hiZ,hcI] at hh
    omega
  have h4A : 4 ≤ Nat.card A := h4J.trans (card_le_of_le hJA)
  have hAc : Nat.card A = 4 := Nat.le_antisymm ((card_le_of_le hAD).trans_eq hcD) h4A
  have hAD' : A = D := eq_of_le_of_card_ge hAD (by rw [hAc,hcD])
  have hJA' : J = A := eq_of_le_of_card_ge hJA (by rw [hAc]; exact h4J)
  refine ⟨hAD',hAc,?_⟩
  change ⁅F.Vi 2 ⊔ D,componentPlaneResidual F C v⁆ = D
  rw [←hAD']
  exact hJA'

/-- The restricted two-residual acts irreducibly on the same returning
fixed four-group. This is the actual action on the original subgroup. -/
theorem nonabelian_caseFive_returning_fixed_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hnatural : NaturalModule c 4) (hiZ : I ≤ F.ZU) (hi : I = ⁅F.ZU,C.K1⁆) :
    ∀ A : Subgroup G, A ≤ I ⊓ centralizer (conjugate F.ZU g : Set G) →
      componentPlaneResidual F C v ≤ normalizer (A : Set G) →
      A = ⊥ ∨ A = I ⊓ centralizer (conjugate F.ZU g : Set G) := by
  obtain ⟨he,hc,hcomm⟩ := nonabelian_caseFive_planeResidual_fixed_eq_returning
    h earlier F hne g hgP hgH B h5 C v hv hline c hnatural hiZ hi
  obtain ⟨_,hid,_⟩ := nonabelian_caseFive_planeResidual_fixed_displacement
    h earlier F hne g hgP hgH B h5 C v hv hline c hnatural hiZ hi
  obtain ⟨_,hPD,_⟩ := nonabelian_caseFive_component_plane_fixed_nontrivial
    h earlier F hne g hgP hgH B h5 C v hv hline c hiZ hi
  rw [he,hcomm] at hid
  rw [he] at hc hPD
  exact four_irreducible_of_twoPerfect_moved _ _
    (isPPerfect_embedded_pResidual 2 (componentPlanePreimage F C v)) hc
    ((map_subtype_le _).trans hPD) hid

/-- The fixed-space identification applies to the same original flag and
chosen natural constituent. Both original actors preserve its elementary
plane extension; the component residual moves exactly the fixed four-group. -/
theorem nonabelian_caseFive_natural_fixed_geometry
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ∃ (v : Additive F.Uhat) (C : ComponentGeometry F L) (I : Subgroup G)
      (c : ChosenModule T C.K1 I),
      v ≠ 0 ∧ hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
      NaturalModule c 4 ∧ I ≤ F.ZU ∧ I = ⁅F.ZU,C.K1⁆ ∧ Nat.card I = 16 ∧
      let D := I ⊓ centralizer (conjugate F.ZU g : Set G)
      let E := F.Vi 2 ⊔ D
      I ⊓ centralizer (planeCentralizerResidual F L : Set G) = D ∧
      Nat.card D = 4 ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 16 ∧
      Disjoint (F.Vi 2) D ∧
      componentPlanePreimage F C v ≤ normalizer (D : Set G) ∧
      componentPlanePreimage F C v ≤ normalizer (E : Set G) ∧
      ⁅E,componentPlaneResidual F C v⁆ = D ∧
      (∀ A : Subgroup G, A ≤ D → componentPlaneResidual F C v ≤ normalizer (A : Set G) →
        A = ⊥ ∨ A = D) ∧
      ⁅E,F.I₂ L⁆ ≤ F.Vi 2 ∧ F.I₂ L ≤ normalizer (E : Set G) ∧
      ¬ componentPlanePreimage F C v ≤ F.Gi 2 := by
  obtain ⟨v,C,I,c,hv,hline,hnat,hiZ,hi,hcard,_,_,_,hPD,hPE⟩ :=
    nonabelian_caseFive_natural_normalizer_geometry modules h preferred earlier four
      F hne g hgP hgH B h5
  obtain ⟨he,hc,hcomm⟩ := nonabelian_caseFive_planeResidual_fixed_eq_returning
    h earlier F hne g hgP hgH B h5 C v hv hline c hnat hiZ hi
  rw [he] at hc hPD hPE
  obtain ⟨hE,hEc⟩ := nonabelian_caseFive_plane_extension_card h F hne C c hnat hiZ
    (show I ⊓ centralizer (conjugate F.ZU g : Set G) ≤ I from inf_le_left)
  rw [hc] at hEc
  refine ⟨v,C,I,c,hv,hline,hnat,hiZ,hi,hcard,he,hc,hE,hEc,?_,hPD,hPE,hcomm,?_,?_,?_,?_⟩
  · exact (nonabelian_caseFive_chosen_disjoint_seed h F hne C c hnat hiZ).symm.mono
      (F.le_seed 2) inf_le_left
  · exact nonabelian_caseFive_returning_fixed_irreducible
      h earlier F hne g hgP hgH B h5 C v hv hline c hnat hiZ hi
  · exact (nonabelian_caseFive_returning_fixed_extension h (.inl rfl) earlier F hne g hgP hgH B h5 hiZ).1
  · exact (nonabelian_caseFive_returning_fixed_extension h (.inl rfl) earlier F hne g hgP hgH B h5 hiZ).2
  · exact nonabelian_caseFive_componentPlanePreimage_not_le_plane h earlier F hne g hgP hgH
      B h5 C v hv hline

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components

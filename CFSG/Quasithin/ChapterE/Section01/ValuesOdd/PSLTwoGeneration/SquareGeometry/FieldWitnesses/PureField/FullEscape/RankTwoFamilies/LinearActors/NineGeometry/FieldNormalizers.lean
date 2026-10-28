module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry.Inputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.SmallField
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed
public import GorensteinWalter.PGL2InnerAction

/-!
# Inner four-group normalizers are field-involution centralizers over F₉

The actual comparison PSL₂(F) ≃ A₆ and the faithful, surjective semilinear
conjugation action give an isomorphism PΓL₂(F) ≃ Aut(A₆). Its compatibility
with the canonical PSL₂ embedding is proved explicitly. The A₆ four-group
calculation supplies an outer involution centralizing the full normalizer,
and computes that normalizer's order as 48.

The lifted involution has nontrivial field coordinate: otherwise the
self-centralizing property of four-groups in PGL₂ would make it inner.
Projective descent computes its centralizer's order as 48, proving equality
of the actual subgroups. This discharges `FourNormalizerField`, the field
involution input to `NineGeometry.nineFieldPlacement_of_normalizers`.

Source: Aschbacher–Smith, E.1.2 and E.1.14(6), printed pp.209–210 and 214,
citing Aschbacher (1982), Lemma 4.10. The exceptional comparison is the
attributed ATLAS port in `Theory.AtlasPort.ExceptionalIsomorphisms.Order360`;
see its source notice and `LICENSES/ATLAS.txt`.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry
open AlternatingSix.ShadowLocal
variable {F : Type*} [Field F] [Finite F]

omit [Field F] [Finite F] in
private theorem nine_odd (hF : Nat.card F = 3 ^ 2) : IsOddPrimePower (Nat.card F) :=
  ⟨3, 2, Nat.prime_three, by decide, by decide, hF⟩

omit [Field F] [Finite F] in
private theorem nine_large (hF : Nat.card F = 3 ^ 2) : 3 < Nat.card F := by
  rw [hF]; decide

private noncomputable def semilinearEquiv (hF : Nat.card F = 3 ^ 2) :
    PGammaL2 F ≃* AutA6 :=
  (MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 F (nine_odd hF) (nine_large hF))
    ⟨pGammaL2ToMulAutPSL2_injective F (nine_odd hF) (nine_large hF),
      pGammaL2ToMulAutPSL2_surjective F hF (nine_odd hF) (nine_large hF)⟩).trans
    (MulAut.congr (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hF))

private theorem semilinearEquiv_inner (hF : Nat.card F = 3 ^ 2) (y : PSL2 F) :
    semilinearEquiv hF (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y)) =
      MulAut.conj (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hF y) := by
  change MulAut.congr _ (pGammaL2ToMulAutPSL2 F (nine_odd hF) (nine_large hF)
    (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y))) = _
  rw [pGammaL2ToMulAutPSL2_inl, pgl2InnerAutPSL2_toPGL]
  ext z
  simp [MulAut.congr, MulAut.conj_apply]

private theorem map_singleton_centralizer {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G) :
    (centralizer ({x} : Set G)).map e.toMonoidHom = centralizer ({e x} : Set H) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e z * e x = e x * e z
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hz)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy

private theorem field_centralizer_card (hF : Nat.card F = 3 ^ 2)
    (x : PGammaL2 F) (hx : orderOf x = 2) (hf : x.right ≠ 1) :
    Nat.card (centralizer ({x} : Set (PGammaL2 F))) = 48 := by
  obtain ⟨c, hc⟩ := projective_semilinear_involution_conj_inr (nine_odd hF) x hx hf
  let a := MulAut.conj (SemidirectProduct.inl c : PGammaL2 F)⁻¹
  have ha : a x = SemidirectProduct.inr x.right := by
    simpa [a, MulAut.conj_apply] using hc
  have hsq : x.right ^ 2 = 1 := by
    change (SemidirectProduct.rightHom x) ^ 2 = 1
    have hh := congrArg (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F))
      (show x ^ 2 = 1 by simpa only [hx] using pow_orderOf_eq_one x)
    simpa only [map_pow, map_one] using hh
  have hmap := map_singleton_centralizer a x
  rw [ha] at hmap
  rw [← card_map_of_injective (f := a.toMonoidHom) a.injective, hmap,
    Nat.card_congr (smallFieldCentralizerEquiv hF x.right hsq hf).toEquiv,
    Nat.card_prod, FiniteField.card_ringAut_of_card_prime_pow Nat.prime_three hF]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem aut_normalizer_le_centralizer
    (A : Subgroup A6) (τ : AutA6)
    (hfix : ∀ g ∈ normalizer (A : Set A6), τ g = g)
    (hN : normalizer (A.map (MulAut.conj : A6 →* AutA6) : Set AutA6) =
      (normalizer (A : Set A6)).map (MulAut.conj : A6 →* AutA6) ⊔ zpowers τ) :
    normalizer (A.map (MulAut.conj : A6 →* AutA6) : Set AutA6) ≤
      centralizer ({τ} : Set AutA6) := by
  rw [hN]
  apply sup_le
  · rintro _ ⟨g, hg, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := aut_conj_inner τ g
    rw [hfix g hg, mul_inv_eq_iff_eq_mul] at hh
    exact hh.symm
  · apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr rfl

variable [Finite (PGammaL2 F)]

/-- Every inner four-group has full normalizer equal to the centralizer
of a genuine field involution, with no prescribed Sylow or placement premise. -/
theorem fourNormalizerField (hF : Nat.card F = 3 ^ 2) : FourNormalizerField F := by
  intro B hB hBL
  let i : PGL2 F →* PGammaL2 F := SemidirectProduct.inl
  let j : PSL2 F →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL
  let B₀ := B.comap j
  have hj : Function.Injective j := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hBmap : B₀.map j = B := map_comap_eq_self hBL
  let eB : B₀ ≃* B := (B₀.equivMapOfInjective j hj).trans (MulEquiv.subgroupCongr hBmap)
  have hB₀ : IsKleinFour B₀ := {
    card_four := (Nat.card_congr eB.toEquiv).trans hB.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eB).trans hB.exponent_two }
  let e₀ := Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hF
  let A := B₀.map e₀.toMonoidHom
  let : IsKleinFour A := isKleinFour_map_of_injective B₀ hB₀ e₀.toMonoidHom e₀.injective
  let e := semilinearEquiv hF
  have hmarked : (B.map i).map e.toMonoidHom = A.map (MulAut.conj : A6 →* AutA6) := by
    rw [← hBmap, map_map, map_map]
    change B₀.map _ = (B₀.map e₀.toMonoidHom).map (MulAut.conj : A6 →* AutA6)
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro y
    exact semilinearEquiv_inner hF y
  let N := normalizer (B.map i : Set (PGammaL2 F))
  have hNmap : N.map e.toMonoidHom =
      normalizer (A.map (MulAut.conj : A6 →* AutA6) : Set AutA6) := by
    rw [map_equiv_normalizer_eq, hmarked]
  obtain ⟨τ, hτ, houter, hfix, hN, _⟩ := FourNormalizers.exists_outer_complement A
  let x := e.symm τ
  have hex : e x = τ := e.apply_symm_apply τ
  have hx : orderOf x = 2 := (e.symm.orderOf_eq τ).trans hτ
  have hNC : N ≤ centralizer ({x} : Set (PGammaL2 F)) := by
    intro n hn
    have hn' : e n ∈ normalizer (A.map (MulAut.conj : A6 →* AutA6) : Set AutA6) := by
      rw [← hNmap]
      exact mem_map_of_mem _ hn
    have hc := mem_centralizer_singleton_iff.mp
      (aut_normalizer_le_centralizer A τ hfix hN hn')
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, hex] using hc
  have hf : x.right ≠ 1 := by
    intro hr
    have hxi : i x.left = x := by
      apply SemidirectProduct.ext
      · rfl
      · exact hr.symm
    have hxc : x.left ∈ centralizer (B : Set (PGL2 F)) := by
      apply mem_centralizer_iff.mpr
      intro b hb
      have hc := mem_centralizer_singleton_iff.mp
        (hNC (le_normalizer (mem_map_of_mem i hb)))
      rw [← hxi, ← map_mul, ← map_mul] at hc
      exact SemidirectProduct.inl_injective hc
    rw [pgl2_kleinFour_centralizer_eq_self F (nine_odd hF) B hB] at hxc
    obtain ⟨y, hy⟩ := hBL hxc
    apply houter
    refine ⟨e₀ y, ?_⟩
    change MulAut.conj (e₀ y) = τ
    rw [← semilinearEquiv_inner hF y]
    change e (i (j y)) = τ
    rw [hy, hxi, hex]
  have hcardN : Nat.card N = 48 := by
    rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, hNmap]
    exact FourNormalizers.aut_normalizer_card
      (fun σ hσ => ⟨swapFixedEquiv σ hσ⟩) A
  refine ⟨x, hx, hf, ?_⟩
  exact (eq_of_le_of_card_ge hNC (by rw [hcardN, field_centralizer_card hF x hx hf])).symm

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry

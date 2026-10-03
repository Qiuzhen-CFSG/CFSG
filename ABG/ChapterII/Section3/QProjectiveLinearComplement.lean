module
public import ABG.ChapterII.Section3.QSylowGeometry
public import ABG.ChapterII.Section3.SylowCenter
public import ABG.ChapterII.Section3.CoreFreeCentralQuotient
public import ABG.ChapterII.Section3.CentralSylowDihedralQuotient
public import GorensteinWalter.NormalSL2ProjectiveImage
public import GorensteinWalter.NormalPSL2Semilinear
public import GorensteinWalter.PGammaL2PureFieldComplement
public import GorensteinWalter.PGammaL2OuterAbelian
public import Theory.GroupTheory.CentralTwoComplementLift

/-!
# The prescribed projective linear and field decomposition of a Q-group

For a finite enlarged Q-group H with trivial odd core and a supplied normal
SL2(K) subgroup L0, the center Z of any Sylow two-subgroup is central, cyclic,
nontrivial and a two-group. There is an actual homomorphism H to PGammaL2(K)
with kernel Z which sends L0 onto the canonical PSL2 layer. The inverse image
L of the linear layer has a cyclic odd-order complement E. Their images are
respectively the actual linear intersection and the pure coefficient image.
Moreover Z L0 has relative index dividing two in L and contains H's derived
subgroup. All enlarged Q cases and the fields of orders three and nine remain.

Proposition 1 makes the Sylow center central, and the enlarged-Q geometry
makes its quotient dihedral. The normal SL2 quotient calculation and the
prescribed-field semilinear embedding identify the supplied PSL2 core over
the same K. Split the actual range by its pure field subgroup, then lift that
odd cyclic complement through the central two-kernel. Map/comap identities
preserve the three required images. The PSL2/PGL2 index formula and abelian
outer quotient give the index and derived-subgroup bounds.

This is the projective decomposition and central lifting step in ABG II.3
Proposition 3, article pages 25--27. Matrix-level recognition, the lifted
coefficient action, and the odd-core centralizer description are subsequent
steps and are not assumptions of this theorem.
-/

namespace ABG
open GorensteinWalter
universe u

public theorem qGroup_projective_linear_complement_with_core_map
    {H : Type u} [Group H] [Finite H] (hH : IsQGroup H)
    (hcore : pPrimeCore 2 H = ⊥) (S : Sylow 2 H)
    (Z : Subgroup H) [Z.Normal] (hZ : Z = subgroupCenter (S : Subgroup H))
    (L0 : Subgroup H) [L0.Normal]
    (K : Type u) [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    Z ≤ Subgroup.center H ∧ IsCyclic Z ∧ Z ≠ ⊥ ∧ IsPGroup 2 Z ∧
      ∃ (f : H →* PGammaL2 K) (L E : Subgroup H),
        f.ker = Z ∧ L.Normal ∧ L0 ≤ L ∧ L.IsComplement' E ∧
        IsCyclic E ∧ Odd (Nat.card E) ∧
        L.map f = f.range ⊓ pGammaL2PGLRange K ∧
        L0.map f = pGammaL2PSLRange K ∧
        E.map f = (pGammaL2FieldProjection K f.range).range.map
          (SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K) ∧
        (Z ⊔ L0).relIndex L ∣ 2 ∧ commutator H ≤ Z ⊔ L0 ∧
        ∀ l : L0, f l.val = SemidirectProduct.inl
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (sl2ProjectiveProjection K (eL0 l))) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZcentral : Z ≤ Subgroup.center H := by
    have h := qGroup_eq_oddCore_mul_sylowCenterCentralizer hH S
    rw [hcore, bot_sup_eq] at h
    rw [hZ]
    exact Subgroup.centralizer_eq_top_iff_subset.mp h
  obtain ⟨hcyc, hne, hmodel⟩ := qGroup_sylow_center_quotient_geometry hH S
  let : Nontrivial (Subgroup.center S) := hne
  let eZ : Subgroup.center S ≃* Z :=
    (Subgroup.equivMapOfInjective _ (S : Subgroup H).subtype
      (S : Subgroup H).subtype_injective).trans (MulEquiv.subgroupCongr hZ.symm)
  have hZcyc : IsCyclic Z := eZ.isCyclic.mp hcyc
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have hn : Nontrivial Z := eZ.injective.nontrivial
    have hc : 1 < Nat.card Z := Finite.one_lt_card_iff_nontrivial.mpr hn
    rw [hbot, Subgroup.card_bot] at hc
    omega
  have hZtwo : IsPGroup 2 Z :=
    (S.isPGroup'.to_subgroup (Subgroup.center S)).of_equiv eZ
  let q := QuotientGroup.mk' Z
  have hq := QuotientGroup.mk'_surjective Z
  let N := L0.map q
  have hNN : N.Normal := Subgroup.Normal.map inferInstance q hq
  let : N.Normal := hNN
  obtain ⟨eN, heN⟩ := exists_normal_sl2_projective_image S Z L0 hZcentral hZ.symm.le K hK eL0
  have hdih := hasDihedralSylowTwo_quotient_sylow_center_of_model S Z hZ hmodel
  have hquotcore := oddCore_quotient_eq_bot_of_central_two_subgroup Z hZcentral hZtwo hcore
  obtain ⟨g, hg, hgN, hgodd⟩ :=
    exists_normal_psl2_semilinear_embedding hdih hquotcore N K hK eN
  let f : H →* PGammaL2 K := g.comp q
  have hfcore (l : L0) : f l.val = SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (sl2ProjectiveProjection K (eL0 l))) := by
    have h := hgN ⟨q l.val, ⟨l.val, l.property, rfl⟩⟩
    rw [heN l] at h
    exact h
  have hfker : f.ker = Z := by
    ext x
    change g (q x) = 1 ↔ x ∈ Z
    rw [← g.map_one, hg.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hfrange : f.range = g.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hq, ← MonoidHom.range_eq_map]
  have hL0map : L0.map f = pGammaL2PSLRange K := by
    have hNmap : N.map g = pGammaL2PSLRange K := by
      ext y
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨eN ⟨n, hn⟩, (hgN ⟨n, hn⟩).symm⟩
      · rintro ⟨a, rfl⟩
        refine ⟨eN.symm a, (eN.symm a).property, ?_⟩
        change g (eN.symm a) = SemidirectProduct.inl
          (Matrix.ProjectiveSpecialLinearGroup.toPGL a)
        simpa only [eN.apply_symm_apply] using hgN (eN.symm a)
    change (L0.map q).map g = _ at hNmap
    rw [Subgroup.map_map] at hNmap
    exact hNmap
  have hPSL : pGammaL2PSLRange K ≤ f.range := by
    rw [← hL0map]
    exact L0.map_le_range f
  have hodd : Odd (Nat.card (pGammaL2FieldProjection K f.range).range) := by
    rw [hfrange]
    exact hgodd
  let A := f.range
  let φ : H →* A := f.rangeRestrict
  have hφ : Function.Surjective φ := f.rangeRestrict_surjective
  let : Finite A := Finite.of_surjective φ hφ
  have hφker : φ.ker = Z := (MonoidHom.ker_rangeRestrict f).trans hfker
  let P := pGammaL2LinearKernel K A
  obtain ⟨Ebar, hcompbar, hEbarcyc, hEbarodd, hEbarimage⟩ :=
    pGammaL2_exists_pure_field_complement K hK A hPSL hodd
  obtain ⟨E, hcomp, hEφ, hEcyc, hEodd, _⟩ :=
    CentralExtension.exists_odd_cyclic_complement_lift φ hφ
      (hφker ▸ hZcentral) (hZtwo.of_equiv (MulEquiv.subgroupCongr hφker).symm)
      P Ebar hcompbar hEbarodd hEbarcyc
  let L := P.comap φ
  have hLN : L.Normal := inferInstance
  have hLeq : L = (pGammaL2PGLRange K).comap f := by
    ext x
    change φ x ∈ pGammaL2LinearKernel K A ↔ f x ∈ pGammaL2PGLRange K
    rw [mem_pGammaL2LinearKernel_iff, pGammaL2PGLRange,
      SemidirectProduct.range_inl_eq_ker_rightHom]
    rfl
  have hLmap : L.map f = f.range ⊓ pGammaL2PGLRange K := by
    rw [hLeq, Subgroup.map_comap_eq]
  have hPSLPGL : pGammaL2PSLRange K ≤ pGammaL2PGLRange K := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  have hL0L : L0 ≤ L := by
    rw [hLeq]
    apply Subgroup.map_le_iff_le_comap.mp
    rw [hL0map]
    exact hPSLPGL
  have hEimage : E.map f = Ebar.map A.subtype := by
    have h := congrArg (Subgroup.map A.subtype) hEφ
    have hφf : A.subtype.comp φ = f := f.subtype_comp_rangeRestrict
    rw [Subgroup.map_map, hφf] at h
    exact h
  have hPSLcomap : (pGammaL2PSLRange K).comap f = Z ⊔ L0 := by
    rw [← hL0map, Subgroup.comap_map_eq, hfker, sup_comm]
  have hindex : (Z ⊔ L0).relIndex L ∣ 2 := by
    rw [← hPSLcomap, Subgroup.relIndex_comap, hLmap]
    have hm := Subgroup.relIndex_mul_relIndex (pGammaL2PSLRange K)
      (f.range ⊓ pGammaL2PGLRange K) (pGammaL2PGLRange K)
      (le_inf hPSL hPSLPGL) inf_le_right
    rw [pGammaL2_psl_range_relIndex_pgl_eq_two K hK] at hm
    exact ⟨_, hm.symm⟩
  have hcomm : commutator H ≤ Z ⊔ L0 := by
    rw [← hPSLcomap]
    apply Subgroup.map_le_iff_le_comap.mp
    rw [map_commutator_eq]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (pGammaL2_commutator_le_psl_range K hK)
  exact ⟨hZcentral, hZcyc, hZne, hZtwo, f, L, E, hfker, hLN, hL0L,
    hcomp, hEcyc, hEodd, hLmap, hL0map, hEimage.trans hEbarimage, hindex, hcomm, hfcore⟩

public theorem qGroup_projective_linear_complement
    {H : Type u} [Group H] [Finite H] (hH : IsQGroup H)
    (hcore : pPrimeCore 2 H = ⊥) (S : Sylow 2 H)
    (Z : Subgroup H) [Z.Normal] (hZ : Z = subgroupCenter (S : Subgroup H))
    (L0 : Subgroup H) [L0.Normal]
    (K : Type u) [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    Z ≤ Subgroup.center H ∧ IsCyclic Z ∧ Z ≠ ⊥ ∧ IsPGroup 2 Z ∧
      ∃ (f : H →* PGammaL2 K) (L E : Subgroup H),
        f.ker = Z ∧ L.Normal ∧ L0 ≤ L ∧ L.IsComplement' E ∧
        IsCyclic E ∧ Odd (Nat.card E) ∧
        L.map f = f.range ⊓ pGammaL2PGLRange K ∧
        L0.map f = pGammaL2PSLRange K ∧
        E.map f = (pGammaL2FieldProjection K f.range).range.map
          (SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K) ∧
        (Z ⊔ L0).relIndex L ∣ 2 ∧ commutator H ≤ Z ⊔ L0 := by
  obtain ⟨hZc, hZcyc, hZne, hZtwo, f, L, E, hfker, hLN, hL0L, hcomp,
      hEcyc, hEodd, hLmap, hL0map, hEmap, hindex, hcomm, _⟩ :=
    qGroup_projective_linear_complement_with_core_map hH hcore S Z hZ L0 K hK eL0
  exact ⟨hZc, hZcyc, hZne, hZtwo, f, L, E, hfker, hLN, hL0L, hcomp,
    hEcyc, hEodd, hLmap, hL0map, hEmap, hindex, hcomm⟩

end ABG

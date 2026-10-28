module
public import GorensteinWalter.PGammaL2FullLinearRestriction
public import GorensteinWalter.SL2ProjectiveCover
public import ABG.ChapterII.Section1.FusionPatterns

/-!
# Original source data for the full linear-constituent comparison

Suppose the supplied projective map f on a finite group H has kernel the
central cyclic Sylow center Z, maps L into the linear PGL2 layer, and maps
the supplied normal SL2 constituent L0 onto the canonical PSL2 layer.
If ZL0 has relative index two in L, restriction produces a surjective
PGL2 map on that same L. Its kernel is exactly Z restricted to L, and its
core equation uses the original SL2 equivalence on L0.

The restriction theorem supplies the projective map, its element equation,
and the inverse image of PSL2. Actual subgroup equivalences transport the
kernel's centrality, cyclicity, nontriviality, two-group property and exact
Sylow-center cardinality. The designated exterior element of the original
Sylow subgroup maps into L through subtype inclusion. Normality of Z
expresses membership in ZL0 as a product, so being outside the original
Sylow central join proves it is outside the restricted kernel/core join.
Injectivity of the subtype maps preserves both its square-one relation and
the alternative that its square generates the original center.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article p26. This
packages the actual source data needed to apply the full matrix comparison.
It retains f, R, L, L0, the prescribed SL2 equivalence and the exterior
element; no source projection or desired matrix equivalence is assumed.
-/

namespace ABG
open GorensteinWalter

/-- Restrict the original projective map and transfer the supplied Sylow
exterior element to the same full linear constituent. -/
public theorem qGroup_full_linear_source_data
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (R : Sylow 2 H)
    (Z : Subgroup H) (hZ : Z = subgroupCenter (R : Subgroup H))
    (hZc : Z ≤ Subgroup.center H) (hZcyc : IsCyclic Z) (hZne : Z ≠ ⊥)
    (hZtwo : IsPGroup 2 Z) (L L0 : Subgroup H) [L0.Normal]
    (hRL : (R : Subgroup H) ≤ L) (hL0L : L0 ≤ L)
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (f : H →* PGammaL2 F) (hfker : f.ker = Z)
    (hlinear : L.map f ≤ pGammaL2PGLRange F)
    (hcore : L0.map f = pGammaL2PSLRange F)
    (hfcore : ∀ l : L0, f l.val = SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (sl2ProjectiveProjection F (eL0 l))))
    (hindex : (Z ⊔ L0).relIndex L = 2)
    (a : R) (ha : a ∉ L0.comap (R : Subgroup H).subtype ⊔ Subgroup.center R) :
    let M := L0.subgroupOf L
    let e0 : M ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
      (Subgroup.subgroupOfEquivOfLe hL0L).trans eL0
    ∃ φ : L →* PGL2 F, Function.Surjective φ ∧
      (∀ l : L, f l = SemidirectProduct.inl (φ l)) ∧
      φ.ker = Z.subgroupOf L ∧ φ.ker ≤ Subgroup.center L ∧
      IsCyclic φ.ker ∧ φ.ker ≠ ⊥ ∧ IsPGroup 2 φ.ker ∧
      Nat.card φ.ker = Nat.card (Subgroup.center R) ∧
      (∀ x : M, φ x.val = Matrix.ProjectiveSpecialLinearGroup.toPGL
        (sl2ProjectiveProjection F (e0 x))) ∧
      (Matrix.ProjectiveSpecialLinearGroup.toPGL.range).comap φ = φ.ker ⊔ M ∧
      ∃ aL : L, aL.val = a.val ∧ aL ∉ φ.ker ⊔ M ∧
        (a ^ 2 = 1 → aL ^ 2 = 1) ∧
        (Subgroup.zpowers (a ^ 2) = Subgroup.center R →
          Subgroup.zpowers (aL ^ 2) = φ.ker) := by
  let M := L0.subgroupOf L
  let e0 : M ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (Subgroup.subgroupOfEquivOfLe hL0L).trans eL0
  have hZR : Z ≤ (R : Subgroup H) := by
    rw [hZ]
    exact Subgroup.map_subtype_le _
  have hZL : Z ≤ L := hZR.trans hRL
  let : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]
    exact hz⟩
  obtain ⟨φ, hsurj, hφ, hker, hpre⟩ :=
    exists_pgl2_restriction_of_full_linear_layer hF f L L0 hL0L hlinear hcore
      (by simpa only [hfker] using hindex)
  rw [hfker] at hker hpre
  let eK : φ.ker ≃* Z := (MulEquiv.subgroupCongr hker).trans
    (Subgroup.subgroupOfEquivOfLe hZL)
  let eZ : Subgroup.center R ≃* Z :=
    ((Subgroup.center R).equivMapOfInjective (R : Subgroup H).subtype
      (R : Subgroup H).subtype_injective).trans (MulEquiv.subgroupCongr hZ.symm)
  have hKc : φ.ker ≤ Subgroup.center L := by
    intro k hk
    rw [hker] at hk
    apply Subgroup.mem_center_iff.mpr
    intro l
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hZc hk) l.val
  have hKcyc : IsCyclic φ.ker := eK.isCyclic.mpr hZcyc
  have hKne : φ.ker ≠ ⊥ := by
    let : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZne
    exact (Subgroup.nontrivial_iff_ne_bot φ.ker).mp eK.symm.injective.nontrivial
  have hKtwo : IsPGroup 2 φ.ker := hZtwo.of_equiv eK.symm
  have hKcard : Nat.card φ.ker = Nat.card (Subgroup.center R) :=
    Nat.card_congr (eK.trans eZ.symm).toEquiv
  have hφcore (x : M) : φ x.val = Matrix.ProjectiveSpecialLinearGroup.toPGL
      (sl2ProjectiveProjection F (e0 x)) := by
    apply (show Function.Injective (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
      from SemidirectProduct.inl_injective)
    rw [← hφ]
    exact hfcore (Subgroup.subgroupOfEquivOfLe hL0L x)
  have hpre' : (Matrix.ProjectiveSpecialLinearGroup.toPGL.range).comap φ = φ.ker ⊔ M := by
    rw [hpre, Subgroup.subgroupOf_sup hZL hL0L, hker]
  let aL : L := ⟨a.val, hRL a.property⟩
  have hjoinmap : (φ.ker ⊔ M).map L.subtype = Z ⊔ L0 := by
    rw [Subgroup.map_sup, hker, Subgroup.map_subgroupOf_eq_of_le hZL,
      Subgroup.map_subgroupOf_eq_of_le hL0L]
  have haL : aL ∉ φ.ker ⊔ M := by
    intro hh
    have haambient : a.val ∈ Z ⊔ L0 := by
      rw [← hjoinmap]
      exact Subgroup.mem_map_of_mem L.subtype hh
    obtain ⟨z, hz, l, hl, he⟩ := Subgroup.mem_sup_of_normal_left.mp haambient
    have hlR : l ∈ (R : Subgroup H) := by
      have hh := (R : Subgroup H).mul_mem ((R : Subgroup H).inv_mem (hZR hz)) a.property
      simpa only [← he, inv_mul_cancel_left] using hh
    have hzR : (⟨z, hZR hz⟩ : R) ∈ Subgroup.center R := by
      have he : Z.comap (R : Subgroup H).subtype = Subgroup.center R := by
        rw [hZ]
        exact Subgroup.comap_map_eq_self_of_injective
          (R : Subgroup H).subtype_injective _
      rw [← he]
      exact hz
    apply ha
    have hprod : (⟨z, hZR hz⟩ : R) * ⟨l, hlR⟩ = a := Subtype.ext he
    rw [← hprod]
    exact (L0.comap (R : Subgroup H).subtype ⊔ Subgroup.center R).mul_mem
      ((show Subgroup.center R ≤ _ from le_sup_right) hzR)
      ((show L0.comap (R : Subgroup H).subtype ≤ _ from le_sup_left) hl)
  refine ⟨φ, hsurj, hφ, hker, hKc, hKcyc, hKne, hKtwo, hKcard,
    hφcore, hpre', aL, rfl, haL, ?_, ?_⟩
  · intro hs
    apply Subtype.ext
    change a.val ^ 2 = (1 : H)
    exact congrArg (fun x : R => x.val) hs
  · intro hs
    apply Subgroup.map_injective L.subtype_injective
    rw [hker, Subgroup.map_subgroupOf_eq_of_le hZL, MonoidHom.map_zpowers]
    have hh := congrArg (Subgroup.map (R : Subgroup H).subtype) hs
    rw [MonoidHom.map_zpowers] at hh
    exact hh.trans hZ.symm
end ABG

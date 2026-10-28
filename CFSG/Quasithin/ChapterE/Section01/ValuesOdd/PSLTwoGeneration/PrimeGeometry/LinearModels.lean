module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.FieldReduction
public import GorensteinWalter.PGammaL2NormalExtension
public import GorensteinWalter.PSL2KleinFourCentralizerEqSelf
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# Linear models for prime-field PSL₂ extensions

A prime field has no nonidentity field automorphism. The faithful conjugation
action on a self-centralizing normal PSL₂ subgroup therefore has trivial field
projection in PΓL₂. Its full linear kernel is PSL₂ or PGL₂, giving an actual
isomorphism of the ambient group with one of those models. The final theorem
applies this to the generalized Fitting subgroup in E.1.14(6).

This establishes the model reduction only; the local E-members still need to
be constructed in both models.

Source: Aschbacher--Smith, E.1.14(6), printed p.214; the projective semilinear
automorphism theorem and index-two linear-layer calculation are supplied by
`GorensteinWalter.PGammaL2NormalExtension` and `PGammaL2Subgroups`.
-/

public section

open GorensteinWalter Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry

private theorem fieldAut_eq_one {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) (σ : F ≃+* F) : σ = 1 := by
  let : Fintype F := Fintype.ofFinite F
  let e : ZMod p ≃+* F := ZMod.ringEquivOfPrime F hp (by simpa using hF)
  have h : e.trans σ = e := Subsingleton.elim _ _
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact congrArg (fun f : ZMod p ≃+* F => f y) h

/-- The ambient group of a self-centralizing normal prime-field PSL₂ is
itself isomorphic to PSL₂ or PGL₂. -/
theorem linear_models_of_normal_prime_psl
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (N : Subgroup G) [N.Normal] {p : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hF : Nat.card F = p) (hp5 : 5 < p) (e : N ≃* PSL2 F)
    (hC : centralizer (N : Set G) = ⊥) :
    Nonempty (G ≃* PSL2 F) ∨ Nonempty (G ≃* PGL2 F) := by
  let : Fact p.Prime := ⟨hp⟩
  have hq : IsOddPrimePower (Nat.card F) := ⟨p, 1, hp, hpo, le_rfl, by simpa using hF⟩
  have hc : 3 < Nat.card F := by omega
  let a : PGammaL2 F ≃* MulAut (PSL2 F) :=
    pGammaL2EquivMulAutPSL2 F hq hc
      (pGammaL2ToMulAutPSL2_surjective F (p := p) (f := 1) (by simpa using hF) hq hc)
  let c : G →* MulAut (PSL2 F) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := N))
  let f : G →* PGammaL2 F := a.symm.toMonoidHom.comp c
  have hf : Function.Injective f :=
    a.symm.injective.comp ((MulAut.congr e).injective.comp
      (conjNormal_injective_of_centralizer_eq_bot N hC))
  have hinner : pGammaL2PSLRange F ≤ f.range := by
    intro x hx
    obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff F x).mp hx
    refine ⟨(e.symm y : N), ?_⟩
    apply a.injective
    change a (a.symm (c (e.symm y))) = _
    rw [a.apply_symm_apply]
    change MulAut.congr e (MulAut.conjNormal ((e.symm y : N) : G)) =
      pGammaL2ToMulAutPSL2 F hq hc (SemidirectProduct.inl
        (Matrix.ProjectiveSpecialLinearGroup.toPGL y))
    rw [pGammaL2ToMulAutPSL2_inl, pgl2InnerAutPSL2_toPGL, MulAut.conjNormal_val]
    ext z
    simp [MulAut.congr, MulAut.conj_apply]
  have hker : pGammaL2LinearKernel F f.range = ⊤ := by
    apply top_unique
    intro x _
    rw [mem_pGammaL2LinearKernel_iff]
    exact fieldAut_eq_one hp hF _
  let er : G ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let ek : pGammaL2LinearKernel F f.range ≃* G :=
    (MulEquiv.subgroupCongr hker).trans ((Subgroup.topEquiv).trans er.symm)
  rcases pGammaL2_linear_kernel_model F hq f.range hinner with ei | ei
  · exact Or.inl ⟨ek.symm.trans ei.some⟩
  · exact Or.inr ⟨ek.symm.trans ei.some⟩

/-- Apply the faithful model reduction to the actual generalized Fitting
subgroup of the E.1.14(6) configuration. -/
theorem linear_models_of_prime_socle
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hp5 : 5 < p)
    (hL : ClassicalGroup.IsPSL (Theory.GroupTheory.generalizedFitting G) 2 p)
    (hC : centralizer (Theory.GroupTheory.generalizedFitting G : Set G) = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
      (Nonempty (G ≃* PSL2 F) ∨ Nonempty (G ≃* PGL2 F)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  exact ⟨F, inferInstance, inferInstance, hF,
    linear_models_of_normal_prime_psl _ hp hpo hF hp5 e hC⟩

/-- A faithful embedding in odd PGL₂ makes every four-group self-centralizing. -/
theorem kleinFour_selfCentralizing_of_embedding
    {G F : Type*} [Group G] [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (j : G →* PGL2 F)
    (hj : Function.Injective j) (A : Subgroup G) (hA : IsKleinFour A) :
    centralizer (A : Set G) = A := by
  let : IsKleinFour A := hA
  have hAj : IsKleinFour (A.map j) := isKleinFour_map_of_injective A hA j hj
  apply le_antisymm
  · intro x hx
    have hcent : j x ∈ centralizer (A.map j : Set (PGL2 F)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      simpa only [map_mul] using congrArg j (mem_centralizer_iff.mp hx a ha)
    rw [pgl2_kleinFour_centralizer_eq_self F hF (A.map j) hAj] at hcent
    exact (mem_map_iff_mem hj).mp hcent
  · intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm
      (⟨y, hy⟩ : A) ⟨x, hx⟩)

/-- The actual prime-field socle model makes every ambient four-group
self-centralizing, including in the diagonal extension. -/
theorem kleinFour_selfCentralizing_of_prime_socle
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hp5 : 5 < p)
    (hL : ClassicalGroup.IsPSL (Theory.GroupTheory.generalizedFitting G) 2 p)
    (hC : centralizer (Theory.GroupTheory.generalizedFitting G : Set G) = ⊥)
    (A : Subgroup G) (hA : IsKleinFour A) : centralizer (A : Set G) = A := by
  obtain ⟨F, _, _, hF, he⟩ := linear_models_of_prime_socle hp hpo hp5 hL hC
  have hq : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, hpo, le_rfl, by simpa using hF⟩
  rcases he with he | he
  · let e := he.some
    let j : G →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL.comp e.toMonoidHom
    exact kleinFour_selfCentralizing_of_embedding hq j
      (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective) A hA
  · exact kleinFour_selfCentralizing_of_embedding hq he.some.toMonoidHom
      he.some.injective A hA

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry

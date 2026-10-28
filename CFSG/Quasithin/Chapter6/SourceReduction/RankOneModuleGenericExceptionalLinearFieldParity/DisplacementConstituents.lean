module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.Estimates
public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.AllDisplacement
public import Theory.Representation.BinaryOffender.SectionLinear


/-!
# Residual constituents in the literal parity quotient

The source residual marking identifies F*(H/O₂(H)) with the concrete
PSL₃(4). The uniform H.4.7 bound therefore gives displacement at least
three on every faithful constituent irreducible under this residual.
The odd-degree product isomorphism then transports the original actor
representatives into the actual U/Z₁ action. Its fixed codimension is
exactly the original relative-index displacement, without order-two lifts.

The final theorem applies both calculations to the odd-degree source
product. It leaves the constituent as an explicit input: constructing the
Cartan orbit of constituents and its n-fold contribution is still part of
qt-d-1222-linear-field-parity, which also owns the global TI/F.8 setup.
No nine-dimensional displacement or parity conclusion is asserted here.

Source: Aschbacher–Smith 5.1.17, printed p.641, and H.4.7, pp.382–383
(refs/quasithin.pdf).
-/

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

private theorem concrete_fitting_equiv
    (hTH : (T : Subgroup G) ≤ H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    Nonempty (Matrix.PSL3Four.PSL ≃* generalizedFitting (H ⧸ pCore 2 H)) := by
  obtain ⟨F,_,_,hcard,⟨e⟩⟩ := residual_coreQuotient_fitting_model hTH hm
  let : Fintype F := Fintype.ofFinite F
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let a : Matrix.PSL3Four.F ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard,
      Matrix.PSL3Four.card_F])
  exact ⟨(Atlas.fieldEquivPSL 3 a).trans e.symm⟩

variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
  [FiniteDimensional (ZMod 2) X]

/-- The original quotient action restricted along the residual factor of the source product. -/
def residualFactorAction
    (e : ((H ⧸ pCore 2 H) × A) ≃*
      ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)))
    (ρ : Representation (ZMod 2)
      ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) X) :
    Representation (ZMod 2) (H ⧸ pCore 2 H) X :=
  ρ.comp (e.toMonoidHom.comp (MonoidHom.inl _ _))

omit [Finite G] [FiniteDimensional (ZMod 2) X] in
/-- Evaluation of the residual factor uses the original product marking. -/
theorem residualFactorAction_eq
    (e : ((H ⧸ pCore 2 H) × A) ≃*
      ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)))
    (ρ : Representation (ZMod 2)
      ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) X) :
    residualFactorAction e ρ = ρ.comp (e.toMonoidHom.comp (MonoidHom.inl _ _)) := by rfl

/-- Each irreducible faithful residual constituent contributes at least three dimensions. -/
theorem residual_constituent_displacement
    (hTH : (T : Subgroup G) ≤ H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) X)
    (J : Subrepresentation σ) (hJ : Function.Injective J.toRepresentation)
    (hi : IsIrreducible (J.toRepresentation.comp
      (generalizedFitting (H ⧸ pCore 2 H)).subtype))
    {y : G} (hy : y ∈ H) (hy2 : y ^ 2 ∈ H.pCoreIn 2) (hne : y ∉ H.pCoreIn 2) :
    3 ≤ fixedCodim J.toRepresentation
      (zpowers (QuotientGroup.mk' (pCore 2 H) ⟨y,hy⟩)) := by
  let t := QuotientGroup.mk' (pCore 2 H) ⟨y,hy⟩
  have h2 : t ^ 2 = 1 := by
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨z,hz,he⟩ := hy2
    exact (Subtype.ext he : z = (⟨y,hy⟩ : H)^2) ▸ hz
  have hne' : t ≠ 1 := by
    intro hh
    exact hne (mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp hh))
  have ht : orderOf t = 2 := orderOf_eq_prime h2 hne'
  obtain ⟨f⟩ := concrete_fitting_equiv hTH hm
  let := hi
  have hb := ChapterH.Section01To04.L3Four.source_psl3Four_involution_displacement_ge_three
    f J.toRepresentation hJ t ht
  simpa only [fixedCodim_zpowers_eq_displacement_rank,Module.End.one_eq_id] using hb

omit [Finite G] in
private theorem subgroupOf_zpowers (K : Subgroup G) (x : K) :
    (zpowers (x : G)).subgroupOf K = zpowers x := by
  apply map_injective K.subtype_injective
  rw [map_subgroupOf_eq_of_le (zpowers_le.mpr x.property),MonoidHom.map_zpowers]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional (ZMod 2) X] in
/-- Fixed codimension in the residual factor equals the original relative-index displacement. -/
theorem displacement_eq_residualFactor_fixedCodim
    {V : Subgroup G} (hf : (setup T L V H A).Hypothesis)
    (e : ((H ⧸ pCore 2 H) × A) ≃*
      ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)))
    (he : ∀ (x : H) (a : A),
      e (QuotientGroup.mk' (pCore 2 H) x, a) =
        QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))
          ⟨(x : G) * (a : G), mul_mem_sup x.property a.property⟩)
    (ρ : Representation (ZMod 2)
      ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) X)
    (c : BinaryConjugationSection (H ⊔ A) (setup T L V H A).U
      (setup T L V H A).V₁ (ρ.comp (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G)))))
    {y : G} (hy : y ∈ H) :
    displacement (setup T L V H A) y =
      fixedCodim (residualFactorAction e ρ)
        (zpowers (QuotientGroup.mk' (pCore 2 H) ⟨y,hy⟩)) := by
  rw [displacement_eq_fixedCodim hf ρ c y (mem_sup_left hy)]
  change fixedCodim ρ (((zpowers y).subgroupOf (H ⊔ A)).map
    (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G)))) = _
  rw [subgroupOf_zpowers (H ⊔ A) ⟨y,mem_sup_left hy⟩,MonoidHom.map_zpowers]
  unfold residualFactorAction fixedCodim
  rw [fixedSpace_comp_map,MonoidHom.map_zpowers]
  have he' := he ⟨y,hy⟩ 1
  have hu : (⟨((⟨y,hy⟩ : H) : G) * ((1 : A) : G),
      mul_mem_sup hy (one_mem A)⟩ : ↥(H ⊔ A : Subgroup G)) = ⟨y,mem_sup_left hy⟩ :=
    Subtype.ext (mul_one y)
  rw [hu] at he'
  exact congrArg (fun z => Module.finrank (ZMod 2)
    (X ⧸ fixedSpace ρ (zpowers z))) he'.symm


/-- The quotient product transfers the residual constituent bound to the literal F.8 displacement. -/
theorem odd_constituent_displacement
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (V : Subgroup G) (hf : (setup T L V H A).Hypothesis) :
    ∃ e : ((H ⧸ pCore 2 H) × A) ≃*
        ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)),
      (∀ (x : H) (a : A),
        e (QuotientGroup.mk' (pCore 2 H) x, a) =
          QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))
            ⟨(x : G) * (a : G), mul_mem_sup x.property a.property⟩) ∧
      ∀ (ρ : Representation (ZMod 2)
          ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) X),
        BinaryConjugationSection (H ⊔ A) (setup T L V H A).U
          (setup T L V H A).V₁
          (ρ.comp (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G)))) →
        ∀ J : Subrepresentation (residualFactorAction e ρ),
          Function.Injective J.toRepresentation →
          IsIrreducible (J.toRepresentation.comp
            (generalizedFitting (H ⧸ pCore 2 H)).subtype) →
          ∀ y, y ∈ H → y ^ 2 ∈ H.pCoreIn 2 → y ∉ H.pCoreIn 2 →
            3 ≤ displacement (setup T L V H A) y := by
  obtain ⟨e,he⟩ := odd_join_quotient_product h hH c hodd hK hnf hm
  refine ⟨e,he,?_⟩
  intro ρ coordinates J hJ hi y hy hy2 hne
  rw [displacement_eq_residualFactor_fixedCodim hf e he ρ coordinates hy]
  exact (residual_constituent_displacement hH.1.1.2 hm _ J hJ hi hy hy2 hne).trans
    (fixedCodim_subrepresentation_le _ J _)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity

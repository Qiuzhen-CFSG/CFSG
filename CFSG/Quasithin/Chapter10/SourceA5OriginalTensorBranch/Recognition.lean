module
public import CFSG.Quasithin.Chapter10.SourceA5ProductAlternatives
public import CFSG.Quasithin.Chapter10.SourceA5TensorRecognition
public import CFSG.Quasithin.Chapter10.SourceA5OriginalIrreducibility.FaithfulAction
public import Theory.Representation.BinaryConjugationSection.Cover
public import Theory.Representation.BinaryConjugationSection.Irreducible
public import Theory.GroupTheory.ReducedNormal.SubspaceMinimality
public import Theory.SpecificGroups.SL2.CardFourEquiv
/-!
# Recognition through the original canonical product action

The literal full module and its central quotient carry actions of
M/C_M(V_M). A marked normal A₅ product embeds in this actor. When the original
exchange preserves the seed, subgroup minimality makes the product quotient
irreducible. The genuine cubic bound excludes the deleted tensor square using
its full normalizer. The canonical coordinate projection is then a central
cover of a cubic-free module; commuting cubic trace makes it injective.
Determinant recognition retains the original quotient and its first marking.

This is the module-theoretic assembly for Aschbacher–Smith D.3.7,
printed pp.197–199. The source wrapper constructs the marked embedding and
the exchange from the original nonnormal component and chosen Sylow element.
-/
public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.QuadraticFourGroup Representation.QuadraticFourGroup.TensorClassification
open BinaryPermutation.FiveTensorSquare
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private local instance originalTensorElementary (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem module_eq_full_of_seed_eq
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hseed : D.seed = D.fullModule) : D.moduleSubgroup = D.fullModule := by
  exact le_antisymm (le_componentOrbit _ _) (hseed ▸ le_componentOrbit D.seed T)

private noncomputable def originalTensorQuotientSection
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {Q : Type*} [Group Q]
    (q : localOrbit T L →* Q)
    (σ : Representation (ZMod 2) Q (Additive D.fullCentralQuotient))
    (hσ : ∀ (g : localOrbit T L) (v : D.fullModule),
      σ (q g) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
        Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
          ⟨(g : G) * (v : G) * (g : G)⁻¹,
            (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule
              ((localOrbit T L).le_normalizer g.property)) v).mp v.property⟩)) :
    BinaryConjugationSection (localOrbit T L) D.fullModule
      (D.fullModule ⊓ centralizer (localOrbit T L : Set G)) (σ.comp q) where
  section_le := D.fullModule_le_orbit
  kernel_le := inf_le_left
  normalized := (localOrbit T L).le_normalizer.trans D.maximalLocal_normalizes_fullModule
  coordinates := {
    toFun v := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v))
    map_one' := (QuotientGroup.mk' D.fullCentralizer).map_one
    map_mul' := (QuotientGroup.mk' D.fullCentralizer).map_mul }
  onto := QuotientGroup.mk'_surjective _
  kernel_eq := by
    ext x
    change QuotientGroup.mk' D.fullCentralizer x = 1 ↔
      (x : G) ∈ D.fullModule ⊓ centralizer (localOrbit T L : Set G)
    exact (QuotientGroup.eq_one_iff x).trans (and_iff_right x.property).symm
  equivariant g v := (hσ g v).symm

private theorem originalTensorQuotientIrreducible
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hseed : D.seed = D.fullModule)
    {Q : Type*} [Group Q]
    (q : localOrbit T L →* Q) (hq : Function.Surjective q)
    (σ : Representation (ZMod 2) Q (Additive D.fullCentralQuotient))
    [Nontrivial (Additive D.fullCentralQuotient)]
    (s : BinaryConjugationSection (localOrbit T L) D.fullModule
      (D.fullModule ⊓ centralizer (localOrbit T L : Set G)) (σ.comp q)) :
    σ.IsIrreducible := by
  apply (irreducible_comp_surjective_iff q hq σ).mp
  apply s.irreducible_of_subgroup_minimal
  intro J hJ hnorm
  rcases ReducedNormal.subspaceImage_eq_or_le_centralizer (localJoin T L)
      (localOrbit T L) le_sup_left D.homogeneous.isIrrPlus J
      (by change J ≤ D.seed; rw [hseed]; exact hJ) hnorm with he | hc
  · exact Or.inl (he.trans hseed)
  · exact Or.inr (le_inf hJ hc)
private theorem originalTensorFullAction
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    ∃ ρ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
      (Additive D.fullModule),
      ∀ (m : D.maximalLocal) (v : D.fullModule),
        ((ρ (q m) (Additive.ofMul v)).toMul : G) =
          (m : G) * (v : G) * (m : G)⁻¹ := by
  dsimp only
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
  let σ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hVM : D.fullModule ≤ D.maximalLocal :=
    D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  let eU : U ≃* D.fullModule := subgroupOfEquivOfLe hVM
  let b : Additive U ≃ₗ[ZMod 2] Additive D.fullModule :=
    eU.toAdditive.toLinearEquiv (fun c v => ZMod.map_smul eU.toAdditive.toAddMonoidHom c v)
  let ρ : Representation (ZMod 2) _ (Additive D.fullModule) :=
    (b.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp σ
  refine ⟨ρ,fun m v => ?_⟩
  change (((σ (q m) (b.symm (Additive.ofMul v))).toMul : D.maximalLocal) : G) = _
  exact congrArg (fun x : D.maximalLocal => (x : G))
    (NormalElementaryQuotient.representation_apply U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) m (b.symm (Additive.ofMul v)))

/-- A marked canonical product and its actual conjugating element supply the
original determinant model. All module actions and the central cover are constructed. -/
theorem source_a5_tensor_model_of_canonical_product
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* Alt)
    (hminimal : D.IsMinimalFullModule) (hseed : D.seed = D.fullModule)
    (hbound : SourceFullModuleCubicBound D) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let qM := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    ∀ (q : localOrbit T L →* Alt × Alt), Function.Surjective q →
      q.ker = pCore 2 (localOrbit T L) →
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ =
        (e (QuotientGroup.mk' _ l),1)) →
    ∀ (i : Alt × Alt →* (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))),
      Function.Injective i → i.range.Normal →
      (∀ x : localOrbit T L, i (q x) = qM ⟨x,(localOrbit T L).le_normalizer x.property⟩) →
    ∀ (t : D.maximalLocal) (α : MulAut Alt),
      (∀ g, qM t * i g * (qM t)⁻¹ = i (α g.2,g.1)) →
      Nonempty (SourceA5TensorModel D e) := by
  dsimp only
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let qM := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
  intro q hq hqker hqfirst i hi hinormal hcompat t α hconj
  let : i.range.Normal := hinormal
  obtain ⟨ρ,hρ,hρirr,hρbound,hρact⟩ :=
    source_minimal_full_quotient_faithful_cubic_action D hminimal hbound
  let : ρ.IsIrreducible := hρirr
  let : Nontrivial (Additive D.fullCentralQuotient) :=
    Subrepresentation.irreducible_module_nontrivial ρ
  let : FiniteDimensional (ZMod 2) (Additive D.fullCentralQuotient) := Module.Finite.of_finite
  let σ : Representation (ZMod 2) (Alt × Alt) (Additive D.fullCentralQuotient) := ρ.comp i
  have hσact (x : localOrbit T L) (v : D.fullModule) :
      σ (q x) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
        Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
          ⟨(x : G) * (v : G) * (x : G)⁻¹,
            (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule
              ((localOrbit T L).le_normalizer x.property)) v).mp v.property⟩) := by
    change ρ (i (q x)) _ = _
    rw [hcompat]
    exact hρact _ v
  let s := originalTensorQuotientSection D q σ hσact
  let : σ.IsIrreducible := originalTensorQuotientIrreducible D hseed q hq σ s
  have hσfaithful : Function.Injective σ := hρ.comp hi
  obtain ⟨a,ha,_,_,_⟩ := BinaryPermutation.AlternatingFiveLinearTwo.exists_cubic_fixed_ne_zero
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha
  have hleft : ∃ g, σ (g,1) ≠ 1 := by
    refine ⟨a,fun h => ha1 (congrArg Prod.fst (hσfaithful (h.trans σ.map_one.symm)))⟩
  have hright : ∃ g, σ (1,g) ≠ 1 := by
    refine ⟨a,fun h => ha1 (congrArg Prod.snd (hσfaithful (h.trans σ.map_one.symm)))⟩
  let E := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom (qM t))
  have hE (g : Alt × Alt) (v : Additive D.fullCentralQuotient) :
      E (σ g v) = σ (α g.2,(MulEquiv.refl Alt) g.1) (E v) := by
    change ρ (qM t) (ρ (i g) v) = ρ (i (α g.2,g.1)) (ρ (qM t) v)
    simp only [←Module.End.mul_apply,←map_mul]
    exact congrArg (fun g => ρ g v) (mul_inv_eq_iff_eq_mul.mp (hconj g))
  have hfree : CubicFreeOnFactors σ := by
    rcases source_a5_product_module_alternatives σ hleft hright E α (MulEquiv.refl Alt)
        hE with hf | hd
    · exact hf
    obtain ⟨ed⟩ := hd
    obtain ⟨A,hA,_,hsmall⟩ := (BinaryOffender.cubicRatio_le_nat_iff ρ 2).mp hρbound
    exact False.elim ((Nat.not_lt_of_ge hsmall)
      (faithful_actor_ratio_gt_two ρ hρ i ed hA))
  obtain ⟨ρfull,hρfull⟩ := originalTensorFullAction D
  let ν : Representation (ZMod 2) (Alt × Alt) (Additive D.fullModule) := ρfull.comp i
  have hν (x : localOrbit T L) (v : Additive D.fullModule) :
      ((ν (q x) v).toMul : G) = (x : G) * (v.toMul : G) * (x : G)⁻¹ := by
    change ((ρfull (i (q x)) v).toMul : G) = _
    rw [hcompat]
    exact hρfull _ v.toMul
  obtain ⟨p,hp,_⟩ := BinaryConjugationSection.exists_cover_of_fully_moved
    σ q hq s ν hν inf_le_right
    (D.fullModule_eq_commutator (source_module_nonsolvable_uniqueness D)).symm
  have hpInj : Function.Injective p := OneCohomology.injective_of_cover_product_cubics
    p hp a (by rw [←ha]; exact pow_orderOf_eq_one _) a (hfree.1 a ha) (hfree.2 a ha)
  let ep : ν.Equiv σ := Representation.Equiv.mk
    (LinearEquiv.ofBijective p.toLinearMap ⟨hpInj,hp.1⟩) p.isIntertwining'
  let c : BinaryConjugationSection (localOrbit T L) D.fullModule ⊥ (ν.comp q) := {
    section_le := D.fullModule_le_orbit
    kernel_le := bot_le
    normalized := (localOrbit T L).le_normalizer.trans D.maximalLocal_normalizes_fullModule
    coordinates := { toFun v := Multiplicative.ofAdd (Additive.ofMul v)
                     map_one' := rfl
                     map_mul' _ _ := rfl }
    onto := fun v => ⟨v.toAdd.toMul,rfl⟩
    kernel_eq := by
      ext v
      change v = 1 ↔ (v : G) = 1
      exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
    equivariant := by
      intro x v
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (hν x (Additive.ofMul v)).symm }
  let cσ := c.relabel q ep
  let j : Alt ≃* Factor 2 :=
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (GaloisField.card 2 2 (by decide))).some.symm
  let q' := (j.prodCongr j).toMonoidHom.comp q
  let σ' : Representation (ZMod 2) (Factor 2 × Factor 2) (Additive D.fullCentralQuotient) :=
    σ.comp (j.symm.prodCongr j.symm).toMonoidHom
  have he : σ'.comp q' = σ.comp q := by
    apply MonoidHom.ext
    intro x
    change σ ((j.symm.prodCongr j.symm) ((j.prodCongr j) (q x))) = σ (q x)
    exact congrArg σ (Prod.ext (j.symm_apply_apply (q x).1) (j.symm_apply_apply (q x).2))
  have hfree' : CubicFreeOnFactors σ' := by
    constructor
    · intro g hg v hv
      apply hfree.1 (j.symm g) ((orderOf_injective j.symm.toMonoidHom j.symm.injective g).trans hg) v
      change σ (j.symm g,j.symm 1) v = v at hv
      simpa only [map_one] using hv
    · intro g hg v hv
      apply hfree.2 (j.symm g) ((orderOf_injective j.symm.toMonoidHom j.symm.injective g).trans hg) v
      change σ (j.symm 1,j.symm g) v = v at hv
      simpa only [map_one] using hv
  apply source_a5_tensor_model_of_cubic_free_product D e hminimal hseed
    (module_eq_full_of_seed_eq D hseed) q' ((j.prodCongr j).surjective.comp hq) ?_
    j ?_ σ' hfree' (he.symm ▸ cσ)
  · change ((j.prodCongr j).toMonoidHom.comp q).ker = _
    rw [MonoidHom.ker_comp_of_injective q _ (j.prodCongr j).injective,hqker]
  · intro l
    change (j.prodCongr j) (q ⟨l,le_componentOrbit L T l.property⟩) = _
    rw [hqfirst]
    exact Prod.ext rfl j.map_one

end CFSG.Quasithin.Chapter10

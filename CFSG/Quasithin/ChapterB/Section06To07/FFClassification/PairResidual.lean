module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairNatural
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
public import Theory.Representation.PSL3Two.ResidualFFForms.Reduction
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.NormalInvariants
/-!
# The exact residual-fixed kernel of the paired natural coordinates

Each natural factor has no fixed vector. The product model therefore has
no fixed vector, and restriction to the two-residual preserves this fact by
the modular fixed-vector theorem. The original quotient map consequently
kills exactly the residual-fixed vectors. The final applications identify
the embedded offender residual with the original ambient two-residual.

Source: Aschbacher–Smith B.6.9(2),(4), E.2.3, pp.115–116 and216–217.
-/
@[expose] public section
open Subgroup Representation Representation.BinaryOffender
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction

private theorem symmetric_five_irreducible :
    IsIrreducible (BinaryPermutation.naturalRepresentation (Fin 5)) := by
  let τ := BinaryPermutation.naturalRepresentation (Fin 5)
  let := BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin 5) (by decide)
  let : Nontrivial (BinaryPermutation.natural (Fin 5)) :=
    Subrepresentation.irreducible_module_nontrivial (τ.comp (alternatingGroup (Fin 5)).subtype)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation (τ.comp (alternatingGroup (Fin 5)).subtype) :=
    ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule g hv⟩
  rcases eq_bot_or_eq_top T with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    have ht := congrArg (fun S : Subrepresentation (τ.comp (alternatingGroup (Fin 5)).subtype) => S.toSubmodule) h
    exact ht
  · right
    apply Subrepresentation.toSubmodule_injective
    have ht := congrArg (fun S : Subrepresentation (τ.comp (alternatingGroup (Fin 5)).subtype) => S.toSubmodule) h
    exact ht

private theorem symmetric_five_invariants :
    (BinaryPermutation.naturalRepresentation (Fin 5)).invariants = ⊥ := by
  let τ := BinaryPermutation.naturalRepresentation (Fin 5)
  let := symmetric_five_irreducible
  by_contra hn
  have hfix : Representation.invariants (τ.comp (⊤ : Subgroup (Equiv.Perm (Fin 5))).subtype) ≠ ⊥ := by
    convert hn using 1
    ext v
    exact ⟨fun h g => h ⟨g,Subgroup.mem_top _⟩,fun h g => h g⟩
  have hk := le_ker_of_normal_invariants_ne_bot τ ⊤ hfix
  rw [(MonoidHom.ker_eq_bot_iff _).mpr
    (BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide))] at hk
  exact top_ne_bot (bot_unique hk)

private theorem product_invariants {D M : Type*} [Group D] [AddCommGroup M]
    [Module (ZMod 2) M] (τ : Representation (ZMod 2) D M) (ht : τ.invariants = ⊥) :
    (Representation.prod (τ.comp (MonoidHom.fst D D))
      (τ.comp (MonoidHom.snd D D))).invariants = ⊥ := by
  apply bot_unique
  intro v hv
  apply Prod.ext
  · apply ht.le
    intro g
    exact congrArg Prod.fst (hv (g,1))
  · apply ht.le
    intro g
    exact congrArg Prod.snd (hv (1,g))

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem residual_fixed_eq_invariants_of_reduced_invariants
    (ρ : Representation (ZMod 2) D V)
    (hρ : (fixed ρ).quotientRepresentation.invariants = ⊥) :
    fixedSpace ρ (pResidual 2 D) = ρ.invariants := by
  apply le_antisymm
  · intro v hv
    have h := BinaryLinearThree.ResidualFFForms.invariants_restrict_eq_bot
      (fixed ρ).quotientRepresentation (pResidual 2 D) (isPGroup_quotient_pResidual 2) hρ
    have hm : (fixed ρ).toSubmodule.mkQ v ∈
        Representation.invariants ((fixed ρ).quotientRepresentation.comp (pResidual 2 D).subtype) := by
      intro g
      exact congrArg (fixed ρ).toSubmodule.mkQ (hv g)
    exact (Submodule.Quotient.mk_eq_zero _).mp (h.le hm)
  · intro v hv g
    exact hv g

theorem SourceInduction.SourceTwoFactorCase.MarkedProduct.linear_residual_fixed
    {ρ : Representation (ZMod 2) D V} {d : SourceTwoFactorCase ρ}
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2)) :
    fixedSpace ρ (pResidual 2 D) = ρ.invariants :=
  residual_fixed_eq_invariants_of_reduced_invariants ρ
    (ExtensionConsequences.invariants_of_equiv c.action
      (product_invariants _ (ExtensionConsequences.linearNatural_invariants F (by decide))))

theorem SourceInduction.SourceTwoFactorCase.MarkedProduct.symmetric_residual_fixed
    {ρ : Representation (ZMod 2) D V} {d : SourceTwoFactorCase ρ}
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5))) :
    fixedSpace ρ (pResidual 2 D) = ρ.invariants :=
  residual_fixed_eq_invariants_of_reduced_invariants ρ
    (ExtensionConsequences.invariants_of_equiv c.action
      (product_invariants _ symmetric_five_invariants))


section Map
variable {A M : Type*} [Group A] [AddCommGroup M] [Module (ZMod 2) M]
  {ρ : Representation (ZMod 2) D V} {d : SourceTwoFactorCase ρ}
  {τ : Representation (ZMod 2) A M}
omit [Finite D] [FiniteDimensional (ZMod 2) V] in
noncomputable def SourceInduction.SourceTwoFactorCase.MarkedProduct.quotientMap (c : d.MarkedProduct τ) :
    V →ₗ[ZMod 2] (M × M) := c.action.linearEquiv.toLinearMap.comp (fixed ρ).toSubmodule.mkQ
omit [Finite D] [FiniteDimensional (ZMod 2) V] in
theorem SourceInduction.SourceTwoFactorCase.MarkedProduct.quotientMap_surjective (c : d.MarkedProduct τ) :
    Function.Surjective c.quotientMap :=
  c.action.linearEquiv.surjective.comp (fixed ρ).toSubmodule.mkQ_surjective
omit [Finite D] [FiniteDimensional (ZMod 2) V] in
theorem SourceInduction.SourceTwoFactorCase.MarkedProduct.quotientMap_ker (c : d.MarkedProduct τ) :
    c.quotientMap.ker = ρ.invariants := by
  rw [SourceInduction.SourceTwoFactorCase.MarkedProduct.quotientMap,LinearMap.ker_comp,
    c.action.linearEquiv.ker,Submodule.comap_bot,Submodule.ker_mkQ]
  rfl
omit [Finite D] [FiniteDimensional (ZMod 2) V] in
theorem SourceInduction.SourceTwoFactorCase.MarkedProduct.quotientMap_action (c : d.MarkedProduct τ)
    (g : D) (v : V) :
    c.quotientMap (ρ g v) =
      (Representation.prod (τ.comp (MonoidHom.fst A A)) (τ.comp (MonoidHom.snd A A)))
        (c.action.groupEquiv g) (c.quotientMap v) :=
  c.action.intertwines g ((fixed ρ).toSubmodule.mkQ v)
end Map

theorem source_offender_pair_linear_kernel
    (ρ : Representation (ZMod 2) D V)
    (T : Sylow 2 D) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 D = ⊥)
    {d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype)}
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2)) :
    c.quotientMap.ker = fixedSpace ρ (pResidual 2 D) := by
  rw [c.quotientMap_ker,← c.linear_residual_fixed F]
  have hh := fixedSpace_comp_map ρ (offenderSubgroup ρ).subtype
    (pResidual 2 (offenderSubgroup ρ))
  rw [offender_residual_eq T hP ρ hff hcore] at hh
  exact hh

theorem source_offender_pair_symmetric_kernel
    (ρ : Representation (ZMod 2) D V)
    (T : Sylow 2 D) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 D = ⊥)
    {d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype)}
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5))) :
    c.quotientMap.ker = fixedSpace ρ (pResidual 2 D) := by
  rw [c.quotientMap_ker,← c.symmetric_residual_fixed]
  have hh := fixedSpace_comp_map ρ (offenderSubgroup ρ).subtype
    (pResidual 2 (offenderSubgroup ρ))
  rw [offender_residual_eq T hP ρ hff hcore] at hh
  exact hh
end CFSG.Quasithin.ChapterB

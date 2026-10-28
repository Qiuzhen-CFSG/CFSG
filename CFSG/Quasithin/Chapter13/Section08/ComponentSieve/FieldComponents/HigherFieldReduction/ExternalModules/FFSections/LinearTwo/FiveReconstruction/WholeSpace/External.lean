module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.CentralSections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.Lift
public import Theory.Representation.BinaryAlternatingNaturalCohomology
public import Theory.Representation.BinaryPermutation.ThreeTensor

/-!
# Splitting the central quotient in the external five-letter branch

The marked constituent and its two-conjugate orbit give coordinates on W,
by `CentralSections` and `Lift`. Restricted to K*, those coordinates are
two copies of the natural A₅ module. Its first cohomology vanishes, so the
extension with central quotient U/W splits: U = W + C_U(K*). The already
proved central-bottom calculation makes this sum direct.

This is a partial reduction of the external alternative (a) of 13.8.20.
It does not prove W = U. The remaining obligation is to exclude the normal
summand C_U(K*) using genuinely earlier ambient information. In particular,
full X*-commutator generation does not exclude a K*-central natural
S₃ summand. No splitting or vanishing whole-module centralizer is assumed.

The theorem uses the literal U_H/V₁ carrier and the original constituent
and multiplicity equivalences. Its premises are precisely the available
representation data and W = [U_H/V₁,K*], the F.9.18(6) conclusion. It makes
no claim that these representation data alone imply the whole-space
assertion, or that they discharge the surrounding source setup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.1.6(1),
printed p.408, F.9.18(6), printed pp.325–326, and the exceptional A₅ constituent
in the proof of 13.8.20, printed p.954.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor
open Representation.OneCohomology
open scoped TensorProduct IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.WholeSpace.External

private theorem pair_principal_surjective
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) D V) (hτ : Function.Surjective (principal τ)) :
    Function.Surjective (principal (τ.prod τ)) := by
  intro f
  let f₁ : cocycles τ := ⟨fun g => (f.val g).1, fun g h => congrArg Prod.fst (f.property g h)⟩
  let f₂ : cocycles τ := ⟨fun g => (f.val g).2, fun g h => congrArg Prod.snd (f.property g h)⟩
  obtain ⟨v₁, hv₁⟩ := hτ f₁
  obtain ⟨v₂, hv₂⟩ := hτ f₂
  refine ⟨(v₁, v₂), ?_⟩
  apply Subtype.ext
  funext g
  exact Prod.ext (congrArg (fun c : cocycles τ => c.val g) hv₁)
    (congrArg (fun c : cocycles τ => c.val g) hv₂)

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (K : Subgroup D) (s : S₃ →* D)
  (W : Subrepresentation ρ)

private theorem factors_H1_subsingleton (c : FactorCoordinates W.toRepresentation K s) :
    Subsingleton (H1 (W.toRepresentation.comp K.subtype)) := by
  let τ := BinaryPermutation.alternatingCoreRepresentation (Fin 5)
  let d := c.moduleEquiv.trans BinaryPermutation.ThreeTensor.pairEquiv
  have hd (k : K) (v : W.toSubmodule) :
      d (W.toRepresentation k.val v) = (τ.prod τ) (c.component k) (d v) := by
    have h := c.intertwines k 1 v
    simp only [map_one, mul_one] at h
    change BinaryPermutation.ThreeTensor.pairEquiv (c.moduleEquiv (W.toRepresentation k.val v)) = _
    rw [h]
    exact BinaryPermutation.ThreeTensor.pairEquiv_equivariant
      (BinaryPermutation.coreRepresentation (Fin 5)) (c.component k).val (c.moduleEquiv v)
  let e := H1Congr (W.toRepresentation.comp K.subtype) (τ.prod τ) c.component d hd
  let : Subsingleton (H1 (τ.prod τ)) :=
    Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr
      (pair_principal_surjective τ
        (BinaryPermutation.alternatingCore_principal_surjective (Fin 5) (by simp) (by decide))))
  exact e.injective.subsingleton

private theorem factors_sup_fixed_eq_top
    (c : FactorCoordinates W.toRepresentation K s)
    (hW : W.toSubmodule = subspaceCommutator ρ ⊤ K) :
    W.toSubmodule ⊔ fixedSpace ρ K = ⊤ := by
  let WK : Subrepresentation (ρ.comp K.subtype) :=
    ⟨W.toSubmodule, fun k => W.apply_mem_toSubmodule k.val⟩
  let : Subsingleton (H1 WK.toRepresentation) := factors_H1_subsingleton ρ K s W c
  have hq : HasTrivialQuotient WK :=
    CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.central_quotient_of_moved_eq ρ K W hW
  apply top_unique
  intro v _
  exact (extensionClass_eq_zero_iff WK hq v).mp (Subsingleton.elim _ _)

open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open Theory.GroupTheory
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections

variable {G : Type*} [Group G]
    (H K₀ X V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [(Source.starImage H K₀).Normal]
    (ρ₀ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (s₀ : S₃ →* Source.Hstar H)
    (hs : ∀ (k : Source.starImage H K₀) g, Commute (k : Source.Hstar H) (s₀ g))
    (W₀ : Subrepresentation ρ₀)

/-- The actual two-conjugate moved orbit has the K*-fixed space as a direct
complement in the literal source module. Excluding that complement remains
an ambient-source obligation; no whole-space conclusion is asserted here. -/
theorem source_central_complement
    {E N : Type*} [Group E] [AddCommGroup N] [Module (ZMod 2) N]
    (σ : Representation (ZMod 2) E N)
    (e : MarkedActionEquiv σ (offenderSubgroup σ) (generalizedFitting E)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
    (r : ConstituentRealization ρ₀ (Source.starImage H K₀) σ (generalizedFitting E))
    (a : SectionMultiplicity ρ₀ s₀ (LinearTwo.centralBottom ρ₀ (Source.starImage H K₀) W₀) W₀
      ≃ₗ[ZMod 2] N)
    (ha : ∀ k v,
      a (sectionMultiplicityAction ρ₀ (Source.starImage H K₀).subtype s₀ hs
        (LinearTwo.centralBottom ρ₀ (Source.starImage H K₀) W₀) W₀ k v) =
      σ (r.component k) (a v))
    (hmark : (alternatingGroup (Fin 3)).map s₀ = Source.starImage H X)
    (hgen : subspaceCommutator ρ₀ ⊤ (Source.starImage H X) = ⊤)
    (hne : r.space ≠ r.space.map (ρ₀ (s₀ cubic)))
    (horbit : W₀.toSubmodule = r.space ⊔ r.space.map (ρ₀ (s₀ cubic)))
    (hmoved : W₀.toSubmodule = subspaceCommutator ρ₀ ⊤ (Source.starImage H K₀)) :
    IsCompl W₀.toSubmodule (fixedSpace ρ₀ (Source.starImage H K₀)) := by
  have hC := centralBottom_eq_bot ρ₀ (Source.starImage H K₀) σ _ _ e r.component
    W₀ r.space r.irrPlus r.linearEquiv r.component_intertwines (s₀ cubic) hne horbit
  let c := upperFactorCoordinates ρ₀ (Source.starImage H K₀) σ _ _ e s₀ hs
    (LinearTwo.centralBottom ρ₀ (Source.starImage H K₀) W₀) W₀ hC r.component a
    (by rw [hmark]; exact hgen) ha
  have hd : Disjoint W₀.toSubmodule (fixedSpace ρ₀ (Source.starImage H K₀)) := by
    rw [horbit]
    exact orbit_disjoint_fixed ρ₀ (Source.starImage H K₀) σ _ _ e r.component
      r.space r.irrPlus r.linearEquiv r.component_intertwines (s₀ cubic) hne
  exact ⟨hd, codisjoint_iff.mpr (factors_sup_fixed_eq_top ρ₀ (Source.starImage H K₀) s₀ W₀ c hmoved)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.WholeSpace.External

end

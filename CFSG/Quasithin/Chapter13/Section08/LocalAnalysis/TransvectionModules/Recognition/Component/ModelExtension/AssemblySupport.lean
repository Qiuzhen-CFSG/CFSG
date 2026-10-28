module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.Extensions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SevenExtension
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# Normality and the full seven-letter source action

The product supplied by 13.7.6(3) makes its C-component the two-residual
of H, by the subnormal supplement theorem. Thus normality is proved before
extending the component action. The natural A₇ coordinates obtained from
the actual central cover then extend to the full S₇ actor in the same
coordinates, by linear-centralizer rigidity and the given transvection.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.4.2(2), p.57; 13.7.6(3), pp.938–940; 13.8.5, p.947.
-/

@[expose] public section
open Subgroup Representation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

/-- The earlier set product discharges relative component normality. -/
theorem component_normal_of_product {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    (hp : (H : Set G) = (K : Set G) * (T : Set G)) :
    (K.subgroupOf H).Normal := by
  let := hK.perfect
  have hperfect : IsPPerfect 2 (K.subgroupOf H) := by
    intro N hN hpN
    let := hN
    have hsub : Subsingleton ((K.subgroupOf H) ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent _ hpN.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  have he := pResidual_eq_of_subnormal_product (K.subgroupOf H) ((T : Subgroup G).subgroupOf H)
    hK.subnormal hperfect T.isPGroup'.comap_subtype
    (fun g => by
      obtain ⟨k, hk, t, ht, he⟩ := Set.mem_mul.mp (show g.val ∈ (K : Set G) * (T : Set G) from hp ▸ g.property)
      exact ⟨⟨k, hKH hk⟩, hk, ⟨t, hTH ht⟩, ht, Subtype.ext he⟩)
  rw [← he]
  infer_instance

variable {G : Type*} [Group G] [Finite G] {H K V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The recognized seven-letter section gives the entire natural S₇ module.
Both intrinsic component coordinates and full-actor equivariance are retained. -/
theorem alternatingSeven_full_module_of_section
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)) eK)
    (t : Source.Hstar H) (ht : IsTransvection ρ t) :
    ∃ eH : Source.Hstar H ≃* Equiv.Perm (Fin 7),
      ∃ eV : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 7),
        (∀ k : Source.starImage H K, eH k = (componentModelEquiv hKH hK eK k).val) ∧
        ∀ a v, eV (ρ a v) = BinaryPermutation.coreRepresentation (Fin 7) (eH a) (eV v) := by
  let hn := component_normal_of_product T hTH hKH hK hprod
  let : (Source.starImage H K).Normal :=
    Subgroup.Normal.map hn (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective (pCore 2 H))
  obtain ⟨eV, heV⟩ := seven_core_of_section hKH hK ρ hρ hgen eK hs
  obtain ⟨eH, heK, heH⟩ := SevenExtension.symmetricSeven_of_core_extension
    (Source.starImage H K) ρ (faithful_of_centralizer_le_core ρ hρ hcentralizer)
      (componentModelEquiv hKH hK eK) eV heV t ht
  exact ⟨eH, eV, heK, heH⟩

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
end

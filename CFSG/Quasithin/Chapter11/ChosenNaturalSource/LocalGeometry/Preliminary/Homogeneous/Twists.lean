module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Homogeneous.Quotient
public import Theory.Representation.ConjugateRep

/-!
# Homogeneity from the normalizer's action on the chosen type

An intertwiner for each inverse conjugation twist identifies every translate
of the seed with its original component-module type. Those translates generate
the literal full quotient, so its entire space is the seed's isotypic component.
The G₂ application constructs all the intertwiners from its natural marking.

Source: Aschbacher--Smith, 11.0.3(2), printed p.760, using 3.2.2(3).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
section Span
open Representation.BinaryOffender.Homogeneous
variable {H W X : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]

private theorem homogeneous_part_of_generating_twists
    (ρ : Representation (ZMod 2) H W) (N : Subgroup H) [N.Normal]
    (θ : Representation (ZMod 2) N X) (hθ : IsIrreducible θ)
    (j : X →ₗ[ZMod 2] W) (hj : Function.Injective j)
    (he : ∀ n x, j (θ n x) = ρ n (j x))
    (ht : ∀ g : H, ∃ e : X ≃ₗ[ZMod 2] X, ∀ n x,
      e (θ n x) = θ (⟨g⁻¹ * n.val * g, by simpa using
        (inferInstance : N.Normal).conj_mem n.val n.property g⁻¹⟩ : N) (e x))
    (hgen : ∀ U : Subrepresentation ρ, j.range ≤ U.toSubmodule → U = ⊤) :
    ∃ I : Subrepresentation (ρ.comp N.subtype),
      IsIrreducible I.toRepresentation ∧ homogeneousPart I ⊤ = ⊤ := by
  let I : Subrepresentation (ρ.comp N.subtype) := ⟨j.range, by
    rintro n _ ⟨x, rfl⟩
    exact ⟨θ n x, he n x⟩⟩
  let e : X ≃ₗ[ZMod 2] I.toSubmodule := LinearEquiv.ofInjective j hj
  have he' (n : N) (x : X) : e (θ n x) = I.toRepresentation n (e x) :=
    Subtype.ext (he n x)
  let a : ActionEquiv θ I.toRepresentation := ⟨MulEquiv.refl N, e, he'⟩
  have hi := ExtensionConsequences.irreducible_of_equiv
    (ExtensionConsequences.actionSymm a) hθ
  let c := conjugateSubrepresentationOrderIso ρ N
  have hs (g : H) : SameModule I (c g I) := by
    obtain ⟨b, hb⟩ := ht g
    let m : I.toSubmodule ≃ₗ[ZMod 2] (c g I).toSubmodule :=
      (I.toSubmodule.equivMapOfInjective (ρ g) (ρ.apply_bijective g).1).trans
        (LinearEquiv.ofEq _ _ (conjugateSubrepresentationOrderIso_toSubmodule ρ N g I).symm)
    refine ⟨e.symm.trans (b.trans (e.trans m)), ?_⟩
    intro n v
    obtain ⟨x, rfl⟩ := e.surjective v
    change m (e (b (e.symm (I.toRepresentation n (e x))))) =
      (c g I).toRepresentation n (m (e (b (e.symm (e x)))))
    rw [← he', e.symm_apply_apply, e.symm_apply_apply, hb]
    apply Subtype.ext
    change ρ g (j (θ _ (b x))) = ρ n (ρ g (j (b x)))
    rw [he]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  let Q : Subrepresentation (ρ.comp N.subtype) := ⨆ g : H, c g I
  have hstable (x : H) : c x Q ≤ Q := by
    simp only [Q, OrderIso.map_iSup]
    refine iSup_le fun g => ?_
    rw [← conjugateSubrepresentationOrderIso_mul]
    exact le_iSup (fun g => c g I) (x * g)
  let U : Subrepresentation ρ := ⟨Q.toSubmodule, by
    intro x v hv
    have hm : ρ x v ∈ Q.toSubmodule.map (ρ x) := ⟨v, hv, rfl⟩
    rw [← conjugateSubrepresentationOrderIso_toSubmodule] at hm
    exact hstable x hm⟩
  have htop : Q.toSubmodule = ⊤ := by
    have hu : U = ⊤ := hgen U (by
      change I ≤ Q
      have h := le_iSup (fun g => c g I) (1 : H)
      simpa only [c, conjugateSubrepresentationOrderIso_one] using h)
    exact congrArg Subrepresentation.toSubmodule hu
  refine ⟨I, hi, top_unique ?_⟩
  calc
    ⊤ = (⨆ g : H, c g I).toSubmodule := htop.symm
    _ = ⨆ g : H, (c g I).toSubmodule := toSubmodule_iSup _
    _ ≤ homogeneousPart I ⊤ := iSup_le fun g => le_iSup_of_le (c g I)
      (le_iSup_of_le ⟨le_top, hs g⟩ le_rfl)
end Span
section Twists
variable (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Invariance of the seed's binary type under the actual normalizer action
makes the literal full quotient a single isotypic component. The G₂ consumer
discharges this premise using the inner-field automorphism theorem. -/
theorem fullModule_homogeneous_of_normalizer_twists
    (ht : ∀ g : normalizer (L : Set G),
      ∃ e : D.chosenCentralQuotient ≃ₗ[ZMod 2] D.chosenCentralQuotient,
        ∀ l v, e (D.chosenCentralAction l v) =
          D.chosenCentralAction (L.normalizerMonoidHom g l) (e v)) :
    letI := fullModule_elementary D S
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    ∃ σ : Representation (ZMod 2) M
        (Additive (U ⧸ (centralizer (L : Set G)).subgroupOf U)),
      (∃ I : Subrepresentation (σ.comp (L.subgroupOf M).subtype),
        IsIrreducible I.toRepresentation ∧ homogeneousPart I ⊤ = ⊤) ∧
      (∀ (g : M) (v : U),
        σ g (Additive.ofMul (QuotientGroup.mk'
          ((centralizer (L : Set G)).subgroupOf U) v)) =
          Additive.ofMul (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U)
            ⟨(g : G) * (v : G) * (g : G)⁻¹,
              (mem_normalizer_iff.mp (le_normalizer_componentOrbit V M g.property) v).mp
                v.property⟩)) := by
  let := fullModule_elementary D S
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let N := L.subgroupOf M
  let : N.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let a : N ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let θ := D.chosenCentralAction.comp a.toMonoidHom
  obtain ⟨σ, _, _, hσ⟩ := fullModule_quotient_semisimple_transitive D S
  have hi : IsIrreducible D.chosenCentralAction :=
    (irreducible_comp_surjective_iff (QuotientGroup.mk' (pCore 2 L))
      (QuotientGroup.mk'_surjective _) D.centralQuotientAction).mpr D.centralQuotientAction_irreducible
  have hθ : IsIrreducible θ :=
    (irreducible_comp_surjective_iff a.toMonoidHom a.surjective D.chosenCentralAction).mpr hi
  refine ⟨σ, ?_, hσ⟩
  apply homogeneous_part_of_generating_twists σ N θ hθ
    (seedQuotientMap D U (le_componentOrbit V M))
    (seedQuotientMap_injective D U (le_componentOrbit V M))
  · intro n q
    exact seedQuotientMap_equivariant D U (le_componentOrbit V M)
      (L.le_normalizer.trans (le_normalizer_componentOrbit V M))
      (σ.comp (inclusion L.le_normalizer))
      (fun l u => hσ (inclusion L.le_normalizer l) u) (a n) q
  · intro g
    obtain ⟨b, hb⟩ := ht g⁻¹
    refine ⟨b, ?_⟩
    intro n x
    change b (D.chosenCentralAction (a n) x) = D.chosenCentralAction (a _) (b x)
    rw [hb]
    apply congrArg (fun l : L => D.chosenCentralAction l (b x))
    apply Subtype.ext
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change (g : G)⁻¹ * n.val.val * ((g : G)⁻¹)⁻¹ = (g : G)⁻¹ * n.val.val * (g : G)
    rw [inv_inv]
  · exact fullQuotient_seed_generates D U (le_componentOrbit V M) σ
      (le_normalizer_componentOrbit V M) hσ rfl
end Twists


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary

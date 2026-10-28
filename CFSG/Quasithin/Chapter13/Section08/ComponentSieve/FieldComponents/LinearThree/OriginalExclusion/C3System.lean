module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.CoreBounds
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeFamily
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeC3Local

/-!
# The C₃-system consumer for the abelian binary branch

The original natural A₆ action identifies the left vertex quotient with A₆
or S₆, preserving both possibilities. The binary whole quotient and central
commutator pairing give the strict left-core size bound required by I.5.
Together with the original generated-core identity, these construct the
actual three-vertex system (LT, K₀L₂T, H) once its local residues are supplied.
I.5 then makes the center of the actual H trivial, contradicting V₁ ≤ Z(H).

The middle quotient, chamber intersection and rank-two residues remain
explicit in this conditional application. Their proof and the final original
13.8.19–21 assembly stay with qt-d-138-fields-source. The preceding source
hypotheses remain with their existing producers and qt-d-1381-source.
Neither a nonabelian V_H assumption nor a C₃ recognition conclusion is an
input. Source: Aschbacher–Smith, 13.7.6(1), printed p.940, and 13.8.19,
printed p.953; I.5, printed pp.419–420.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open Subgroup Representation SourceCompletion
open TransvectionRecognition.Component.ModelExtension
open Geometry.CoveredProduct.ResidualPlacement
open Section07.NaturalAction Section07.OrdinarySource.LinearThreeFamily
open Section07.OrdinarySource.LinearThreeC3Local Quasithin.I5
open TransvectionQuotients.FiveSeed TransvectionQuotients.FiveSeed.BarMarking
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private theorem source_binary_natural_kernel
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    (permutation (localNaturalSetup c.localSetup)).ker =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let d := localNaturalSetup c.localSetup
  have h := c.f9 H c.component.local_overgroup
  obtain ⟨eL⟩ := source_binary_local_ordinary c e₀
  let α := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hα : Function.Surjective α := d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : (permutation d).ker = actorKernel (L ⊔ (T : Subgroup G)) V := by
    ext x
    exact Section07.permutation_eq_one_iff d x
  have hCT := centralizer_le_sylow_of_natural_action L V T d.normalizes_L
    (permutation d) hk α hα (permutation_L d) eL
  ext x
  constructor
  · intro hx
    have hc : x.val ∈ centralizer (V : Set G) := (Section07.permutation_eq_one_iff d x).mp hx
    have ht : x.val ∈ (T : Subgroup G) := hCT ⟨hc,x.property⟩
    have hm : x.val ∈ (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 :=
      h.sylow_centralizer ▸ ⟨ht,hc⟩
    obtain ⟨y,hy,he⟩ := hm
    exact (Subtype.ext he : y=x) ▸ hy
  · intro hx
    apply (Section07.permutation_eq_one_iff d x).mpr
    exact d.chosen.core_centralizes (mem_map_of_mem _ hx)

/-- The actual left C₃ vertex has ordinary alternating or symmetric quotient.
The abelian span does not justify selecting S₆ in advance. -/
theorem source_binary_left_quotient
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    Nonempty (((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≃*
      alternatingGroup (Fin 6)) ∨
    Nonempty (((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≃*
      Equiv.Perm (Fin 6)) := by
  let d := localNaturalSetup c.localSetup
  let π := permutation d
  let e := (QuotientGroup.quotientMulEquivOfEq
    (source_binary_natural_kernel c e₀).symm).trans (QuotientGroup.quotientKerEquivRange π)
  have hd : π.range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le (alternating_le_range d)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact Or.inr ⟨e.trans ((MulEquiv.subgroupCongr (index_eq_one.mp hi)).trans topEquiv)⟩
  · exact Or.inl ⟨e.trans (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi))⟩

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Assemble I.5 on the literal three source vertices. The middle quotient
and the three local residues are the only remaining C₃ premises. -/
noncomputable def source_binary_system_of_residues
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL)
    (hc : chamberSubgroup (family (L ⊔ (T : Subgroup G)) (middle T L K V₂) H) =
      (T : Subgroup G).subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H))
    (eJ : (middle T L K V₂ ⧸ pCore 2 (middle T L K V₂)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hpoint : let F := family (L ⊔ (T : Subgroup G)) (middle T L K V₂) H
      RankTwoParabolics (F 0) ((chamberSubgroup F).subgroupOf (F 0))
        (localParabolic F 0 1) (localParabolic F 0 2))
    (hline : let F := family (L ⊔ (T : Subgroup G)) (middle T L K V₂) H
      RankTwoParabolics (F 1) ((chamberSubgroup F).subgroupOf (F 1))
        (localParabolic F 1 0) (localParabolic F 1 2))
    (hplane : let F := family (L ⊔ (T : Subgroup G)) (middle T L K V₂) H
      RankTwoParabolics (F 2) ((chamberSubgroup F).subgroupOf (F 2))
        (localParabolic F 2 0) (localParabolic F 2 1)) :
    DSystem .C3 ((L ⊔ (T : Subgroup G)) ⊔ H : Subgroup G) := by
  let A := L ⊔ (T : Subgroup G)
  let J := middle T L K V₂
  let F := family A J H
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  let e0 : F 0 ≃* A := subgroupOfEquivOfLe le_sup_left
  let e1 : F 1 ≃* J := subgroupOfEquivOfLe (middle_le_generated hKH)
  let e2 : F 2 ≃* H := subgroupOfEquivOfLe le_sup_right
  have hlarge : 32 < Nat.card (pCore 2 (F 0)) := by
    have hc0 : Nat.card (pCore 2 (F 0)) = Nat.card (pCore 2 A) := by
      rw [←pCore_map_iso 2 e0,card_map_of_injective e0.injective]
    have hcA : Nat.card (A.pCoreIn 2) = Nat.card (pCore 2 A) :=
      card_map_of_injective A.subtype_injective
    rw [hc0,←hcA]
    have hb := source_binary_large_local_core c act e₀
    change 32 < Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2)
    omega
  exact {
    family := F
    finite_vertex := fun _ => inferInstance
    point_A3 := fun he => nomatch he
    point_C3 := fun _ => by
      let e := QuotientGroup.congr _ _ e0 (pCore_map_iso 2 e0)
      rcases source_binary_left_quotient c e₀ with hL | hS
      · obtain ⟨f⟩ := hL
        exact Or.inl ⟨e.trans f⟩
      · obtain ⟨f⟩ := hS
        exact Or.inr ⟨e.trans f⟩
    line_quotient := ⟨(QuotientGroup.congr _ _ e1 (pCore_map_iso 2 e1)).trans eJ⟩
    plane_quotient := ⟨(QuotientGroup.congr _ _ e2 (pCore_map_iso 2 e2)).trans e₀⟩
    sylow := family_sylow A J H le_sup_right hc
    point_parabolics := hpoint
    line_parabolics := hline
    plane_parabolics := hplane
    generate := family_generate A J H
    core_free := family_core_free A J H le_sup_right hc
      (c.f9 H c.component.local_overgroup).generated_core
    nondegenerate := fun _ => Or.inr hlarge }

/-- Apply I.5 to the original H, whose original central line is nontrivial.
The remaining local-residue premises stay with this field-sieve owner. -/
theorem source_binary_false_of_residues
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL)
    (hc : chamberSubgroup (family (L ⊔ (T : Subgroup G)) (middle T L K V₂) H) =
      (T : Subgroup G).subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ H))
    (eJ : (middle T L K V₂ ⧸ pCore 2 (middle T L K V₂)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hpoint : let F := family (L ⊔ (T : Subgroup G)) (middle T L K V₂) H
      RankTwoParabolics (F 0) ((chamberSubgroup F).subgroupOf (F 0))
        (localParabolic F 0 1) (localParabolic F 0 2))
    (hline : let F := family (L ⊔ (T : Subgroup G)) (middle T L K V₂) H
      RankTwoParabolics (F 1) ((chamberSubgroup F).subgroupOf (F 1))
        (localParabolic F 1 0) (localParabolic F 1 2))
    (hplane : let F := family (L ⊔ (T : Subgroup G)) (middle T L K V₂) H
      RankTwoParabolics (F 2) ((chamberSubgroup F).subgroupOf (F 2))
        (localParabolic F 2 0) (localParabolic F 2 1)) : False :=
  source_false_of_C3_system (localNaturalSetup c.localSetup) (c.f9 H c.component.local_overgroup)
    (source_binary_system_of_residues c act e₀ hc eJ hpoint hline hplane) rfl
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion

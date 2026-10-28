module
public import Theory.Representation.CliffordRestriction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.SourceGeometry
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Clifford and conjugation adapters for the original exchanged action

The component is normal in the residual, and the residual is normal in the
actor quotient. Clifford restriction is therefore semisimple on that component
for every irreducible ambient module. Conjugating a component Borel fixed-space
inequality gives the other component inequality; the two joins are precisely
the original product Borel and residual. The local consumer uses H/O₂(H) and
the actual intrinsic component map throughout.

Source: Aschbacher–Smith D.3.6–7, pp.196–197; 15.3.65, p.1152.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction RepresentationReduction.SourceRestrictions.Cases.Exchanged
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

theorem fixedSpace_le_conjugate {C K : Subgroup D}
    (h : fixedSpace ρ C ≤ fixedSpace ρ K) (t : D) :
    fixedSpace ρ (C.conjBy t) ≤ fixedSpace ρ (K.conjBy t) := by
  intro v hv
  have hinv (x : V) : ρ t⁻¹ (ρ t x) = x := by
    rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hw : ρ t⁻¹ v ∈ fixedSpace ρ C := by
    intro c
    have hh := congrArg (ρ t⁻¹) (hv ⟨t*c*t⁻¹,⟨c,c.property,rfl⟩⟩)
    change ρ t⁻¹ (ρ (t*(c : D)*t⁻¹) v) = ρ t⁻¹ v at hh
    change ρ (c : D) (ρ t⁻¹ v) = ρ t⁻¹ v
    simpa only [map_mul,Module.End.mul_apply,hinv] using hh
  intro k
  obtain ⟨x,hx,hxk⟩ := k.property
  change ρ (k : D) v = v
  rw [← hxk]
  change ρ (t*x*t⁻¹) v = v
  rw [map_mul,map_mul]
  change ρ t (ρ x (ρ t⁻¹ v)) = v
  have hxf : ρ x (ρ t⁻¹ v) = ρ t⁻¹ v := h hw ⟨x,hx⟩
  rw [hxf,← Module.End.mul_apply,← map_mul,mul_inv_cancel,
    map_one,Module.End.one_apply]

theorem fixedSpace_le_product_of_conjugate {K K₀ B C : Subgroup D} {t : D}
    (hpair : K ⊔ K.conjBy t = K₀) (hB : C ⊔ C.conjBy t ≤ B)
    (h : fixedSpace ρ C ≤ fixedSpace ρ K) :
    fixedSpace ρ B ≤ fixedSpace ρ K₀ := by
  rw [← hpair]
  apply le_fixedSpace_sup ρ
  · intro v hv
    exact h (fun c => hv ⟨c,(le_sup_left.trans hB) c.property⟩)
  · intro v hv
    exact fixedSpace_le_conjugate ρ h t (fun c => hv ⟨c,(le_sup_right.trans hB) c.property⟩)

theorem fixedSpace_le_residual_of_component
    {K K₀ T B C : Subgroup D} (geo : ExchangedGeometry K K₀ T B C)
    (h : fixedSpace ρ C ≤ fixedSpace ρ K) :
    fixedSpace ρ B ≤ fixedSpace ρ K₀ := by
  obtain ⟨t,ht,hout⟩ := geo.moved
  obtain ⟨hp,_,_,_,hb⟩ := geo.pair t ht hout
  exact fixedSpace_le_product_of_conjugate ρ hp hb.ge h
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MonoidAlgebra
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction.SourceRestrictions.Cases.Exchanged
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)

theorem component_restriction_semisimple
    {K K₀ T B C : Subgroup D} [K₀.Normal]
    (geo : ExchangedGeometry K K₀ T B C) (hi : IsIrreducible ρ) :
    IsSemisimpleModule (ZMod 2)[K] (Representation.asModule (ρ.comp K.subtype)) :=
  irreducible_restriction_semisimple_of_normal_chain ρ hi K K₀ geo.component_le geo.component_normal

variable {G : Type*} [Group G] [Finite G]

theorem local_component_restriction_semisimple {T : Sylow 2 G} {H M : Subgroup G}
    (hH : H ∈ minimalSylowOutsideFamily T M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.prop.1.2) ⊤)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple H)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup G).subgroupOf H = ⊤) (hn : ¬K.Normal)
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) V) (hi : IsIrreducible σ) :
    IsSemisimpleModule (ZMod 2)[actorImage H (K.map H.subtype)]
      (Representation.asModule (σ.comp (actorImage H (K.map H.subtype)).subtype)) := by
  have hr : actorImage H (residual H) = pResidual 2 (H ⧸ pCore 2 H) := by
    unfold actorImage residual subgroupOf
    rw [comap_map_eq_self_of_injective H.subtype_injective,map_pResidual_quotient]
  let : (actorImage H (residual H)).Normal := by rw [hr]; infer_instance
  exact component_restriction_semisimple σ (local_geometry hH hP hSQTK K hK hqK hgen hn) hi
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged

module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSCoverKernel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSVertexAction

/-!
# The kernel criterion on the original G₂ moving cover

A genuine offender in the faithful ambient natural action lies in the marked
component. Transport through that exact component equivalence applies the
orthogonal-cover kernel criterion without changing the original actor or
projection. In particular the entire central kernel lies in the offender's
moved subspace, and its nonzero vectors are precisely those moved vectors
that are not single commutators.

The final theorem constructs this data from the original Sylow-normalizer
escape, on the central-omega moved section of LT/O₂(LT). This supplies the
central-cover input to the comparison at the two critical vertices; their
embedded kernels still have to be identified before comparing field actions.
Source: MS93 (1.5)(iv), p.843, and (3.2), pp.865--866. The line-action owner
retains that comparison and the 11.2.3 consumer, with final source assembly
in qt-d-1222-natural-normalizer-source.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative Pointwise
open Atlas.G2
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS

open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Representation.BinaryOffender

/-- The kernel criterion on the actual ambient moved-section action. The
critical actor's containment in the component is deduced from offending. -/
theorem moved_cover_offender_kernel
    {J V : Type*} [Group J] [Finite J] [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
    (E : BinaryField) (hE : E.degree = 2)
    (s : MovedSection ρ B) (e : ActionEquiv (s.action.comp B.subtype) (binaryG2 E))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hf : Function.Injective (MovedSection.ambientAction s e))
    (A : Subgroup J) (hA : IsOffender (MovedSection.ambientAction s e) A) :
    (MovedSection.coverProjection s e).toLinearMap.ker ≤
      Coinvariants.ker (s.space.toRepresentation.comp A.subtype) ∧
    ∀ w : s.space.toSubmodule,
      w ∈ Coinvariants.ker (s.space.toRepresentation.comp A.subtype) → w ≠ 0 →
      (MovedSection.coverProjection s e w = 0 ↔
        ¬ ∃ a ∈ A, ∃ v, s.space.toRepresentation a v - v = w) := by
  have hAB := (ambient_offender_rank_six E hE (MovedSection.ambientAction s e) B
    e.groupEquiv (MovedSection.ambientAction_component s e) hf A hA).1
  let C := (A.subgroupOf B).map e.groupEquiv.toMonoidHom
  have hC : IsOffender (NaturalOffenders.binaryNatural (F := E.Carrier)) C :=
    (hA.subgroupOf _ hAB).map_equivariant ((MovedSection.ambientAction s e).comp B.subtype)
      (NaturalOffenders.binaryNatural (F := E.Carrier)) e.groupEquiv.toMonoidHom
      e.groupEquiv.injective (LinearEquiv.refl (ZMod 2) _)
      (fun b v => MovedSection.ambientAction_component s e b v)
  have hc (a : C) : (e.groupEquiv.symm a.val : J) ∈ A := by
    obtain ⟨b,hb,hb'⟩ := a.property
    rw [←hb']
    change (e.groupEquiv.symm (e.groupEquiv b)).val ∈ A
    rw [e.groupEquiv.symm_apply_apply]
    exact hb
  have ha (a : A) : e.groupEquiv ⟨a.val,hAB a.property⟩ ∈ C :=
    mem_map_of_mem e.groupEquiv.toMonoidHom a.property
  have hm : Coinvariants.ker ((MovedSection.coverAction s e).comp C.subtype) =
      Coinvariants.ker (s.space.toRepresentation.comp A.subtype) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨a,v⟩,rfl⟩
      exact Coinvariants.sub_mem_ker (ρ := s.space.toRepresentation.comp A.subtype)
        ⟨(e.groupEquiv.symm a.val : J),hc a⟩ v
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨a,v⟩,rfl⟩
      have hh := Coinvariants.sub_mem_ker
        (ρ := (MovedSection.coverAction s e).comp C.subtype)
        ⟨e.groupEquiv ⟨a.val,hAB a.property⟩,ha a⟩ v
      change s.space.toRepresentation (e.groupEquiv.symm (e.groupEquiv ⟨a.val,hAB a.property⟩)) v - v ∈ _ at hh
      rw [e.groupEquiv.symm_apply_apply] at hh
      exact hh
  have hcard : Nat.card E.Carrier = 2^2 := by rw [E.card_eq,hE]
  refine ⟨?_,?_⟩
  · rw [←hm]
    exact full_cover_offender_kernel_le_moved (MovedSection.coverAction s e)
      hcard (by decide) (MovedSection.coverProjection s e) hp C hC
  · intro w hw hne
    rw [full_cover_offender_kernel (MovedSection.coverAction s e) hcard (by decide)
      (MovedSection.coverProjection s e) hp C hC w (hm.symm ▸ hw) hne]
    apply not_congr
    constructor
    · rintro ⟨c,hc',v,he⟩
      exact ⟨(e.groupEquiv.symm c : J),hc ⟨c,hc'⟩,v,he⟩
    · rintro ⟨a,ha',v,he⟩
      refine ⟨e.groupEquiv ⟨a,hAB ha'⟩,ha ⟨a,ha'⟩,v,?_⟩
      change s.space.toRepresentation (e.groupEquiv.symm (e.groupEquiv ⟨a,hAB ha'⟩)) v - v = w
      rwa [e.groupEquiv.symm_apply_apply]

/-- The central kernel and its intrinsic description on every actual offender. -/
def HasNaturalMovingKernel
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) J V) (B : Subgroup J) [B.Normal] : Prop :=
  let s := MovedSection.ofNormal ρ B
  ∃ E : BinaryField, E.degree = 2 ∧
  ∃ e : ActionEquiv (s.action.comp B.subtype) (binaryG2 E),
    IsCover (MovedSection.coverProjection s e) ∧
    ∀ A, IsOffender (MovedSection.ambientAction s e) A →
    (MovedSection.coverProjection s e).toLinearMap.ker ≤
      Coinvariants.ker (s.space.toRepresentation.comp A.subtype) ∧
    ∀ w : s.space.toSubmodule,
      w ∈ Coinvariants.ker (s.space.toRepresentation.comp A.subtype) → w ≠ 0 →
      (MovedSection.coverProjection s e w = 0 ↔
        ¬ ∃ a ∈ A, ∃ v, s.space.toRepresentation a v - v = w)

private theorem moving_kernel_of_cover
    {J V : Type*} [Group J] [Finite J] [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) J V) (B : Subgroup J) [B.Normal]
    (hcent : centralizer (B : Set J) = ⊥) (h : HasNaturalMovingCover ρ B) :
    HasNaturalMovingKernel ρ B := by
  obtain ⟨E,hE,e,hp⟩ := h
  let s := MovedSection.ofNormal ρ B
  have hf : Function.Injective (MovedSection.ambientAction s e) := by
    apply MovedSection.ambientAction_faithful s e _ hcent
    intro g h heq
    apply Natural.action_injective E.Carrier
    exact LinearMap.ext (fun v => LinearMap.congr_fun heq v)
  exact ⟨E,hE,e,hp,fun A hA => moved_cover_offender_kernel E hE s e hp hf A hA⟩

open CFSG.Quasithin.Chapter12.Section02
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V₀ : Subgroup G}
  (D : ChosenModule T L V₀) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
local notation "H" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "K" => Subgroup.subgroupOf L (L ⊔ (T : Subgroup G))

include D S m in
private theorem source_component_centric :
    centralizer ((K).map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  have hF : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact (show (2:ℕ)^1 < 2^S.field.degree from
      Nat.pow_lt_pow_right (by decide) S.nonbinary)
  let : IsSimpleGroup (Model S.field.Carrier) := Atlas.G2.isSimple hF
  let : IsSimpleGroup (K ⧸ pCore 2 K) :=
    (source_component_model D S m).some.isSimpleGroup
  apply (ChapterC.MSCentralOrbit.component_image_structure K
    ((T : Subgroup G).subgroupOf H) S.source.maximal_faithful.1.1.1
    (T.isPGroup'.of_equiv (subgroupOfEquivOfLe le_sup_right).symm) ?_).2.2.2.2
  intro h
  have hh : (h : G) ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left L (T : Subgroup G)
      D.sylow_normalizes_component]
    exact h.property
  obtain ⟨k,hk,r,hr,he⟩ := hh
  exact ⟨⟨k,mem_sup_left hk⟩,hk,⟨r,mem_sup_right hr⟩,hr,Subtype.ext he⟩

include D S m in
/-- The original escape supplies the central-kernel criterion on the original
central-omega moved cover, keeping its literal O₂(LT) quotient. -/
theorem source_initial_cover_kernel
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    let q := QuotientGroup.mk' (pCore 2 H)
    let B := (K).map q
    let X := omegaCenterIn (pCore 2 H)
    ∃ hker : q.ker = centralizer (X : Set H), ∃ hn : B.Normal,
      letI := hn
      HasNaturalMovingKernel (NormalElementaryQuotient.representation X q
        (QuotientGroup.mk'_surjective _) hker) B := by
  obtain ⟨hk,hn,h⟩ := source_initial_cover D S m hescape
  let := hn
  exact ⟨hk,hn,moving_kernel_of_cover _ _ (source_component_centric D S m) h⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS

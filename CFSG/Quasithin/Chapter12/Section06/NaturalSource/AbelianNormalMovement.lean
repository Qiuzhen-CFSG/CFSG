module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.F9
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.Setup
public import Theory.Representation.BinaryConjugationSection.FullMovement
public import Theory.Representation.BinaryOffender.IrreducibleDiagonal
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Full movement by a normal subgroup of the original local actor

Lift a nontrivial normal subgroup of H-star in the image of L₁T through
the literal two-core quotient. F.9 irreducibility makes its commutator
with V₅ fill V₅ modulo V₁: the zero case puts its normal preimage in the
original seed-kernel core. Normality then propagates movement through
U_H = ⟨V₅^H⟩. The conclusion uses the prescribed action on U_H/V₁.

Consequently such an actor cannot centralize a nontrivial subgroup K
and fix [U_H/V₁,K]. Commuting the two displacement operators would make
K fix the whole faithful section. This argument does not require an odd
order assumption or a splitting of the section's fixed space.

Source: Aschbacher--Smith 12.6.31, printed p.836, using F.9.1(a),(b)
and F.9.2, printed pp.317--318. Earlier geometry remains explicit.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)]
  (a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁)

include hz hTV hTz hbound hH in
/-- A nontrivial normal subgroup in the original local image moves all
of the literal section U_H/V₁. -/
theorem SourceHypothesis.original_normal_local_actor_full_movement
    (C : Subgroup (H ⧸ pCore 2 H)) [C.Normal] (hC : C ≠ ⊥)
    (hplace : C ≤ actorImage H ((D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G))) :
    subspaceCommutator a.representation ⊤ C = ⊤ := by
  let E := D.fullSetup hZ T z
  let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let q := QuotientGroup.mk' (pCore 2 H)
  let X := (C.comap q).map H.subtype
  have hXH : X ≤ H := map_subtype_le _
  have hNX : H ≤ normalizer (X : Set G) := by
    simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map, range_subtype] using
      (C.comap q).le_normalizer_map H.subtype
  have hXimage : actorImage H X = C := by
    change ((X.subgroupOf H).map q) = C
    change (((C.comap q).map H.subtype).subgroupOf H).map q = C
    rw [subgroupOf,comap_map_eq_self_of_injective H.subtype_injective]
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hQ : H.pCoreIn 2 ≤ normalizer (E.V₅ : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans
      h.commutator_UH_QH_le_point).trans h.point_lt.le
  have hn : X ≤ normalizer (E.V₅ : Set G) := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := hplace hx
    have hk : y⁻¹*x ∈ pCore 2 H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (y⁻¹*x)=1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hm := (normalizer (E.V₅ : Set G)).mul_mem (h.local_normalizes hy)
      (hQ (mem_map_of_mem H.subtype hk))
    change (y:G)*((y:G)⁻¹*(x:G)) ∈ normalizer (E.V₅ : Set G) at hm
    simpa only [mul_inv_cancel_left, Subgroup.subtype_apply] using hm
  have hlocal : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₅ : Set G) := h.local_normalizes
  have hNZ : H ≤ normalizer (E.V₁ : Set G) :=
    h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hseed : E.V₅ = ⁅X,E.V₅⁆ ⊔ E.V₁ := by
    let W := ⁅X,E.V₅⁆ ⊔ E.V₁
    have hWV : W ≤ E.V₅ := sup_le
      (le_normalizer_iff_commutator_le_right.mp hn) h.point_lt.le
    have hNW : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (W : Set G) := by
      intro g hg
      change g ∈ normalizer ((⁅X,E.V₅⁆ ⊔ E.V₁ : Subgroup G) : Set G)
      rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (hNX (h.local_le hg)),
        mem_normalizer_iff_map_conj_eq.mp (hlocal hg),
        mem_normalizer_iff_map_conj_eq.mp (hNZ (h.local_le hg))]
    rcases h.irreducible W le_sup_right hWV hNW with he | he
    · exfalso
      let : (E.V₁.subgroupOf H).Normal := h.point_normal
      let : (X.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hNX
      have hXK : X.subgroupOf H ≤ centralizerModulo ⊤ (E.V₅.subgroupOf H)
          (E.V₁.subgroupOf H) := by
        intro x hx
        apply mem_centralizerModulo_iff.mpr
        refine ⟨mem_top _,fun v hv => ?_⟩
        have hc : ⁅X,E.V₅⁆ ≤ E.V₁ := le_sup_left.trans he.le
        rw [commutator_comm] at hc
        exact hc (commutator_mem_commutator hv hx)
      have hXQ : X.subgroupOf H ≤ pCore 2 H :=
        (normal_le_normalCore.mpr hXK).trans h.kernel_core
      apply hC
      rw [←hXimage]
      exact (Subgroup.map_eq_bot_iff _).mpr (hXQ.trans_eq (QuotientGroup.ker_mk' _).symm)
    · exact he.symm
  have hmove : E.UH H = ⁅X,E.UH H⁆ ⊔ E.V₁ := by
    have hNU : H ≤ normalizer (E.UH H : Set G) := le_normalizer_conjugateSpanBy E.V₅ H
    apply le_antisymm
    · apply conjugateSpanBy_le
      · rw [hseed]
        exact sup_le_sup (commutator_mono le_rfl (le_conjugateSpanBy _ _)) le_rfl
      · intro g hg
        rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,map_commutator,
          mem_normalizer_iff_map_conj_eq.mp (hNX hg),
          mem_normalizer_iff_map_conj_eq.mp (hNU hg),
          mem_normalizer_iff_map_conj_eq.mp (hNZ hg)]
    · exact sup_le (le_normalizer_iff_commutator_le_right.mp (hXH.trans hNU))
        (h.point_lt.le.trans (le_conjugateSpanBy _ _))
  let c : BinaryConjugationSection H (E.UH H) E.V₁ (a.representation.comp q) := {
    section_le := a.le_local
    kernel_le := a.kernel_le
    normalized := a.normalizes
    coordinates := (MulEquiv.multiplicativeAdditive _).symm.toMonoidHom.comp
      (QuotientGroup.mk' (E.V₁.subgroupOf (E.UH H)))
    onto := (MulEquiv.multiplicativeAdditive _).symm.surjective.comp
      (QuotientGroup.mk'_surjective _)
    kernel_eq := by ext u; exact QuotientGroup.eq_one_iff u
    equivariant := fun g u => (a.conjugation g u).symm }
  have hm := c.subspaceCommutator_eq_top_of_movement X hXH hmove
  rw [subspaceCommutator_comp_map] at hm
  change subspaceCommutator a.representation ⊤ (actorImage H X) = ⊤ at hm
  rwa [hXimage] at hm

include hz hTV hTz hbound hH in
/-- A commuting nontrivial subgroup has a moved space that this normal
local actor cannot fix pointwise. Both actions are on the original section. -/
theorem SourceHypothesis.original_normal_local_actor_not_fix_moved
    (C K : Subgroup (H ⧸ pCore 2 H)) [C.Normal] (hC : C ≠ ⊥) (hK : K ≠ ⊥)
    (hplace : C ≤ actorImage H ((D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
    (hc : C ≤ centralizer (K : Set (H ⧸ pCore 2 H))) :
    ¬ subspaceCommutator a.representation ⊤ K ≤ fixedSpace a.representation C := by
  intro hf
  have hm := S.original_normal_local_actor_full_movement D hZ z hz hTV hTz hbound hH a C hC hplace
  apply hK
  apply bot_unique
  intro k hk
  have he : a.representation k = 1 := by
    apply LinearMap.ext
    intro v
    apply fixes_commutatorSubspace_of_commutes_of_displacement_fixed a.representation
      (X := C) (b := k)
    · intro c hcC
      exact hc hcC k hk
    · intro w
      exact hf (Submodule.subset_span ⟨k,hk,w,Submodule.mem_top,rfl⟩)
    · rw [hm]
      trivial
  exact a.faithful (he.trans (map_one a.representation).symm)
end CFSG.Quasithin.Chapter12.Section06

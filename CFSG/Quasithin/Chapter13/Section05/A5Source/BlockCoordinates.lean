module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ModuleIntersections
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Chapter13

/-!
# The original A₅ coordinates for the G.2.4 substitution

The orbit of the original line spans V by irreducibility. The marked
five-point action identifies the actual image of L in LT/O₂(LT) with
A₅: its projection kernel is precisely O₂(L). These identifications
retain the literal projection and conjugation maps required by G.2.4.
Source: Aschbacher–Smith13.5.14(3–4), printed p.919.
-/
@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open ChapterG.Section02.AlternatingFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem line_span_eq : conjugateSpanBy V₁ L = V := by
  have h1 : V₁ ≤ V := d.flag.one_le_two.trans d.flag.two_le_V
  have hV : conjugateSpanBy V₁ L ≤ V := conjugateSpanBy_le h1 d.chosen.normalizes
  rcases d.irreducible_module _ hV (le_normalizer_conjugateSpanBy V₁ L) with h | h
  · have hz : V₁ = ⊥ := bot_unique ((le_conjugateSpanBy V₁ L).trans_eq h)
    have hc := d.flag.one_card
    simp [hz] at hc
  · exact h

theorem local_core_intersection : L ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 = L.pCoreIn 2 := by
  rw [← (d.local_centralizers d.normalizes_L).1,← inf_assoc,inf_of_le_left (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)]
  exact d.centralizer_eq_core

variable (H : Subgroup G)

/-- The literal projection with its original L domain made explicit. -/
def blockProjection (T : Sylow 2 G) (L V₁ V₃ H : Subgroup G) :
    L →* (chapter13Setup V₁ V₃ L T H).star L :=
  starProjection (chapter13Setup V₁ V₃ L T H)

/-- The original quotient projection has the same kernel as the module action. -/
theorem blockProjection_kernel :
    (blockProjection T L V₁ V₃ H).ker = pCore 2 L := by
  ext l
  rw [MonoidHom.mem_ker,Subtype.ext_iff]
  change (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))
    ⟨l,mem_sup_left l.property⟩ = 1 ↔ l ∈ pCore 2 L
  refine (QuotientGroup.eq_one_iff (N := pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
    (⟨l,mem_sup_left l.property⟩ : (L ⊔ (T : Subgroup G) : Subgroup G))).trans ?_
  constructor
  · intro hl
    have hc : (l : G) ∈ L ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      ⟨l.property,mem_map_of_mem (L ⊔ (T : Subgroup G)).subtype hl⟩
    obtain ⟨k,hk,he⟩ := d.local_core_intersection ▸ hc
    exact (Subtype.ext he : k=l) ▸ hk
  · intro hl
    have hc : (l : G) ∈ L ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      d.local_core_intersection.symm ▸ mem_map_of_mem L.subtype hl
    obtain ⟨k,hk,he⟩ := hc.2
    exact (Subtype.ext he : k=⟨l,mem_sup_left l.property⟩) ▸ hk

noncomputable def blockModel :
    (chapter13Setup V₁ V₃ L T H).star L ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientKerEquivOfSurjective
    (blockProjection T L V₁ V₃ H) (starProjection_surjective _)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (d.blockProjection_kernel H)).trans d.quotient)

@[simp] theorem blockModel_projection (l : L) :
    d.blockModel H (starProjection (chapter13Setup V₁ V₃ L T H) l) = d.flag.module.action l := by
  let f := blockProjection T L V₁ V₃ H
  let e := QuotientGroup.quotientKerEquivOfSurjective f (starProjection_surjective _)
  have he : e.symm (f l) = QuotientGroup.mk' f.ker l := by
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  change d.quotient ((QuotientGroup.quotientMulEquivOfEq (d.blockProjection_kernel H))
    (e.symm (f l))) = _
  rw [he]
  exact d.quotient_mk l

noncomputable def blockCoordinateEmbedding :
    Multiplicative (BinaryPermutation.core (Fin 5)) →* (chapter13Setup V₁ V₃ L T H).VL :=
  d.flag.module.map.codRestrict _ (fun x => by
    change d.flag.module.map x ∈ conjugateSpanBy V₁ L
    rw [d.line_span_eq]
    exact d.flag.module.range_eq.le ⟨x,rfl⟩)

theorem blockCoordinateEmbedding_bijective : Function.Bijective (d.blockCoordinateEmbedding H) := by
  constructor
  · intro x y he
    exact d.flag.module.injective (congrArg Subtype.val he)
  · intro v
    have hv : (v : G) ∈ V := d.line_span_eq ▸ v.property
    obtain ⟨x,hx⟩ := d.flag.module.range_eq.symm ▸ hv
    exact ⟨x,Subtype.ext hx⟩

noncomputable def blockCoordinates : (chapter13Setup V₁ V₃ L T H).VL ≃*
    Multiplicative (BinaryPermutation.core (Fin 5)) :=
  (MulEquiv.ofBijective (d.blockCoordinateEmbedding H)
    (d.blockCoordinateEmbedding_bijective H)).symm

@[simp] theorem map_blockCoordinates (v : (chapter13Setup V₁ V₃ L T H).VL) :
    d.flag.module.map (d.blockCoordinates H v) = v :=
  congrArg Subtype.val ((MulEquiv.ofBijective (d.blockCoordinateEmbedding H)
    (d.blockCoordinateEmbedding_bijective H)).apply_symm_apply v)

theorem blockCoordinates_equivariant (l : L) (v : (chapter13Setup V₁ V₃ L T H).VL) :
    d.blockCoordinates H ⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (L_normalizes_VL (chapter13Setup V₁ V₃ L T H) l.property) v).mp v.property⟩ =
      Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5)
        (d.blockModel H (starProjection (chapter13Setup V₁ V₃ L T H) l)).val
        (d.blockCoordinates H v).toAdd) := by
  apply d.flag.module.injective
  rw [d.map_blockCoordinates,d.blockModel_projection,← d.flag.module.equivariant]
  change (l : G) * (v : G) * (l : G)⁻¹ =
    MulAut.conj (l : G) (d.flag.module.map (d.blockCoordinates H v))
  rw [d.map_blockCoordinates]
  rfl

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context

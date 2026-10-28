module

public import CFSG.Quasithin.Chapter13.Section07.SpanGrowth
public import Theory.GroupTheory.CentralCoreInvolutionLift
public import Theory.GroupTheory.PCoreImage
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.TransverseInvolution

/-!
# The actual involution chosen before13.7.10

An even involution moves the marked natural point to a nonorthogonal point.
The literal quotient L/O₂,Z(L) lifts it to an element squaring into O₂(L):
a central kernel above the two-core has odd order. Inverting the lift aligns
with the source's right-conjugation convention. Its displaced point lies
outside V₃=V₁-perpendicular, so together with V₃ it generates V.

The resulting original g∈L feeds the existing intersection-exchange theorem
with its actual square condition. The final source consumer constructs the
witness, core containment, point escape and both centralizer conclusions.
Only genuine F.9 applicability and earlier abelianness of U_H remain.
Source: Aschbacher–Smith, choice before13.7.10 and13.7.10(1),(6), pp.941–942.
-/

@[expose] public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

private theorem naturalImage_mono {A B : Subgroup G} (hAB : A ≤ B) : image d A ≤ image d B := by
  intro w hw
  obtain ⟨v, hv, he⟩ := (mem_image d A w).mp hw
  exact (mem_image d B w).mpr ⟨v, hAB hv, he⟩

private theorem sup_eq_top_of_off_hyperplane (w : natural (Fin 6))
    (hw : w ∉ image d V₃) : image d V₃ ⊔ Submodule.span (ZMod 2) {w} = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [Submodule.finrank_sup_span_singleton hw, image_dim d V₃ d.seed_le 3 d.seed_card,
    finrank_natural_even (Fin 6) (by decide)]
  decide

/-- The actual source involution and spanning conjugate point; both the square
and the displacement are constructed from the original natural marking. -/
theorem exists_chosen_conjugator : ∃ g : L,
    (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
      (inclusion le_sup_left g)) ^ 2 = 1 ∧
    V ≤ V₃ ⊔ ChapterF.Section09.Setup.conjugate V₁ (g : G) := by
  obtain ⟨z, hz, hz1⟩ : ∃ z : G, z ∈ V₁ ∧ z ≠ 1 := by
    have hn : V₁ ≠ ⊥ := by intro he; have hh := d.line_card; rw [he] at hh; simp at hh
    obtain ⟨z, hz, hnz⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hn)
    exact ⟨z, hz, by simpa only [mem_bot] using hnz⟩
  let zV : V := ⟨z, d.seed_le (d.plane_le_seed (d.line_le_plane hz))⟩
  have hz0 : (d.coordinate zV).toAdd ≠ 0 := by
    intro he
    have h := d.coordinate.injective (he.trans (map_one d.coordinate).symm)
    exact hz1 (congrArg Subtype.val h)
  obtain ⟨a, hasq, hpair⟩ :=
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.TransverseInvolution.exists_nonorthogonal_involution
      (d.coordinate zV).toAdd hz0
  let α : L →* alternatingGroup (Fin 6) :=
    d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hα : Function.Surjective α := d.local_quotient.surjective.comp
    (QuotientGroup.mk'_surjective (centralCore L))
  have hk : pCore 2 L ≤ α.ker := by
    intro l hl
    have hq : QuotientGroup.mk' (pCore 2 L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    have hlc : l ∈ centralCore L := by change QuotientGroup.mk' (pCore 2 L) l ∈ center _; rw [hq]; exact one_mem _
    change d.local_quotient (QuotientGroup.mk' (centralCore L) l) = 1
    have hh : QuotientGroup.mk' (centralCore L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hlc
    rw [hh, map_one]
  have hc : α.ker.map (QuotientGroup.mk' (pCore 2 L)) ≤ center (L ⧸ pCore 2 L) := by
    rintro _ ⟨l, hl, rfl⟩
    have hh : QuotientGroup.mk' (centralCore L) l = 1 :=
      d.local_quotient.injective (hl.trans (map_one d.local_quotient).symm)
    exact (QuotientGroup.eq_one_iff l).mp hh
  obtain ⟨l, hl, hlsq⟩ := α.exists_square_mem_twoCore_lift hα hk hc a hasq
  let g := l⁻¹
  have hcore : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer d.normalizes_L)
  have hgcore : ((g : L) : G) ^ 2 ∈ (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 := by
    have hgL : g ^ 2 ∈ pCore 2 L := by
      dsimp only [g]
      rw [inv_pow]
      exact inv_mem hlsq
    exact hcore (mem_map_of_mem L.subtype hgL)
  refine ⟨g, ?_, ?_⟩
  · have he : (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) g)^2 ∈
        pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
      change ((inclusion le_sup_left g)^2 : (L ⊔ (T : Subgroup G) : Subgroup G)) ∈ _
      obtain ⟨x, hx, hxg⟩ := hgcore
      have heq : x = (inclusion le_sup_left g)^2 := Subtype.ext hxg
      exact heq ▸ hx
    exact (map_pow _ _ _).symm.trans ((QuotientGroup.eq_one_iff _).mpr he)
  · let y : V := V.normalizerMonoidHom ⟨l.val, d.normalizes_V (mem_sup_left l.property)⟩ zV
    have hycoord : (d.coordinate y).toAdd = naturalRepresentation (Fin 6) a.val (d.coordinate zV).toAdd := by
      have he := d.conjugation l zV
      change (d.coordinate y).toAdd = alternatingNaturalRepresentation (Fin 6) (α l) _ at he
      rw [hl] at he
      exact he
    have hynot : (d.coordinate y).toAdd ∉ image d V₃ := by
      intro hy
      rw [seed_perpendicular d] at hy
      have hh := hy (d.coordinate zV).toAdd ((mem_image d V₁ _).mpr ⟨zV, hz, rfl⟩)
      rw [hycoord, hpair] at hh
      exact one_ne_zero hh
    let N := V₃ ⊔ ChapterF.Section09.Setup.conjugate V₁ (g : G)
    have hyN : y.val ∈ N := by
      apply mem_sup_right
      change y.val ∈ V₁.map (MulAut.conj ((g : L) : G)⁻¹).toMonoidHom
      refine ⟨z, hz, ?_⟩
      change (l.val⁻¹)⁻¹ * z * ((l.val⁻¹)⁻¹)⁻¹ = l.val * z * l.val⁻¹
      simp only [inv_inv]
    have him : image d V₃ ⊔ Submodule.span (ZMod 2) {(d.coordinate y).toAdd} ≤ image d N := by
      apply sup_le (naturalImage_mono d le_sup_left)
      apply Submodule.span_le.mpr
      intro w hw
      rcases Set.mem_singleton_iff.mp hw with rfl
      exact (mem_image d N _).mpr ⟨y, hyN, rfl⟩
    rw [sup_eq_top_of_off_hyperplane d _ hynot] at him
    intro v hv
    have hh : (d.coordinate ⟨v, hv⟩).toAdd ∈ image d N := him (Submodule.mem_top)
    obtain ⟨w, hw, he⟩ := (mem_image d N _).mp hh
    have hwv : w = (⟨v, hv⟩ : V) := d.coordinate.injective he
    have hh : (⟨v, hv⟩ : V).val ∈ N := hwv ▸ hw
    exact hh

/-- The source choice and literal13.7.10(1),(6), with no witness or desired
intersection/centralizer hypothesis supplied by the caller. -/
theorem exists_source_intersections {H : Subgroup G}
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ∃ g : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left g)) ^ 2 = 1 ∧
      ¬ ChapterF.Section09.Setup.conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃ ∧
      ⁅(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).DH (g : G),
        ChapterF.Section09.Setup.conjugate (Section08.Source.UH H V₃) (g : G)⁆ = ⊥ ∧
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).DHg (g : G) ≤
        H ⊓ centralizer (Section08.Source.UH H V₃ : Set G) ∧
      ⁅(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).DH (g : G),
        ChapterF.Section09.Setup.conjugate (Section08.Source.VH H V) (g : G) ⊓
          (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2⁆ = ⊥ ∧
      ⁅(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).DHg (g : G),
        Section08.Source.VH H V⁆ ≤ V₁ := by
  obtain ⟨g, hs, hspan⟩ := exists_chosen_conjugator d
  exact ⟨g, hs, source_intersections_of_natural d h (inclusion le_sup_left g) hs
    hspan hU hV⟩

end CFSG.Quasithin.Chapter13.Section07

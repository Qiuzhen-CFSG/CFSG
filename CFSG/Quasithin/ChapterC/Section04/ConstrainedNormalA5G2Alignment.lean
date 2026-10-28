module

public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalA5SmallExclusions
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.G2ParabolicFromSource
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2

/-!
# The original normal A₅ seed in the G₂ star marking

The literal marked local intersection contains a full Sylow subgroup,
because its conjugate is a root parabolic. Its actual seed image remains
a C-component with A₅ two-core quotient. The full-Sylow local placement
theorem therefore identifies that same image with a root local residual
and forces the coefficient field to have four elements.

Source: Aschbacher--Smith C.4.1 and 12.7.5, printed pp.151 and 840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Atlas.G2 Atlas.G2.LieParabolicSetup

/-- The original marked seed is a literal G₂ parabolic residual, over
the forced field of four elements. -/
theorem constrained_normal_a5_g2_alignment
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
    {H M L R V : Subgroup G}
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (eA5 : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J)
    (e : starImage (J.map H.subtype) R (J.map H.subtype) ≃* Model F)
    (hF : 4 ≤ Nat.card F) :
    Nat.card F = 4 ∧ ∃ g : Model F,
      let B := (L.subgroupOf (J.map H.subtype)).map
        (e.toMonoidHom.comp (toStarImage (J.map H.subtype) R))
      B.map (MulAut.conj g).toMonoidHom = local₁ ∨
        B.map (MulAut.conj g).toMonoidHom = local₂ := by
  let K := J.map H.subtype
  let C := starImage K R K
  let A := (L.subgroupOf K).map (toStarImage K R)
  let P := (starM K R M).subgroupOf C
  let B := A.map e.toMonoidHom
  let N := P.map e.toMonoidHom
  obtain ⟨hAP,_,hAc⟩ := h.constrained_normal_star_seed_component hn J hJ hq hout hf
  obtain ⟨a⟩ := h.constrained_normal_a5_star_seed_quotient hn eA5 J hJ hq hout hf
  have hBN : B ≤ N := map_mono hAP
  have hBc : (B.subgroupOf N).IsCComponent := by
    have hh := hAc.map_equiv (e.subgroupMap P)
    have he : (A.subgroupOf P).map (e.subgroupMap P).toMonoidHom = B.subgroupOf N := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact mem_map_of_mem e.toMonoidHom hy
      · rintro ⟨y,hy,he⟩
        exact ⟨⟨y,hAP hy⟩,hy,Subtype.ext he⟩
    exact he ▸ hh
  let aB := e.subgroupMap A
  let aQ : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ aB (pCore_map_iso 2 aB)).symm.trans a
  obtain ⟨g,hg⟩ := C27Source.star_g2_marked_parabolic_from_source
    (h.constrained_source_input J hJ hq hout hf) e hF
  let c := MulAut.conj g
  have hSN : (sylow (F := F) : Subgroup (Model F)) ≤ N.map c.toMonoidHom := by
    rcases hg with hg | hg
    · rw [hg,sylow_coe]
      exact (show unipotent ≤ Atlas.G2.borel from le_sup_left).trans borel_le_parabolic₁
    · rw [hg,sylow_coe]
      exact (show unipotent ≤ Atlas.G2.borel from le_sup_left).trans borel_le_parabolic₂
  let S := (sylow (F := F)).mapSurjective (f := c.symm.toMonoidHom) c.symm.surjective
  have hSP : (S : Subgroup (Model F)) ≤ N := by
    have hh := map_mono (f := c.symm.toMonoidHom) hSN
    have he : c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id (Model F) := by
      apply MonoidHom.ext
      intro x
      exact c.symm_apply_apply x
    change ((sylow (F := F) : Subgroup (Model F)).map c.symm.toMonoidHom) ≤ N
    simpa only [map_map,he,map_id] using hh
  have hlocal : B ∈ ChapterA.Section03.localCComponents S :=
    hBc.subgroupOf_of_le le_sup_left (sup_le hBN hSP)
  have hP : N ≠ ⊤ := by
    intro ht
    have hp : P = ⊤ := by
      have hh := congrArg (comap e.toMonoidHom) ht
      simpa only [N,comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective,
        comap_top] using hh
    exact (C27Source.star_thompson_intersection_from_source
      (h.constrained_source_input J hJ hq hout hf)).2.not_ge (subgroupOf_eq_top.mp hp)
  have hproper : B ≠ ⊤ := fun hb => hP (top_unique (hb ▸ hBN))
  have hh := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2.five_section_placement
    (by omega : 2 < Nat.card F) S B hlocal hproper aQ
  simpa only [B,A,map_map] using hh

end CFSG.Quasithin.ChapterC.HypothesisC28

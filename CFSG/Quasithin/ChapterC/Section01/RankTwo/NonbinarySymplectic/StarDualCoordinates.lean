module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StarQuotient
public import Theory.Representation.DualCoverFromConjugationSection

/-!
# Natural coordinates in a marked star quotient

For an arbitrary finite holomorph graph, the moving cover and the marked
star quotient have the same full kernel on the moving subgroup. Their
projections therefore identify the natural module with its actual image in
the star quotient. The first star comparison and the quotient's fixed-space
condition make this inclusion a dual cover. This coordinate calculation
requires no characteristic minimum, field restriction or radical saturation.

Source: the dual-module step of MS93 (3.4), printed p.869.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit

theorem marked_star_dual_cover
    {M : Type*} [Group M] [Finite M] (T : Subgroup M)
    {E J V : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
    (Y : Subgroup T) (s₀ : MovedSection ρ B)
    (e : ActionEquiv (s₀.action.comp B.subtype) (binaryNatural (K := E)))
    (he : IsCover (MovedSection.coverProjection s₀ e))
    (j : Multiplicative s₀.space.toSubmodule →* FreeAmalgam T)
    (hjr : j.range = U T (alpha T))
    (s : SourceStarQuotient T Y J)
    (hκL : ((Ltilde T (alpha T)).subgroupOf
      (stabilizer T (alpha T))).map s.quotient = B)
    (hconj : ∀ (g : stabilizer T (alpha T)) (v : s₀.space.toSubmodule),
      j (Multiplicative.ofAdd (s₀.space.toRepresentation (s.quotient g) v)) =
        (g : FreeAmalgam T)*j (Multiplicative.ofAdd v)*(g : FreeAmalgam T)⁻¹)
    (hker : ∀ v : s₀.space.toSubmodule, MovedSection.coverProjection s₀ e v = 0 ↔
      j (Multiplicative.ofAdd v) ∈
        centralizer (Ltilde T (alpha T) : Set (FreeAmalgam T)))
    (hAQ : sourceStarAlpha T Y ≤ Q T (alpha T))
    (hcomm : ⁅sourceStarAlpha T Y,Ltilde T (alpha T)⁆ ≤
      U T (alpha T)) :
    let γ : L (K := E) →* J := B.subtype.comp e.groupEquiv.symm.toMonoidHom
    ∃ i : (binaryNatural (K := E)).IntertwiningMap (s.action.comp γ),
      Function.Injective i ∧ IsDualCover i.range ∧
      ∀ w, w ∈ i.toLinearMap.range ↔
        ∃ a : sourceStarAlpha T Y, (a : FreeAmalgam T) ∈
          U T (alpha T) ∧ (s.sectionData.coordinates a).toAdd = w := by
  let γ : L (K := E) →* J := B.subtype.comp e.groupEquiv.symm.toMonoidHom
  have hγ : γ.range = B := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.groupEquiv.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  let L₀ := Ltilde T (alpha T)
  let S := stabilizer T (alpha T)
  have hLS : L₀ ≤ S := Ltilde_le_stabilizer _
  let f₀ : L₀ →* B := (s.quotient.comp (inclusion hLS)).codRestrict B (by
    intro l
    exact hκL.le (mem_map_of_mem s.quotient (show inclusion hLS l ∈ L₀.subgroupOf S from l.property)))
  have hf₀ : Function.Surjective f₀ := by
    intro c
    obtain ⟨l,hl,he⟩ := (hκL.symm ▸ c.property : c.val ∈ (L₀.subgroupOf S).map s.quotient)
    exact ⟨⟨l.val,hl⟩,Subtype.ext he⟩
  let f := e.groupEquiv.toMonoidHom.comp f₀
  have hf : Function.Surjective f := e.groupEquiv.surjective.comp hf₀
  have hγf (l : L₀) : γ (f l) = s.quotient (inclusion hLS l) := by
    change (e.groupEquiv.symm (e.groupEquiv (f₀ l)) : J) = _
    rw [e.groupEquiv.symm_apply_apply]
    rfl
  let σ := s.action.comp γ
  let π := s.sectionData.coordinates
  have hUA : U T (alpha T) ≤ sourceStarAlpha T Y :=
    (U_le_Z _).trans (Z_le_sourceStarAlpha _ _)
  have hLA : L₀ ≤ normalizer (sourceStarAlpha T Y : Set (FreeAmalgam T)) :=
    hLS.trans (sourceStarAlpha_normalized _ _)
  have hact (l : L₀) (a : sourceStarAlpha T Y) :
      (π ⟨(l : FreeAmalgam T)*a*(l : FreeAmalgam T)⁻¹,
        (mem_normalizer_iff.mp (hLA l.property) a).mp a.property⟩).toAdd =
          σ (f l) (π a).toAdd := by
    change _ = s.action (γ (f l)) (π a).toAdd
    rw [hγf]
    exact s.sectionData.equivariant (inclusion hLS l) a
  have hjact (l : L₀) (v : s₀.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s₀ e (f l) v)) =
        (l : FreeAmalgam T)*j (Multiplicative.ofAdd v)*(l : FreeAmalgam T)⁻¹ := by
    change j (Multiplicative.ofAdd (s₀.space.toRepresentation (γ (f l)) v)) = _
    rw [hγf]
    exact hconj (inclusion hLS l) v
  have hkernel (v : s₀.space.toSubmodule) : MovedSection.coverProjection s₀ e v = 0 ↔
      π ⟨j (Multiplicative.ofAdd v),hUA (hjr ▸ ⟨Multiplicative.ofAdd v,rfl⟩)⟩ = 1 := by
    have hvU : j (Multiplicative.ofAdd v) ∈ U T (alpha T) :=
      hjr ▸ ⟨Multiplicative.ofAdd v,rfl⟩
    have hvQ : j (Multiplicative.ofAdd v) ∈ Q T (alpha T) :=
      hAQ (hUA hvU)
    apply (hker v).trans
    exact (show (j (Multiplicative.ofAdd v) ∈ centralizer (L₀ : Set (FreeAmalgam T))) ↔
      j (Multiplicative.ofAdd v) ∈ sourceStarAlpha T Y ⊓ fixedCore T (alpha T)
      from ⟨fun hv => ⟨hUA hvU,hvQ,hv⟩,fun hv => hv.2.2⟩).trans
      (s.sectionData.coordinates_eq_one_iff ⟨j (Multiplicative.ofAdd v),hUA hvU⟩).symm
  have hmap : ((Ltilde T (alpha T)).subgroupOf S).map s.quotient = B := by
    exact hκL
  have hfixed : OneCohomology.fixed σ = ⊥ := by
    apply bot_unique
    intro v hv
    apply s.fixed_eq_bot.le
    intro c
    have hc : c.val ∈ B := hmap.le c.property
    obtain ⟨g,hg⟩ := (hγ.symm ▸ hc : c.val ∈ γ.range)
    change s.action c.val v = v
    rw [←hg]
    exact hv g
  obtain ⟨i,hi,hdual,hover,hrange⟩ := exists_dualCover_of_conjugation_section
    (sourceStarAlpha T Y) (U T (alpha T)) L₀ hUA hLA
    hcomm
    (MovedSection.coverAction s₀ e) σ (binaryNatural (K := E))
    (MovedSection.coverProjection s₀ e) he.1 j hjr π s.sectionData.onto f hf hjact hact hkernel hfixed
  exact ⟨i,hi,hdual,hrange⟩


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

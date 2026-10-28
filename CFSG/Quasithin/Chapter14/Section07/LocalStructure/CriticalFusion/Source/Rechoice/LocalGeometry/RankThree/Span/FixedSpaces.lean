module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Elementary
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Sections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.MarkedSpans

/-!
# The two original T-fixed decompositions in 14.7.70

The compatible earlier R₁ marking and the checked natural cover prove
C_(U/V₁)(R₁) = V/V₁ + ker(p) with the literal original actors. The original
projection identifies the T-fixed line of V/V₁ with the flag plane V₂/V₁.
Splitting the R₁-fixed space then gives the T-fixed decomposition, without
assuming that T fixes the whole kernel.

For one source critical path, T-normalization of E = V₁Zα makes the image
of Zα pointwise fixed. Its nonzero projection supplies the second complement
to the T-fixed kernel. This proves both sides of the displayed T-fixed
identity used immediately before the orbit-span calculation.

Inputs: Preliminary is supplied by qt-14-07-rechoice-preparation;
T-normalization by qt-14-07-rank-three-moved-plane; action descent by
14.5.15(4), producer qt-14-05; ModuleSeparation by 14.7.2(1), producer
qt-14-07-solvable; the compatible UpperMarking and LocalActors by the
14.3/14.7 producers qt-14-03 and qt-14-07. Their final discharge remains
with qt-14-07-rechoice-rank-three-action and its source assembly.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.64–65, printed pp.1069–1070, and proof of 14.7.70,
printed p.1074 (PDF p.1091).
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Span
open Subgroup Representation Chapter12.Section08 Preparation
open Preparation.MarkedSpans
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W) (s : d.ActionDescent)
include s

/-- The first identity of 14.7.65 uses the literal R₁ actor on the original section. -/
theorem original_R₁_fixed (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) :
    Representation.invariants (d.action.comp ((F.Ri L 1).subgroupOf F.H).subtype) =
      tilde d V ⊔ d.projection.toLinearMap.ker := by
  rw [← upper_eq_seed_sup_kernel d s mark sep actors]
  ext w
  constructor
  · intro hw g
    have hm : alternatingActor d.naturalQuotient g ∈
        ((F.Ri L 1).subgroupOf F.H).map d.qH := by
      rw [mark]
      exact mem_map_of_mem _ g.property
    obtain ⟨r, hr, he⟩ := hm
    change s.action (alternatingActor d.naturalQuotient g) w = w
    rw [← he, s.original]
    exact hw ⟨r, hr⟩
  · intro hw r
    have hm : d.qH r ∈ (Matrix.SpecialLinearGroup.upperUnipotent SL2FourNatural.F).map
        (alternatingActor d.naturalQuotient) := by
      rw [← mark]
      exact mem_map_of_mem _ r.property
    obtain ⟨g, hg, he⟩ := hm
    change d.action r w = w
    rw [← s.original, ← he]
    exact hw ⟨g, hg⟩

/-- The actual flag identifies the T-fixed line in V/V₁. -/
theorem seed_fixed (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) : tilde d V ⊓ fixedT d = tilde d (F.Vi 2) := by
  let := finite_original d
  let TH : Sylow 2 F.H := T.subtype (F.invariant 1)
  let P : Sylow 2 ChapterJ.S5 := TH.mapSurjective d.qH_surjective
  have hTP : (actorT (F := F)).map d.qH = (P : Subgroup ChapterJ.S5) :=
    (Sylow.coe_mapSurjective d.qH_surjective TH).symm
  have hupper a : alternatingActor d.naturalQuotient (SL2FourNatural.upper a) ∈ P :=
    show _ ∈ (P : Subgroup ChapterJ.S5) from hTP ▸ upper_mem_actorT d mark a
  have hn : ∀ x : actorT (F := F), ∀ w ∈ tilde d V, d.action x w ∈ tilde d V :=
    tilde_invariant d (by simpa only [F.last] using F.invariant 3)
  have hmap : (tilde d V).map d.projection.toLinearMap = SL2FourNatural.upperFixed :=
    upper_complement_image d.naturalQuotient s.projection d.projection_onto s.kernel_fixed _
      (upper_eq_seed_sup_kernel d s mark sep actors)
  have hdim := original_complement_fixed_finrank d.naturalQuotient d.action d.qH d.projection
    (actorT (F := F)) P hTP hupper (tilde d V) hn (seed_disjoint_kernel d sep) hmap
  exact (Submodule.eq_of_le_of_finrank_eq
    (le_inf (d.conjugationSection.imageSpace_mono (F.le_seed 2)) (plane_tilde_fixed d))
    ((plane_tilde_finrank d).trans hdim.symm)).symm

/-- The source T-fixed decomposition retains the original kernel and plane. -/
theorem fixed_eq_plane_sup_kernel (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) :
    fixedT d = tilde d (F.Vi 2) ⊔ (d.projection.toLinearMap.ker ⊓ fixedT d) := by
  have h := original_fixed_decomposition d.naturalQuotient d.action d.qH d.projection
    (actorT (F := F)) ((F.Ri L 1).subgroupOf F.H)
    (subgroupOf_mono F.H R₁_le_T) (tilde d V)
    (tilde_invariant d (by simpa only [F.last] using F.invariant 3))
    (seed_disjoint_kernel d sep) (original_R₁_fixed d s mark sep actors)
  rw [seed_fixed d s mark sep actors] at h
  exact h

variable (c : CriticalPath (L := L) F) (h : Preliminary d c)
omit s
include h

/-- T-normalization of E fixes its image pointwise, since |E/V₁|=2. -/
theorem opposite_fixed (hT : (T : Subgroup G) ≤ normalizer (E c : Set G)) :
    tilde d c.Zα ≤ fixedT d := by
  intro w hw
  obtain ⟨a, ha, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
  intro t
  exact flag_plane_fixed d.action d.conjugationSection
    (h.E_le_intersection.trans inf_le_left) (le_sup_left : F.Vi 1 ≤ E c)
    (by simpa using F.card 1 (by decide)) h.E_card
    t (hT t.property) a ((le_sup_right : c.Zα ≤ E c) ha)

include s
/-- Both products in the displayed T-fixed identity of 14.7.70 are literal images. -/
theorem fixed_decompositions (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) (hT : (T : Subgroup G) ≤ normalizer (E c : Set G)) :
    tilde d c.Zα ⊔ (d.projection.toLinearMap.ker ⊓ fixedT d) = fixedT d ∧
      fixedT d = tilde d (F.Vi 2) ⊔ (d.projection.toLinearMap.ker ⊓ fixedT d) := by
  let := finite_original d
  have hf := fixed_eq_plane_sup_kernel d s mark sep actors
  have hz := opposite_fixed d c h hT
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ c.Zα, a ∉ d.U₀ := by
    by_contra! he
    exact h.opposite_not_le he
  let aU : F.U := ⟨a, (h.opposite_le.trans (h.commutator_le.trans inf_le_left)) ha⟩
  let z : W := (d.conjugationSection.coordinates aU).toAdd
  have hzZ : z ∈ tilde d c.Zα :=
    (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨aU, ha, rfl⟩
  have hz0 : z ∉ d.projection.toLinearMap.ker := fun he => ha0 ((d.mem_U₀ aU).mpr he)
  obtain ⟨v, hv, k, hk, he⟩ := Submodule.mem_sup.mp (hf ▸ hz hzZ)
  have hv0 : v ≠ 0 := by
    intro hv0
    rw [hv0, zero_add] at he
    exact hz0 (he ▸ hk.1)
  have hline := eq_span_singleton_of_mem_of_finrank_eq_one
    (plane_tilde_finrank d) hv hv0
  constructor
  · apply le_antisymm (sup_le hz inf_le_right)
    apply le_trans hf.le
    apply sup_le _ le_sup_right
    rw [hline]
    apply Submodule.span_le.mpr
    intro x hx
    have hxv : x = v := Set.mem_singleton_iff.mp hx
    subst x
    have hvz : v = z - k := by rw [← he]; abel
    rw [hvz]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hzZ) (Submodule.mem_sup_right hk)
  · exact hf
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Span

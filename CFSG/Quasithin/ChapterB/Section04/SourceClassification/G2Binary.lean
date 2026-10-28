module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.G2Recognition
public import Theory.Representation.G2BinaryNaturalOffenders
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract

/-!
# The marked binary G₂ endpoint of B.4.2

Recognition identifies the literal quasisimple layer with G₂(2)′ and its
original module with the natural six-space. The full binary normalizer is
G₂(2), so the ambient actor embeds with this same marking. Every offender
contains a conjugate of the short root outside the derived subgroup;
hence the ambient embedding is surjective. The concrete model offenders
generate the whole group, have rank three, and give quadratic ratio one.

The resulting marked action identifies the actual layer inside the actual
offender-generated group. Neither an ambient extension nor its generation
is assumed. Source: Aschbacher–Smith B.4.2(4), B.4.6(13), and K.3.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceClassification
open Atlas.G2.Natural.BinaryNormalizer
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

omit [FiniteDimensional (ZMod 2) V] in
theorem g2_binary_ambient (h : ChapterK.RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    (M : ActionEquiv (ρ.comp L.subtype)
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype)) :
    ∃ f : G ≃* Full, (∀ l : L, f l = (M.groupEquiv l : Full)) ∧
      ∀ g v, M.linearEquiv (ρ g v) = Atlas.G2.Natural.action (ZMod 2) (f g) (M.linearEquiv v) := by
  let := h.layer_normal
  obtain ⟨f,hf,hmark,haction⟩ := ambient_embedding ρ L M.groupEquiv M.linearEquiv
    M.intertwines h.faithful
  have hD : Derived ≤ f.range := by
    intro x hx
    refine ⟨M.groupEquiv.symm ⟨x,hx⟩, ?_⟩
    rw [hmark, M.groupEquiv.apply_symm_apply]
  obtain ⟨A,hA⟩ := hff
  have hmap := hA.map_equivariant ρ (Atlas.G2.Natural.action (ZMod 2)) f hf M.linearEquiv haction
  obtain ⟨g,_,hg⟩ := Atlas.G2.NaturalOffenders.natural_offender_rootPair
    (n := 1) (by norm_num) (by decide) _ hmap
  have hcg : g * Atlas.G2.rootC 1 * g⁻¹ ∉ Derived := by
    intro hmem
    apply rootC_not_mem_derived
    have he := (inferInstance : Derived.Normal).conj_mem' _ hmem g
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using he
  have htop : f.range = ⊤ := eq_top_of_derived_le hD ((map_le_range _ _) hg) hcg
  exact ⟨MulEquiv.ofBijective f ⟨hf,MonoidHom.range_eq_top.mp htop⟩,hmark,haction⟩
theorem g2_binary_case (h : ChapterK.RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  obtain ⟨M⟩ := g2_binary_natural_action h e
  obtain ⟨f,hmark,haction⟩ := g2_binary_ambient h hff M
  have hinv (g : Full) (v : N) : M.linearEquiv.symm (Atlas.G2.Natural.action (ZMod 2) g v) =
      ρ (f.symm g) (M.linearEquiv.symm v) := by
    apply M.linearEquiv.injective
    rw [M.linearEquiv.apply_symm_apply, haction, f.apply_symm_apply, M.linearEquiv.apply_symm_apply]
  have hJ : offenderSubgroup ρ = ⊤ := by
    have hle : (⊤ : Subgroup Full) ≤ (offenderSubgroup ρ).comap f.symm.toMonoidHom := by
      rw [← generated_eq_top]
      apply iSup_le
      intro A
      apply iSup_le
      rintro ⟨hA,_⟩
      exact Subgroup.map_le_iff_le_comap.mp
        ((hA.map_equivariant (Atlas.G2.Natural.action (ZMod 2)) ρ f.symm
          M.linearEquiv.symm hinv).le_offenderSubgroup ρ)
    apply top_unique
    intro g _
    have hg := hle (mem_top (f g))
    change f.symm (f g) ∈ offenderSubgroup ρ at hg
    simpa only [f.symm_apply_apply] using hg
  let j : offenderSubgroup ρ ≃* G := (MulEquiv.subgroupCongr hJ).trans Subgroup.topEquiv
  have hLJ : L ≤ offenderSubgroup ρ := by rw [hJ]; exact le_top
  let m : MarkedActionEquiv ρ (offenderSubgroup ρ) L (g2Natural (ZMod 2))
      (commutator (Atlas.G2.Model (ZMod 2))) := {
    action := {
      groupEquiv := j.trans f
      linearEquiv := M.linearEquiv
      intertwines := fun g v => haction g v }
    contained := hLJ
    subgroupEquiv := M.groupEquiv
    compatible := fun l => hmark l }
  refine .g2Two m ?_ ?_
  · intro A hA
    have ho := (hA.isOffender ρ).map_equivariant ρ (Atlas.G2.Natural.action (ZMod 2))
      f.toMonoidHom f.injective M.linearEquiv haction
    have hr := Atlas.G2.NaturalOffenders.natural_offender_rank (n := 1)
      (by norm_num) (by decide) _ ho
    rwa [rank_map_injective _ f.injective] at hr
  · apply quadraticRatio_eq_one_of_no_strong ρ hff
    intro A hA
    have ho := (show IsOffender ρ A from ⟨hA.1,hA.2.le⟩).map_equivariant
      ρ (Atlas.G2.Natural.action (ZMod 2)) f.toMonoidHom f.injective M.linearEquiv haction
    have hr := Atlas.G2.NaturalOffenders.natural_offender_rank (n := 1)
      (by norm_num) (by decide) _ ho
    have hd := Atlas.G2.NaturalOffenders.natural_offender_fixedCodim (n := 1)
      (by norm_num) (by decide) _ ho
    rw [rank_map_injective _ f.injective] at hr
    rw [← fixedCodim_map_equivariant ρ _ _ M.linearEquiv haction] at hd
    have hs := hA.2
    omega
theorem g2_binary_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) :=
  g2_binary_case (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA)
    ⟨A,hA.isOffender ρ⟩ e
end CFSG.Quasithin.ChapterB.SourceClassification

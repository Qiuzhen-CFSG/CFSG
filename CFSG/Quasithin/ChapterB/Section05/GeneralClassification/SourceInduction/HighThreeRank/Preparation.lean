module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.Contracts
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.NilpotentCover

/-!
# The actual nilpotent SQTK presentation for B.5.7

Apply the proved B.5.2(1–2) construction to the quotient in B.5.3. The
nilpotent preimage of the Fitting subgroup makes each prime-core preimage
have a normal Sylow subgroup mapping onto that core. Consequently the prime
cores of the cover map onto those of the original actor. This identifies
B.5.7's image X with the original three-core, using the actual quotient map.

These lemmas are below the final branch assembly so that the cover reduction
and the module calculation can both import them.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.2 and B.5.7,
printed pp.103–106.
-/

@[expose] public section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank
universe u v
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V)

/-- B.5.3 supplies an actual prepared SQTK cover, without any component assumption. -/
theorem exists_preparedCover (hyp : FFHypothesis K ρ) : Nonempty (PreparedCover K G) := by
  obtain ⟨q⟩ := hyp.quotient
  let f := q.equiv.toMonoidHom.comp (QuotientGroup.mk' q.kernel)
  have hf : Function.Surjective f :=
    q.equiv.surjective.comp (QuotientGroup.mk'_surjective q.kernel)
  obtain ⟨H, hH, hfin, α, hsqtk, hα, hfit, hker, hodd, _, _⟩ :=
    NilpotentCover.exists_sqtk_cover q.sqtk f hf
  exact ⟨{
    Cover := H
    coverGroup := hH
    coverFinite := hfin
    projection := α
    surjective := hα
    sqtk := hsqtk
    fitting_nilpotent := hfit
    kernel_nilpotent := hker
    kernel_odd := hodd }⟩

/-- The presentation identifies its literal kernel quotient with the actor. -/
noncomputable def PreparedCover.quotientEquiv (c : PreparedCover K G) :
    (c.Cover ⧸ c.projection.ker) ≃* G :=
  QuotientGroup.quotientKerEquivOfSurjective c.projection c.surjective

omit [Finite G] in
theorem PreparedCover.quotientEquiv_apply (c : PreparedCover K G) (x : c.Cover) :
    c.quotientEquiv (QuotientGroup.mk' c.projection.ker x) = c.projection x := rfl

/-- Every prime core is the image of the corresponding core of the prepared cover.
The normal Sylow subgroup in its nilpotent preimage supplies the reverse inclusion. -/
theorem PreparedCover.map_pCore (c : PreparedCover K G) (p : ℕ) [Fact p.Prime] :
    (pCore p c.Cover).map c.projection = pCore p G := by
  let : Group.IsNilpotent ((fittingSubgroup G).comap c.projection) := c.fitting_nilpotent
  let P : Sylow p ((pCore p G).comap c.projection) := Classical.choice inferInstance
  obtain ⟨hn, hm⟩ := NilpotentCover.sylow_pCore_preimage
    c.projection c.surjective p P
  apply le_antisymm
  · exact le_sSup ⟨Subgroup.Normal.map inferInstance c.projection c.surjective,
      pCore_isPGroup.map c.projection⟩
  · rw [← hm]
    exact map_mono (show P.map ((pCore p G).comap c.projection).subtype ≤ pCore p c.Cover from
      le_sSup ⟨hn, P.isPGroup'.map _⟩)

/-- The source's `X := X̂α` is exactly `O₃(G)`, not an unspecified cyclic subgroup. -/
theorem NoncentralContext.threeCore_image {L : Subgroup G} (d : NoncentralContext K G L) :
    (pCore 3 d.cover.Cover).map d.cover.projection = pCore 3 G :=
  d.cover.map_pCore 3

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank

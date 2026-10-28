module
public import ABG.ChapterII.Section1.FusionPatterns
public import Theory.GroupTheory.WeakClosureQuotient

/-!
# Weak closure of images of central Sylow subgroups

Let S be a Sylow two-subgroup of a finite group G, and suppose that every
subgroup of its center is weakly closed in S. Under a surjective homomorphism
q : G → H, every subgroup of q(Z(S)) is weakly closed in q(S).
No condition on the kernel is needed; the conclusion concerns the image of
the original center.

For a subgroup Z of q(Z(S)), its inverse image intersected with Z(S) maps
onto Z and is weakly closed by hypothesis. The general Sylow quotient theorem
`weakly_closed_map_of_surjective` then gives weak closure of Z. The final
calculation translates that theorem's left conjugation convention into the
right conjugation used by `BenderSuzuki.External.WeaklyClosedIn`.

This is the quotient weak-closure reduction in ABG Chapter II §3 Proposition 1,
`refs/latex/alperin-brauer-gorenstein-pages/page-022.tex` and `page-023.tex`.
-/

namespace ABG
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- Subgroups of the image of the Sylow center remain weakly closed under
a surjective homomorphism. -/
public theorem HasWeaklyClosedCenterSubgroups.weaklyClosedIn_of_le_map
    {S : Sylow 2 G} (hS : HasWeaklyClosedCenterSubgroups (S : Subgroup G))
    (q : G →* H) (hq : Function.Surjective q)
    (Z : Subgroup H) (hZ : Z ≤ (subgroupCenter (S : Subgroup G)).map q) :
    BenderSuzuki.External.WeaklyClosedIn ((S : Subgroup G).map q) Z := by
  let J : Subgroup G := Z.comap q ⊓ subgroupCenter (S : Subgroup G)
  have hJ : BenderSuzuki.External.WeaklyClosedIn (S : Subgroup G) J := hS J inf_le_right
  have hmap : J.map q = Z := by
    apply le_antisymm
    · rintro z ⟨j, hj, rfl⟩
      exact hj.1
    · intro z hz
      obtain ⟨j, hj, hjz⟩ := hZ hz
      exact ⟨j, ⟨by simpa [Subgroup.mem_comap, hjz] using hz, hj⟩, hjz⟩
  rw [← hmap]
  refine ⟨Subgroup.map_mono hJ.1, ?_⟩
  intro b hb
  change (J.map q).map (MulAut.conj b⁻¹).toMonoidHom ≤ (S : Subgroup G).map q at hb
  change (J.map q).map (MulAut.conj b⁻¹).toMonoidHom = J.map q
  apply weakly_closed_map_of_surjective S J hJ.1 ?_ q hq b⁻¹ hb
  intro g hg
  simpa [BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy] using
    (hJ.2 g⁻¹ (by
      simpa [BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy] using hg))
end ABG

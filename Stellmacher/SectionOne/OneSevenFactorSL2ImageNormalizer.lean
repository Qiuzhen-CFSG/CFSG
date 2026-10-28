module
public import Stellmacher.SectionOne.OneSevenFactorPair
public import Stellmacher.SectionOne.OneSevenFactorConjugation
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SL2Products

/-!
# A full SL₂(2) image forces canonical-factor normalization

Let D be a canonical factor from (1.7), F an ambient subgroup, and f a
homomorphism from F to an SL₂(2) group. If the image of D intersect F is
the full target, then F normalizes D. The consumer typically has D≤F,
but that additional containment is unnecessary for the conclusion.

Every F-conjugate of D has full image as well. Distinct canonical factors
commute elementwise by the pairwise factor theorem. Full images of two
commuting factors would make the target abelian, whereas SL₂(2) has trivial
center and order six. Consequently each F-conjugate equals D.

This is the group-side recognition step for the central quotient action
in Stellmacher (9.4), printed pp.51–52 of
`refs/files/stellmacher-n-group.pdf`; it uses the actual quotient map
rather than assuming the selected factor is already normal.
-/

namespace Stellmacher.SectionOne
universe u

public theorem oneSevenFactor_normalized_of_full_sl2_image
    {G V L : Type u} [Group G] [Group V] [Group L]
    [Finite G] [Finite V] [Finite L]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hyp : Hypotheses G V) (D F : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D)
    (f : F →* L) (hL : IsSL2Two L)
    (hfull : (D.subgroupOf F).map f = ⊤) :
    F ≤ Subgroup.normalizer D := by
  intro g hg
  rcases oneSevenFactor_eq_or_commute hyp D (D.conjBy g) hD (hD.conjBy D g) with heq | hcomm
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm
  · have hsurj (l : L) : ∃ d : F, (d : G) ∈ D ∧ f d = l := by
      have hl : l ∈ (D.subgroupOf F).map f := hfull.symm ▸ Subgroup.mem_top l
      exact Subgroup.mem_map.mp hl
    let gF : F := ⟨g,hg⟩
    have hall (l m : L) : l*m=m*l := by
      obtain ⟨d,hd,hfd⟩ := hsurj l
      obtain ⟨e,he,hfe⟩ := hsurj ((f gF)⁻¹*m*f gF)
      have heconj : g * (e : G) * g⁻¹ ∈ D.conjBy g :=
        Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom he
      have hc : d * (gF*e*gF⁻¹) = (gF*e*gF⁻¹)*d :=
        Subtype.ext (hcomm d hd _ heconj)
      have hfc := congrArg f hc
      have himage : f (gF*e*gF⁻¹) = m := by
        simp only [map_mul,map_inv,hfe]
        group
      simpa only [map_mul,hfd,himage] using hfc
    have hone (l : L) : l=1 := by
      have hc : l ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr (fun m => hall m l)
      rwa [RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two hL] at hc
    let _ : Subsingleton L := ⟨fun l m => (hone l).trans (hone m).symm⟩
    have hc : Nat.card L = 1 := Nat.card_of_subsingleton (1 : L)
    rw [RankOneThreeGroupAssembly.isSL2Two_card hL] at hc
    omega

end Stellmacher.SectionOne

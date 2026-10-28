module

public import CFSG.Quasithin.MainConverse.ReeSections.MaximalCover.Structure

/-!
# Transport of the structural Ree alternatives

Malle's list is a list up to conjugacy. An isomorphism transports each normal
layer by inverse image and identifies its quotient with the original quotient,
so that all four index-two clauses survive. The parabolic and subfield clauses
retain their actual group equivalences.

This module proves transport only, not exhaustion of the list.
Source: Malle, J. Algebra 139 (1991), 52–69, as reproduced in the proof of
Theorem 5 of Himstedt–Nguyen–Tiep, arXiv:0910.4758, pp.2–3.
-/

public section

namespace CFSG.Quasithin.MainConverse.ReeSections

private noncomputable def comapLayerEquiv {H K : Type} [Group H] [Group K]
    (e : H ≃* K) (N : Subgroup K) : N.comap e.toMonoidHom ≃* N :=
  (e.subgroupMap (N.comap e.toMonoidHom)).trans
    (MulEquiv.subgroupCongr
      (Subgroup.map_comap_eq_self_of_surjective e.surjective N))

private theorem card_quotient_comap {H K : Type} [Group H] [Group K]
    (e : H ≃* K) (N : Subgroup K) [N.Normal] :
    Nat.card (H ⧸ N.comap e.toMonoidHom) = Nat.card (K ⧸ N) :=
  Nat.card_congr (QuotientGroup.congr (N.comap e.toMonoidHom) N e
    (Subgroup.map_comap_eq_self_of_surjective e.surjective N)).toEquiv

/-- Transport all the structures, including their relative normality and
index-two quotient, along an actual multiplicative equivalence. -/
theorem MaximalAlternative.of_mulEquiv {m : ℕ} {H K : Type} [Group H] [Group K]
    (h : MaximalAlternative m K) (e : H ≃* K) : MaximalAlternative m H := by
  cases h with
  | parabolic s f => exact .parabolic s (e.trans f)
  | torusNormalizer hK =>
      let := hK
      exact .torusNormalizer
        (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  | specialUnitary F J hcard hconj N f hindex =>
      exact .specialUnitary F J hcard hconj (N.comap e.toMonoidHom)
        ((comapLayerEquiv e N).trans f) ((card_quotient_comap e N).trans hindex)
  | projectiveUnitary F J hcard hconj N f hindex =>
      exact .projectiveUnitary F J hcard hconj (N.comap e.toMonoidHom)
        ((comapLayerEquiv e N).trans f) ((card_quotient_comap e N).trans hindex)
  | suzukiWreath N f hindex =>
      exact .suzukiWreath (N.comap e.toMonoidHom)
        ((comapLayerEquiv e N).trans f) ((card_quotient_comap e N).trans hindex)
  | symplectic F hcard N f hindex =>
      exact .symplectic F hcard (N.comap e.toMonoidHom)
        ((comapLayerEquiv e N).trans f) ((card_quotient_comap e N).trans hindex)
  | subfield k hlt hdiv hprime f =>
      exact .subfield k hlt hdiv hprime (e.trans f)

/-- A source alternative for a conjugate subgroup gives the alternative for
the original subgroup. Conjugation means the forward map `x ↦ g*x*g⁻¹`. -/
theorem MaximalAlternative.of_conjugate {m : ℕ} {G : Type} [Group G]
    (M : Subgroup G) (g : G)
    (h : MaximalAlternative m (M.map (MulAut.conj g).toMonoidHom)) :
    MaximalAlternative m M :=
  h.of_mulEquiv ((MulAut.conj g).subgroupMap M)

/-- Maximality upgrades containment of a conjugate in a proper full parabolic
to an equivalence with that whole parabolic. -/
theorem MaximalAlternative.parabolic_of_conjugate_le {m : ℕ}
    (M : Subgroup (ReeF4.Model m)) (hM : IsCoatom M)
    (g : ReeF4.Model m) (s : ReeF4.LargeLocalSeeds.Side)
    (hP : ReeF4.ConverseParabolics.parabolic m s ≠ ⊤)
    (hle : M.map (MulAut.conj g).toMonoidHom ≤
      ReeF4.ConverseParabolics.parabolic m s) : MaximalAlternative m M := by
  have hMc : IsCoatom (M.map (MulAut.conj g).toMonoidHom) :=
    (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup M).mpr hM
  have heq := ((hMc.le_iff_eq hP).mp hle).symm
  exact .parabolic s
    (((MulAut.conj g).subgroupMap M).trans (MulEquiv.subgroupCongr heq))

/-- A normalizer cover for the ambient image of a subgroup normal in `M`
places the whole maximal subgroup in a full parabolic. Ambient normality of
the image is not assumed. -/
theorem MaximalAlternative.parabolic_of_conjugate_normalizer_le {m : ℕ}
    (M : Subgroup (ReeF4.Model m)) (hM : IsCoatom M)
    (A : Subgroup M) [A.Normal]
    (g : ReeF4.Model m) (s : ReeF4.LargeLocalSeeds.Side)
    (hP : ReeF4.ConverseParabolics.parabolic m s ≠ ⊤)
    (hcover : (Subgroup.normalizer (A.map M.subtype : Set (ReeF4.Model m))).map
      (MulAut.conj g).toMonoidHom ≤ ReeF4.ConverseParabolics.parabolic m s) :
    MaximalAlternative m M := by
  have hMN : M ≤ Subgroup.normalizer (A.map M.subtype : Set (ReeF4.Model m)) := by
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] using A.le_normalizer_map M.subtype
  exact .parabolic_of_conjugate_le M hM g s hP
    ((Subgroup.map_mono hMN).trans hcover)

end CFSG.Quasithin.MainConverse.ReeSections

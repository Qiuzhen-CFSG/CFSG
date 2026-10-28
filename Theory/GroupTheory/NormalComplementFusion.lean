module

public import Mathlib.GroupTheory.Sylow

/-!
# Fusion in the presence of a normal prime complement

If a finite group has a normal subgroup of order prime to `p` with
`p`-group quotient, conjugate elements of a Sylow `p`-subgroup are
already conjugate within that subgroup. The quotient map restricts to
an isomorphism on the Sylow subgroup: coprimality gives injectivity and
Sylow maximality gives surjectivity. Lift a quotient conjugator through
this restriction.

This is the normal-complement fusion argument used in Lyons,
*A Characterization of the Group U₃(4)* (1972), Lemma 1, p. 373.
-/

namespace Sylow

/-- A normal prime complement prevents additional element fusion in a Sylow subgroup. -/
public theorem isConj_of_isConj_of_normal_pComplement
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N : Subgroup G) [N.Normal]
    (hcop : Nat.Coprime p (Nat.card N)) (hquot : IsPGroup p (G ⧸ N))
    {x y : S} (hxy : IsConj (x : G) (y : G)) : IsConj x y := by
  let q := QuotientGroup.mk' N
  let f : S →* G ⧸ N := q.comp (S : Subgroup G).subtype
  have hfinj : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro s hs
    change s = 1
    have hsN : (s : G) ∈ N := (QuotientGroup.eq_one_iff (N := N) _).mp hs
    have hd : orderOf s ∣ Nat.card N := by
      simpa only [Subgroup.orderOf_coe] using N.orderOf_dvd_natCard hsN
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (S.isPGroup'.orderOf_coprime hcop s) dvd_rfl hd)
  have hfsurj : Function.Surjective f := by
    let T := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
    have htop : (T : Subgroup (G ⧸ N)) = ⊤ :=
      (T.is_maximal' (hquot.to_subgroup ⊤) le_top).symm
    intro a
    have ha : a ∈ (S : Subgroup G).map q := by
      rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective N) S, htop]
      trivial
    obtain ⟨s, hs, he⟩ := ha
    exact ⟨⟨s, hs⟩, he⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  obtain ⟨s, hs⟩ := hfsurj (q g)
  apply isConj_iff.mpr
  refine ⟨s, hfinj ?_⟩
  change f (s * x * s⁻¹) = f y
  rw [map_mul, map_mul, map_inv, hs]
  exact congrArg q hg

end Sylow

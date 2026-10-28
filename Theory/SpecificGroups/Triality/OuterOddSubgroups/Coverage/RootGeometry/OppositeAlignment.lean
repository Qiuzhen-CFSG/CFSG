module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.OppositeAlignment.WeylIntersection


/-!
# Aligning the opposite triality unipotent subgroup

The concrete Bruhat decomposition expresses every conjugate of U as a Borel
conjugate of a published Weyl conjugate. Disjointness from U forces the Weyl
word to be the literal opposition `.r 3`. Factoring the remaining Borel element
as u t, and using that the torus normalizes the opposite subgroup, gives the
correcting element u⁻¹ in U.

For an automorphism a preserving U, its image of the opposite subgroup is
conjugation of U by a(n₀), where n₀ is the published opposition representative.
The orbit theorem therefore supplies precisely the second normalization
`MulAut.conj u * a`. No root-recognition, simplicity or perfectness premise is
required, and every positive binary exponent is included, in particular f = 1.
The existing first normalization and the root-frame assembly are unchanged.

Source: Steinberg, Theorem 30(1) and the proof of Theorem 36,
`refs/KGroup/GLS3/Chapter2St1.tex`; GLS3 2.3.4(c), 2.3.5 and 2.3.8,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section

namespace Triality.Standard.OuterOdd.Coverage.RootGeometry.OppositeAlignment
open Parabolics ConcreteBruhat
open scoped Pointwise
noncomputable section

private theorem map_conj_mul {G : Type*} [Group G] (H : Subgroup G) (g h : G) :
    H.map (MulAut.conj (g * h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  change (MulAut.conj (g * h)) • H = MulAut.conj g • (MulAut.conj h • H)
  rw [map_mul, mul_smul]

private theorem map_conj_one {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  change (MulAut.conj (1 : G)) • H = H
  rw [map_one, one_smul]

private theorem map_unipotent_conj_borel (P : Parameters) (hp : P.prime = 2)
    {b : Carrier P} (hb : b ∈ borel P) :
    (unipotent P).map (MulAut.conj b).toMonoidHom = unipotent P :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (borel_le_normalizer_unipotent P hp hb)

private theorem map_conj_eq_of_mem_cell (f : ℕ) (hf : 0 < f)
    (g : Carrier (binaryParameters f hf)) :
    ∃ w : DihedralGroup 6, ∃ b ∈ borel (binaryParameters f hf),
      (unipotent (binaryParameters f hf)).map (MulAut.conj g).toMonoidHom =
        ((unipotent (binaryParameters f hf)).map
          (MulAut.conj (weylRepresentative (binaryParameters f hf)
            (binaryParameters_prime f hf) w)).toMonoidHom).map (MulAut.conj b).toMonoidHom := by
  obtain ⟨w, hw⟩ := FixedDescent.exists_mem_cell f hf g
  obtain ⟨b, hb, c, hc, hg⟩ := (mem_cell_iff _ (binaryParameters_prime f hf) w g).mp hw
  refine ⟨w, b, hb, ?_⟩
  rw [hg, map_conj_mul, map_conj_mul, map_unipotent_conj_borel _ (binaryParameters_prime f hf) hc]

private theorem torus_le_normalizer_opposite (P : Parameters) (hp : P.prime = 2) :
    torus P ≤ Subgroup.normalizer (oppositeUnipotent P hp) := by
  rw [normalizer_oppositeUnipotent]
  intro t ht
  let n := weylRepresentative P hp (.r 3)
  have hn : n⁻¹ ∈ Subgroup.normalizer (torus P) :=
    (Subgroup.normalizer (torus P : Set (Carrier P))).inv_mem
      (RelativeNormalizer.weylRepresentative_normalizes_torus P hp (.r 3))
  have hnt : n⁻¹ * t * n ∈ torus P := by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hn t).mp ht
  refine ⟨n⁻¹ * t * n, torus_le_borel P hnt, ?_⟩
  change n * (n⁻¹ * t * n) * n⁻¹ = t
  group

private theorem exists_unipotent_conj_of_borel (P : Parameters) (hp : P.prime = 2)
    {b : Carrier P} (hb : b ∈ borel P) :
    ∃ u ∈ unipotent P,
      ((oppositeUnipotent P hp).map (MulAut.conj b).toMonoidHom).map
        (MulAut.conj u).toMonoidHom = oppositeUnipotent P hp := by
  have hb' : b ∈ (unipotent P : Set (Carrier P)) * torus P := by
    rw [← borel_eq_mul P hp]
    exact hb
  obtain ⟨u, hu, t, ht, he⟩ := hb'
  refine ⟨u⁻¹, (unipotent P).inv_mem hu, ?_⟩
  have ht' : (oppositeUnipotent P hp).map (MulAut.conj t).toMonoidHom =
      oppositeUnipotent P hp := Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (torus_le_normalizer_opposite P hp ht)
  rw [← he, map_conj_mul, ht', ← map_conj_mul, inv_mul_cancel, map_conj_one]

/-- Every conjugate of U disjoint from U can be moved to its literal opposite
by an element of U. -/
theorem exists_unipotent_conj_opposite_of_disjoint (f : ℕ) (hf : 0 < f)
    (g : Carrier (binaryParameters f hf))
    (hd : Disjoint (unipotent (binaryParameters f hf))
      ((unipotent (binaryParameters f hf)).map (MulAut.conj g).toMonoidHom)) :
    ∃ u ∈ unipotent (binaryParameters f hf),
      ((unipotent (binaryParameters f hf)).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj u).toMonoidHom =
          oppositeUnipotent (binaryParameters f hf) (binaryParameters_prime f hf) := by
  let P := binaryParameters f hf
  obtain ⟨w, b, hb, he⟩ := map_conj_eq_of_mem_cell f hf g
  have hd' := Subgroup.disjoint_map (f := (MulAut.conj b⁻¹).toMonoidHom)
    (MulAut.conj b⁻¹).injective hd
  rw [map_unipotent_conj_borel P (binaryParameters_prime f hf) ((borel P).inv_mem hb),
    he, ← map_conj_mul, inv_mul_cancel, map_conj_one] at hd'
  have hw := weyl_eq_opposition_of_disjoint f hf w hd'
  subst w
  obtain ⟨u, hu, hu'⟩ := exists_unipotent_conj_of_borel P (binaryParameters_prime f hf) hb
  exact ⟨u, hu, by rw [he]; exact hu'⟩

private theorem map_conj_equiv {G : Type*} [Group G]
    (H : Subgroup G) (g : G) (a : MulAut G) :
    (H.map (MulAut.conj g).toMonoidHom).map a.toMonoidHom =
      (H.map a.toMonoidHom).map (MulAut.conj (a g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

end
end Triality.Standard.OuterOdd.Coverage.RootGeometry.OppositeAlignment

namespace Triality.Standard.OuterOdd.Coverage.RootGeometry
open Parabolics ConcreteBruhat OppositeAlignment

/-- The exact second normalization of Steinberg's argument, including q = 2. -/
theorem exists_unipotent_opposite_invariant (f : ℕ) (hf : 0 < f)
    (a : MulAut (Carrier (binaryParameters f hf)))
    (ha : (unipotent (binaryParameters f hf)).map a.toMonoidHom =
      unipotent (binaryParameters f hf)) :
    ∃ u ∈ unipotent (binaryParameters f hf),
      (oppositeUnipotent (binaryParameters f hf) rfl).map
        (MulAut.conj u * a).toMonoidHom = oppositeUnipotent (binaryParameters f hf) rfl := by
  let P := binaryParameters f hf
  let n := weylRepresentative P (binaryParameters_prime f hf) (.r 3)
  have he : (oppositeUnipotent P (binaryParameters_prime f hf)).map a.toMonoidHom =
      (unipotent P).map (MulAut.conj (a n)).toMonoidHom := by
    rw [oppositeUnipotent, map_conj_equiv, ha]
  have hd := Subgroup.disjoint_map (f := a.toMonoidHom) a.injective
    (disjoint_unipotent_opposite f hf)
  rw [ha, he] at hd
  obtain ⟨u, hu, hu'⟩ := exists_unipotent_conj_opposite_of_disjoint f hf (a n) hd
  refine ⟨u, hu, ?_⟩
  change (oppositeUnipotent P (binaryParameters_prime f hf)).map
    ((MulAut.conj u).toMonoidHom.comp a.toMonoidHom) = _
  rw [← Subgroup.map_map, he]
  exact hu'

end Triality.Standard.OuterOdd.Coverage.RootGeometry

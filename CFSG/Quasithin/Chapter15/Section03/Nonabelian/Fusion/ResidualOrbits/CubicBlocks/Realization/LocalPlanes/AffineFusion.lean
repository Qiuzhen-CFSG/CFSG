module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.Centralizers
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.Orthogonality
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.AffineFusion.Tensor
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.AffineFusion.CentralOrbits
/-!
# Affine cubic fusion in the literal local planes

The binary tensor calculation supplies a cubic translate with polar value
zero, and outside the singular cubic line also one with value one. The
actual D-image lifts these rotations, and lower compatibility preserves
their ambient conjugations. Writing the centralizer generator as u v with
u in Ua ≤ U gives the affine membership criterion when it is outside U.
Since the generator centralizes D, this proves fusion for both cosets of V.

The commutator-line equality remains an explicit geometric premise. It
places the literal commutator subgroup in the central subgroup V, so the
central commutator homomorphism proves transitivity on its right coset and
the equality between the source product and the subgroup join.

This is a conditional helper for Aschbacher–Smith, proof of 15.3.61(2),
printed pp.1150–1151, using the hyperplane of 15.3.53(2), p.1146. The source
assembly must supply the intersection, normalization and commutator-line
identity; this module does not assert the complete numbered source lemma.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.AffineFusion
variable {G : Type*} [Group G] {I Y P V : Subgroup G}
  {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
  [(V.subgroupOf P).Normal]

/-- The affine coset outside U is cut out by polar value one. Its origin
is obtained from the literal product Ua V. -/
theorem affine_mem_iff (d : LayerActions I Y P V hIP hIV)
    (hcentral : V ≤ centralizer (P : Set G))
    (U Ua : Subgroup G) (hUaU : Ua ≤ U) (hLP : Ua ⊔ V ≤ P)
    (z : V) (hUV : U ⊓ V = sourceHyperplane d z)
    (a : G) (ha : a ∈ Ua ⊔ V) (haU : a ∉ U) (v : V) :
    a * (v : G) ∈ U ↔ determinantPolar (d.lowerCoordinates z) (d.lowerCoordinates v) = 1 := by
  have hUaP : Ua ≤ P := le_sup_left.trans hLP
  have hp : ((Ua ⊔ V : Subgroup G) : Set G) = (Ua : Set G) * (V : Set G) :=
    coe_mul_of_right_le_normalizer_left Ua V
      ((hcentral.trans (centralizer_le hUaP)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hm : a ∈ (Ua : Set G) * (V : Set G) := by rw [← hp]; exact ha
  obtain ⟨u, hu, w, hw, he⟩ := hm
  let wV : V := ⟨w, hw⟩
  have hwU : w ∉ U := fun hwU => haU (he ▸ U.mul_mem (hUaU hu) hwU)
  have hw0 : determinantPolar (d.lowerCoordinates z) (d.lowerCoordinates wV) ≠ 0 := by
    intro h
    exact hwU ((mem_lower_source_iff d U z hUV wV).mpr h)
  have hw1 : determinantPolar (d.lowerCoordinates z) (d.lowerCoordinates wV) = 1 := by
    have hb : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
    exact hb _ hw0
  rw [← he, mul_assoc, U.mul_mem_cancel_left (hUaU hu)]
  change ((wV * v : V) : G) ∈ U ↔ _
  rw [mem_lower_source_iff d U z hUV, map_mul, determinantPolar_mul, hw1]
  have hb : ∀ t : ZMod 2, 1 + t = 0 ↔ t = 1 := by decide
  exact hb _

omit [(V.subgroupOf P).Normal] in
private theorem plane_decomposition [Finite G]
    (hcentral : V ≤ centralizer (P : Set G))
    (A : Subgroup G) (hAP : A ≤ P) (a : G) (ha : a ∈ A) (ha2 : orderOf a = 2)
    (hA : A = zpowers a ⊔ V) (x : G) (hx : x ∈ A) :
    ∃ v : V, x = (v : G) ∨ x = a * (v : G) := by
  classical
  have hnorm : zpowers a ≤ normalizer (V : Set G) := by
    apply zpowers_le.mpr
    apply Subgroup.centralizer_le_normalizer
    intro v hv
    exact (hcentral hv a (hAP ha)).symm
  have hm : x ∈ (zpowers a : Set G) * (V : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hnorm, ← hA]
    exact hx
  obtain ⟨u, hu, v, hv, he⟩ := hm
  change u ∈ zpowers a at hu
  rw [mem_zpowers_iff_mem_range_orderOf, ha2] at hu
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
  have hnlt : n < 2 := Finset.mem_range.mp hn
  refine ⟨⟨v, hv⟩, ?_⟩
  interval_cases n
  · exact Or.inl (by simpa using he.symm)
  · exact Or.inr (by simpa using he.symm)

private theorem lift_cubic_power (d : LayerActions I Y P V hIP hIV)
    (j : Fin 2) (D : Subgroup G)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic j) (n : ℕ) :
    ∃ b : I, (b : G) ∈ D ∧ d.actor b = complementaryRotation j ^ n := by
  have hm : complementaryRotation j ^ n ∈ (D.subgroupOf I).map d.actor := by
    rw [himage]
    exact pow_mem (mem_zpowers _) n
  obtain ⟨b, hb, he⟩ := hm
  exact ⟨b, hb, he⟩

/-- Every vector of V has a conjugate in the actual intersection U ∩ V. -/
theorem lower_fusion (d : LayerActions I Y P V hIP hIV)
    (j : Fin 2) (D : Subgroup G)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic j)
    (U : Subgroup G) (z : V) (hUV : U ⊓ V = sourceHyperplane d z) (v : V) :
    ∃ b ∈ D, MulAut.conj b (v : G) ∈ U := by
  obtain ⟨n, hn⟩ := exists_cubic_orthogonal j (d.lowerCoordinates z) (d.lowerCoordinates v)
  obtain ⟨b, hb, he⟩ := lift_cubic_power d j D himage n.val
  refine ⟨b, hb, ?_⟩
  have hm := (mem_lower_source_iff d U z hUV (lowerAction I V hIV b v)).mpr
    (by rw [d.lower_compatible, he]; exact hn)
  exact hm

/-- If the centralizer generator is in U, all of the plane is fused into U. -/
theorem plane_fusion_of_mem [Finite G] (d : LayerActions I Y P V hIP hIV)
    (hcentral : V ≤ centralizer (P : Set G))
    (j : Fin 2) (D : Subgroup G)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic j)
    (U : Subgroup G) (z : V) (hUV : U ⊓ V = sourceHyperplane d z)
    (A : Subgroup G) (hAP : A ≤ P) (a : G)
    (ha : a ∈ A ⊓ centralizer (D : Set G)) (ha2 : orderOf a = 2)
    (hA : A = zpowers a ⊔ V) (haU : a ∈ U) :
    ∀ x ∈ A, ∃ b ∈ D, MulAut.conj b x ∈ U := by
  intro x hx
  obtain ⟨v, rfl | rfl⟩ := plane_decomposition hcentral A hAP a ha.1 ha2 hA x hx
  · exact lower_fusion d j D himage U z hUV v
  · obtain ⟨b, hb, hv⟩ := lower_fusion d j D himage U z hUV v
    refine ⟨b, hb, ?_⟩
    have hf : MulAut.conj b a = a := by
      change b * a * b⁻¹ = a
      rw [ha.2 b hb, mul_inv_cancel_right]
    rw [map_mul, hf]
    exact U.mul_mem haU hv

/-- Off ⟨a⟩[a,P], the other affine coset also has a cubic conjugate in U.
The only geometric input beyond the actual hyperplane is the specified
commutator-line identity. -/
theorem plane_fusion_of_not_mem [Finite G] (d : LayerActions I Y P V hIP hIV)
    (hcentral : V ≤ centralizer (P : Set G))
    (j : Fin 2) (D : Subgroup G)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic j)
    (U Ua : Subgroup G) (hUaU : Ua ≤ U) (hLP : Ua ⊔ V ≤ P)
    (z : V) (hz : z ≠ 1) (hs : (d.lowerCoordinates z).toAdd.det = 0)
    (hUV : U ⊓ V = sourceHyperplane d z)
    (A : Subgroup G) (hAB : A ≤ Ua ⊔ V) (a : G)
    (ha : a ∈ A ⊓ centralizer (D : Set G)) (ha2 : orderOf a = 2)
    (hA : A = zpowers a ⊔ V) (haU : a ∉ U)
    (hline : ⁅zpowers a, P⁆ =
      (tensorCubicLine j (d.lowerCoordinates z)).map (tensorEmbedding d)) :
    ∀ x ∈ A, x ∉ zpowers a ⊔ ⁅zpowers a, P⁆ → ∃ b ∈ D, MulAut.conj b x ∈ U := by
  intro x hx hxout
  obtain ⟨v, rfl | rfl⟩ :=
    plane_decomposition hcentral A (hAB.trans hLP) a ha.1 ha2 hA x hx
  · exact lower_fusion d j D himage U z hUV v
  · have hvline : d.lowerCoordinates v ∉ tensorCubicLine j (d.lowerCoordinates z) := by
      intro hv
      have hvC : (v : G) ∈ ⁅zpowers a, P⁆ := by
        rw [hline]
        exact mem_map.mpr ⟨d.lowerCoordinates v, hv, tensorEmbedding_coordinates d v⟩
      exact hxout (mul_mem (mem_sup_left (mem_zpowers a)) (mem_sup_right hvC))
    have hz' : d.lowerCoordinates z ≠ 1 := by
      intro he
      exact hz (d.lowerCoordinates.injective (he.trans (map_one d.lowerCoordinates).symm))
    obtain ⟨n, hn⟩ := exists_cubic_nonorthogonal j _ _ hz' hs hvline
    obtain ⟨b, hb, he⟩ := lift_cubic_power d j D himage n.val
    have hm := (affine_mem_iff d hcentral U Ua hUaU hLP z hUV a (hAB ha.1) haU
      (lowerAction I V hIV b v)).mpr (by rw [d.lower_compatible, he]; exact hn)
    have hf : MulAut.conj (b : G) a = a := by
      change (b : G) * a * (b : G)⁻¹ = a
      rw [ha.2 b hb, mul_inv_cancel_right]
    refine ⟨b, hb, ?_⟩
    rw [map_mul, hf]
    exact hm

/-- The conditional affine-fusion package used in the first paragraph of
15.3.61(2). The parent constructs the singular commutator-line identity.
All conjugations, subgroups, products and the orthogonal hyperplane here
are literal; no orbit or fusion assertion is assumed. -/
theorem local_plane_affine_fusion [Finite G] (d : LayerActions I Y P V hIP hIV)
    (_hVP : V ≤ P) (hcentral : V ≤ centralizer (P : Set G))
    (j : Fin 2) (D : Subgroup G) (_hDI : D ≤ I) (_hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic j)
    (z : V) (hz : z ≠ 1) (hs : (d.lowerCoordinates z).toAdd.det = 0)
    (U Ua : Subgroup G) (hUaU : Ua ≤ U) (_hVU : V ≤ normalizer (U : Set G))
    (hLP : Ua ⊔ V ≤ P) (hUV : U ⊓ V = sourceHyperplane d z)
    (A : Subgroup G) (hAB : A ≤ Ua ⊔ V) (_hVA : V ≤ A) (a : G)
    (ha : a ∈ A ⊓ centralizer (D : Set G)) (ha2 : orderOf a = 2)
    (_haV : a ∉ V) (hA : A = zpowers a ⊔ V)
    (hline : ⁅zpowers a, P⁆ =
      (tensorCubicLine j (d.lowerCoordinates z)).map (tensorEmbedding d)) :
    (a ∈ U → ∀ x ∈ A, ∃ b ∈ D, MulAut.conj b x ∈ U) ∧
    (a ∉ U → ∀ x ∈ A, x ∉ zpowers a ⊔ ⁅zpowers a, P⁆ →
      ∃ b ∈ D, MulAut.conj b x ∈ U) ∧
    (∀ c₁ ∈ ⁅zpowers a, P⁆, ∀ c₂ ∈ ⁅zpowers a, P⁆,
      ∃ p ∈ P, MulAut.conj p (a * c₁) = a * c₂) ∧
    ((zpowers a ⊔ ⁅zpowers a, P⁆ : Subgroup G) : Set G) =
      (zpowers a : Set G) * (⁅zpowers a, P⁆ : Subgroup G) := by
  have haP : a ∈ P := hLP (hAB ha.1)
  have hCV : ⁅zpowers a, P⁆ ≤ V := by
    rw [hline]
    rintro x ⟨v, _, rfl⟩
    exact (d.lowerCoordinates.symm v).property
  have hC := hCV.trans hcentral
  exact ⟨plane_fusion_of_mem d hcentral j D himage U z hUV A (hAB.trans hLP) a ha ha2 hA,
    (fun haU => plane_fusion_of_not_mem d hcentral j D himage U Ua hUaU hLP z hz hs hUV
      A hAB a ha ha2 hA haU hline),
    commutator_coset_transitive P a haP hC,
    cyclic_commutator_sup_eq_product P a haP hC⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.AffineFusion

module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.NaturalPreimage.Coordinates
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.KernelReduction

/-!
# The marked natural-module inverse image in 12.8.9(6)

On each natural summand, displacement by u sends the displaced W-line
back to the W-line with the same binary coordinate. We first apply this
to every element of Z(U), then use ker φ = E to obtain the full inverse
image. The original right conjugator g ∈ P − H is retained by factoring
through O₂(P) ≤ H; both X and Z(U)^g are preserved.

The genuine equivariant natural-module witness and the earlier parabolic
factorization remain explicit source inputs. They contain no clause of
12.8.9(4–6). Their construction belongs to the preceding-source assembly.

Source: Aschbacher–Smith, Lemma 12.8.9, printed p.853, PDF p.870.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

private def internalCenterMap (F : InvariantFlag T V n) (g h : G)
    (hZ : conjugate F.ZU h = conjugate F.ZU g) : F.ZU →* F.X g where
  toFun z := ⟨h⁻¹ * z * h, F.conjugate_ZU_le_X g (by
    rw [← hZ]
    exact ⟨z, z.property, by simp⟩)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

private theorem internalCenterMap_range (F : InvariantFlag T V n) (g h : G)
    (hZ : conjugate F.ZU h = conjugate F.ZU g) :
    (internalCenterMap F g h hZ).range = (conjugate F.ZU g).subgroupOf (F.X g) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change h⁻¹ * z * h ∈ conjugate F.ZU g
    rw [← hZ]
    exact ⟨z, z.property, by simp⟩
  · intro hx
    change (x : G) ∈ conjugate F.ZU g at hx
    rw [← hZ] at hx
    obtain ⟨z, hz, he⟩ := hx
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    simpa [internalCenterMap, MulAut.conj_apply] using he

/-- Displacement sends the actual conjugate of the center onto its actual
image in W/E. This equality is proved from coordinates, not assumed. -/
theorem parabolicCommutator_center_image (F : InvariantFlag T V n)
    (L : Subgroup G) (g : G) {ι : Type*} [Fintype ι]
    (M : F.ParabolicNaturalModule L g ι)
    (h : G) (hh : h ∈ F.I₂ L) (hZ : conjugate F.ZU h = conjugate F.ZU g)
    (u : F.U) (hu : (u : G) ∉ F.W)
    [((F.E g).subgroupOf F.W).Normal]
    (hcomm : ∀ x ∈ F.X g, ⁅x, (u : G)⁆ ∈ F.W)
    (habel : ⁅F.W ⊔ F.X g, F.W ⊔ F.X g⁆ ≤ F.E g) :
    ((conjugate F.ZU g).subgroupOf (F.X g)).map
        (F.parabolicCommutator g u hcomm habel) =
      (F.ZU.subgroupOf F.W).map (QuotientGroup.mk' ((F.E g).subgroupOf F.W)) := by
  let φ := F.parabolicCommutator g u hcomm habel
  let q := QuotientGroup.mk' ((F.E g).subgroupOf F.W)
  let cZ := internalCenterMap F g h hZ
  have hpoint : ∀ z : F.ZU, φ (cZ z) = q (inclusion F.ZU_le_W z) := by
    intro z
    let c : ↥(F.W ⊔ F.X g) := ⟨⁅(cZ z : G), (u : G)⁆,
      (le_sup_left : F.W ≤ F.W ⊔ F.X g) (hcomm _ (cZ z).property)⟩
    have he := M.displaced_center_coordinates h hh hZ u hu z c rfl
    have hmem := (M.coordinates_eq_iff _ _).mp he
    apply (MonoidHom.eq_iff q).mpr
    rw [QuotientGroup.ker_mk']
    exact hmem
  have he : φ.comp cZ = q.comp (inclusion F.ZU_le_W) := MonoidHom.ext hpoint
  rw [← internalCenterMap_range F g h hZ]
  change cZ.range.map φ = _
  rw [← MonoidHom.range_comp, he, MonoidHom.range_comp]
  congr 1
  ext z
  constructor
  · rintro ⟨z, rfl⟩
    exact z.property
  · intro hz
    exact ⟨⟨z, hz⟩, rfl⟩

/-- The moved-space identity [X/E,u] = W/E, on the literal quotient map.
Every W-coordinate is lifted through the genuine natural decomposition
onto the marked X-line before applying displacement. -/
theorem parabolicCommutator_natural_surjective (F : InvariantFlag T V n)
    (L : Subgroup G) (g : G) {ι : Type*} [Fintype ι]
    (M : F.ParabolicNaturalModule L g ι)
    (u : F.U) (hu : (u : G) ∉ F.W)
    [((F.E g).subgroupOf F.W).Normal]
    (hcomm : ∀ x ∈ F.X g, ⁅x, (u : G)⁆ ∈ F.W)
    (habel : ⁅F.W ⊔ F.X g, F.W ⊔ F.X g⁆ ≤ F.E g) :
    Function.Surjective (F.parabolicCommutator g u hcomm habel) := by
  intro a
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective ((F.E g).subgroupOf F.W) a
  let ws : ↥(F.W ⊔ F.X g) := ⟨w, (le_sup_left : F.W ≤ F.W ⊔ F.X g) w.property⟩
  let v : ι → BinaryPermutation.core (Fin 3) := fun j =>
    BinaryPermutation.coreRepresentation (Fin 3) (Equiv.swap 0 1)
      (Multiplicative.toAdd (M.coordinates ws) j)
  obtain ⟨xs, hxs⟩ := M.onto (Multiplicative.ofAdd v)
  have hv (j : ι) : (v j).val 1 = 0 := by
    have hw := (M.W_marking ws).mp w.property j
    simpa [v, BinaryPermutation.coreRepresentation_apply,
      BinaryPermutation.representation_apply] using hw
  have hxX : (xs : G) ∈ F.X g := (M.X_marking xs).mpr (by
    intro j
    rw [hxs]
    exact hv j)
  let x : F.X g := ⟨xs, hxX⟩
  let c : ↥(F.W ⊔ F.X g) := ⟨⁅(x : G), (u : G)⁆,
    (le_sup_left : F.W ≤ F.W ⊔ F.X g) (hcomm _ x.property)⟩
  have he : M.coordinates c = M.coordinates ws := by
    apply Multiplicative.toAdd.injective
    funext j
    rw [M.commutator_coordinates u hu xs c rfl j, hxs]
    exact ParabolicNaturalModule.natural_coordinate_calculation _ _
      ((M.W_marking ws).mp w.property j) (hv j)
  refine ⟨x, ?_⟩
  apply (MonoidHom.eq_iff (QuotientGroup.mk' ((F.E g).subgroupOf F.W))).mpr
  rw [QuotientGroup.ker_mk']
  exact (M.coordinates_eq_iff c ws).mp he

/-- The exact inverse-image calculation D = Z(U)^g E in the source proof.
The original g lies in P − H; only its internally chosen representative
lies in I₂. Normality of E is relative to the displayed groups. -/
theorem parabolicCommutator_natural_preimage (F : InvariantFlag T V n)
    (L : Subgroup G) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {ι : Type*} [Fintype ι] (M : F.ParabolicNaturalModule L g ι)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
    (hPH : (F.P L).pCoreIn 2 ≤ F.H)
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
    [((F.E g).subgroupOf (F.I₂ L)).Normal]
    [((F.E g).subgroupOf F.W).Normal]
    (u : F.U) (hu : (u : G) ∉ F.W)
    (hcomm : ∀ x ∈ F.X g, ⁅x, (u : G)⁆ ∈ F.W)
    (habel : ⁅F.W ⊔ F.X g, F.W ⊔ F.X g⁆ ≤ F.E g) :
    ((F.ZU.subgroupOf F.W).map (QuotientGroup.mk' ((F.E g).subgroupOf F.W))).comap
        (F.parabolicCommutator g u hcomm habel) =
      (conjugate F.ZU g ⊔ F.E g).subgroupOf (F.X g) := by
  obtain ⟨h, hh, _, _, _, hZ⟩ :=
    F.exists_internal_natural_representative L g hgP hgH hfactor hPH hcore
  have hfixed : ∀ x ∈ F.X g, ⁅x, (u : G)⁆ ∈ F.E g ↔ x ∈ F.W := by
    intro x hx
    exact M.commutator_mem_E_iff u hu
      ⟨x, (le_sup_right : F.X g ≤ F.W ⊔ F.X g) hx⟩
      ⟨⁅x, (u : G)⁆, (le_sup_left : F.W ≤ F.W ⊔ F.X g) (hcomm x hx)⟩ rfl
  rw [← F.parabolicCommutator_center_image L g M h hh hZ u hu hcomm habel,
    comap_map_eq, F.parabolicCommutator_ker g u hcomm habel hfixed,
    ← subgroupOf_sup (F.conjugate_ZU_le_X g) (show F.E g ≤ F.X g from inf_le_right)]

/-- Application to the literal U/Z(U) action: the natural-module calculation
discharges hpreimage in the published point-stabilizer reduction, proving (6)
conditional only on the displayed preceding-source parabolic inputs. -/
theorem hat_stabilizer_le_of_natural_module (F : InvariantFlag T V n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G)) (hn : 2 ≤ n)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {ι : Type*} [Fintype ι] (M : F.ParabolicNaturalModule L g ι)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
    (hPH : (F.P L).pCoreIn 2 ≤ F.H)
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
    [((F.E g).subgroupOf (F.I₂ L)).Normal]
    [((F.E g).subgroupOf F.W).Normal]
    (u : F.U) (hu : (u : G) ∉ F.W)
    (hcomm : ∀ x ∈ F.X g, ⁅x, (u : G)⁆ ∈ F.W)
    (x : F.X g)
    (hx : F.xHatAction g (F.P_le_G₂ hn L hL hgP) x
      (QuotientGroup.mk' (center F.U) u) = QuotientGroup.mk' (center F.U) u) :
    (x : G) ∈ conjugate F.ZU g ⊔ F.E g := by
  apply F.hat_stabilizer_le_of_commutator_preimage g (F.P_le_G₂ hn L hL hgP)
    u hcomm M.commutator_core_le ?_ x hx
  intro y hy
  have he := F.parabolicCommutator_natural_preimage L g hgP hgH M
    hfactor hPH hcore u hu hcomm M.commutator_core_le
  change y ∈ ((F.ZU.subgroupOf F.W).map
    (QuotientGroup.mk' ((F.E g).subgroupOf F.W))).comap
      (F.parabolicCommutator g u hcomm M.commutator_core_le) at hy
  rw [he] at hy
  exact hy

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag

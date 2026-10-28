module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.FlagCores
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.CentralizerGeometry

/-!
# The characteristic subgroup underlying the middle flag

For nonzero W ≤ U < V, the intersection of the two subspace radicals is
Hom(V/U,W), acting by translations. Its fixed space is U and its displacement
space is W. Transvections recover both spaces, so its normalizer is precisely
the stabilizer of the flag W ≤ U.

The ambient image of Z(T′) is defined intrinsically as T′ ∩ C(T′). It is
functorial under group isomorphisms and normalized by T. Consequently an
identification of Z(T′) with the rectangular translation group supplies an
invariant flag without any classification of automorphisms. The degree-five
Sylow identification itself is a separate calculation.

Source: Aschbacher–Smith 2.3.9(7), printed pp.525–526; the invariant parabolic
convention is explained in E.2.2 on printed p.216.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup
variable {G : Type*} [Group G]

/-- The ambient image of the center of the derived subgroup of T. -/
def derivedCenter (T : Subgroup G) : Subgroup G :=
  ⁅T, T⁆ ⊓ centralizer ((⁅T, T⁆ : Subgroup G) : Set G)

/-- This definition is the genuine center of the derived subgroup, embedded in G. -/
theorem derivedCenter_eq_map_center (T : Subgroup G) :
    derivedCenter T = (center ↥(⁅T, T⁆ : Subgroup G)).map (⁅T, T⁆ : Subgroup G).subtype := by
  let D : Subgroup G := ⁅T, T⁆
  change D ⊓ centralizer (D : Set G) = (center D).map D.subtype
  ext x
  constructor
  · rintro ⟨hx, hxc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    exact mem_center_iff.mpr (fun y => Subtype.ext (hxc y y.property))
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    intro z hz
    exact congrArg Subtype.val (mem_center_iff.mp hy ⟨z, hz⟩)

theorem derivedCenter_map {K : Type*} [Group K] (T : Subgroup G) (a : G ≃* K) :
    (derivedCenter T).map a.toMonoidHom = derivedCenter (T.map a.toMonoidHom) := by
  have hc (D : Subgroup G) : (centralizer (D : Set G)).map a.toMonoidHom =
      centralizer (D.map a.toMonoidHom : Set K) := by
    ext x
    rw [mem_map_equiv]
    constructor
    · intro h y hy
      obtain ⟨y, hy, rfl⟩ := hy
      change a y * x = x * a y
      simpa only [map_mul, a.apply_symm_apply] using congrArg a (h y hy)
    · intro h y hy
      apply a.injective
      simpa only [map_mul, a.apply_symm_apply] using h (a y) (mem_map_of_mem _ hy)
  unfold derivedCenter
  rw [map_inf _ _ a.toMonoidHom a.injective, hc, map_commutator]

theorem le_normalizer_derivedCenter (T : Subgroup G) :
    T ≤ normalizer (derivedCenter T : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq]
  change (derivedCenter T).map (MulAut.conj x).toMonoidHom = _
  rw [derivedCenter_map]
  apply congrArg derivedCenter
  exact mem_normalizer_iff_map_conj_eq.mp (T.le_normalizer hx)

variable {n : ℕ}
private theorem scalar_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha

private theorem transvection_mem_radical_inf {W U : Space n} (hWU : W ≤ U)
    {w : Vector n} (hw : w ∈ W) {f : Vector n →ₗ[ZMod 2] ZMod 2}
    (hf : U ≤ f.ker) :
    BinaryLinear.transvection w f (hf (hWU hw)) ∈
      BinaryLinear.radical W ⊓ BinaryLinear.radical U :=
  ⟨BinaryLinear.transvection_mem hw (hWU.trans hf),
    BinaryLinear.transvection_mem (hWU hw) hf⟩

/-- The common fixed space of the maps from V/U to W is U. -/
theorem mem_iff_fixed_radical_inf {W U : Space n} (hW : W ≠ ⊥) (hWU : W ≤ U)
    (v : Vector n) : v ∈ U ↔
    ∀ g ∈ BinaryLinear.radical W ⊓ BinaryLinear.radical U, g v = v := by
  constructor
  · exact fun hv g hg => hg.2.1 v hv
  · intro hv
    by_contra hnv
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    obtain ⟨f, hfv, hf⟩ := U.exists_le_ker_of_notMem hnv
    have he := hv _ (transvection_mem_radical_inf hWU hw hf)
    change v + f v • w = v at he
    rw [scalar_one hfv, one_smul] at he
    exact hw0 (add_eq_left.mp he)

/-- The normalizer of the rectangular translation group is the flag stabilizer. -/
theorem normalizer_radical_inf {W U : Space n} (hW : W ≠ ⊥) (hU : U ≠ ⊤)
    (hWU : W ≤ U) :
    normalizer (↑(BinaryLinear.radical W ⊓ BinaryLinear.radical U) : Set (BinaryLinear.GL (Vector n))) =
      BinaryLinear.parabolic W ⊓ BinaryLinear.parabolic U := by
  apply le_antisymm
  · let Q := BinaryLinear.radical W ⊓ BinaryLinear.radical U
    have stableW (g : BinaryLinear.GL (Vector n)) (hg : g ∈ normalizer (Q : Set (BinaryLinear.GL (Vector n))))
        (w : Vector n) (hw : w ∈ W) : g w ∈ W := by
      obtain ⟨v, _, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hU)
      obtain ⟨f, hfv, hf⟩ := U.exists_le_ker_of_notMem hv
      let t := BinaryLinear.transvection w f (hf (hWU hw))
      have ht : t ∈ Q := transvection_mem_radical_inf hWU hw hf
      have hc := (hg t).mp ht
      have hd := hc.1.2 (g v)
      change (g * t * g⁻¹) (g v) - g v ∈ W at hd
      simpa [t, BinaryLinear.transvection, map_add, map_smul, scalar_one hfv] using hd
    have stableU (g : BinaryLinear.GL (Vector n)) (hg : g ∈ normalizer (Q : Set (BinaryLinear.GL (Vector n))))
        (u : Vector n) (hu : u ∈ U) : g u ∈ U := by
      apply (mem_iff_fixed_radical_inf hW hWU (g u)).mpr
      intro t ht
      have hti : g⁻¹ * t * g ∈ Q := by
        simpa only [inv_inv, SetLike.mem_coe] using ((normalizer (Q : Set (BinaryLinear.GL (Vector n)))).inv_mem hg t).mp ht
      have hh := hti.2.1 u hu
      have hh' := congrArg g hh
      simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
        LinearEquiv.apply_symm_apply] using hh'
    intro g hg
    change g ∈ normalizer (Q : Set (BinaryLinear.GL (Vector n))) at hg
    have hgi : g⁻¹ ∈ normalizer (Q : Set (BinaryLinear.GL (Vector n))) :=
      (normalizer (Q : Set (BinaryLinear.GL (Vector n)))).inv_mem hg
    constructor
    · intro v
      constructor
      · intro hv
        simpa using stableW g⁻¹ hgi (g v) hv
      · exact stableW g hg v
    · intro v
      constructor
      · intro hv
        simpa using stableU g⁻¹ hgi (g v) hv
      · exact stableU g hg v
  · exact (inf_le_inf (BinaryLinear.parabolic_le_normalizer W)
      (BinaryLinear.parabolic_le_normalizer U)).trans inf_normalizer_le_normalizer_inf

variable {L : Subgroup G} [NeZero n]

theorem normalizer_subspaceRadical_inf (e : L ≃* PSL n) {W U : Space n}
    (hW : W ≠ ⊥) (hU : U ≠ ⊤) (hWU : W ≤ U) :
    normalizer (↑(subspaceRadical e W ⊓ subspaceRadical e U) : Set L) =
      subspaceStabilizer e W ⊓ subspaceStabilizer e U := by
  change normalizer (↑((BinaryLinear.radical W).comap (linearModel e).toMonoidHom ⊓
    (BinaryLinear.radical U).comap (linearModel e).toMonoidHom) : Set L) = _
  rw [← comap_inf, ← comap_normalizer_eq_of_surjective _ (linearModel e).surjective,
    normalizer_radical_inf hW hU hWU, comap_inf]
  rfl

/-- A subspace fixed pointwise by the transvection lies in its intrinsic hyperplane. -/
theorem TransvectionCoordinates.le_hyperplane_of_mem_radical {e : L ≃* PSL n} {t : L}
    (c : TransvectionCoordinates e t) {U : Space n} (ht : t ∈ subspaceRadical e U) :
    U ≤ c.hyperplane := by
  intro v hv
  have hf : linearModel e t v = v := ht.1 v hv
  rw [c.action] at hf
  exact (smul_eq_zero.mp (add_eq_left.mp hf)).resolve_right c.vector_ne_zero

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end

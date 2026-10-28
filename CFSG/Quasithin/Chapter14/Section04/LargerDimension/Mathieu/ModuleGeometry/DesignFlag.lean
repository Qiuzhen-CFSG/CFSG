module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.DesignFlag.Stabilizer
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Assembly

/-!
# Simultaneous design, Sylow, and module marking for 14.4.12

The literal hexad preimage equals the native six-space stabilizer. Hexad
conjugacy followed by Sylow conjugacy inside this stabilizer therefore marks
both the source parabolic and its original Sylow subgroup at once. The same
native matrix carries its fixed line to the marked vector 1327. The final
application takes the actual residual join constructed by the actor catalogue.

Source: Aschbacher--Smith 14.4.12, printed pp.1011--1012; H.12.1, pp.393--394.
-/

@[expose] public section
noncomputable section
open Subgroup Sporadic.Mathieu M22TripleCover
open Representation.BinaryOffender
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.DesignFlag
open ActorCatalogue.NativeParabolics

theorem hexadPreimage_conjugate (b : Finset (Fin 22)) (x : Group) :
    (hexadPreimage b).map (MulAut.conj x).toMonoidHom =
      hexadPreimage (designProjection x • b) := by
  rw [hexadPreimage, hexadPreimage,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mem_map.mpr ⟨designProjection z, hz, by simp [MulAut.conj_apply]⟩
  · rintro ⟨z, hz, hzy⟩
    refine mem_map.mpr ⟨(MulAut.conj (x⁻¹)) y, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    change designProjection ((MulAut.conj (x⁻¹)) y) ∈ MulAction.stabilizer _ b
    have hmap : designProjection ((MulAut.conj (x⁻¹)) y) =
        (MulAut.conj ((designProjection x)⁻¹)) (designProjection y) := by
      change designProjection (x⁻¹ * y * x) =
        (designProjection x)⁻¹ * designProjection y * designProjection x
      rw [map_mul, map_mul, map_inv]
    rw [hmap, ← hzy]
    change (designProjection x)⁻¹ *
      (designProjection x * z * (designProjection x)⁻¹) * designProjection x ∈ _
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    exact hz

theorem exists_hexad_marking (b : Finset (Fin 22)) (hb : b ∈ m22Blocks) :
    ∃ x : Group, (hexadPreimage b).map (MulAut.conj x).toMonoidHom = parabolic := by
  obtain ⟨a, ha⟩ := exists_smul_m22Hexad123_eq hb
  obtain ⟨c, hc⟩ := exists_smul_m22Hexad123_eq markedHexad_mem
  obtain ⟨x, hx⟩ := designProjection_surjective
    (M22ValueBound.Concrete.inclusion (c * a⁻¹))
  refine ⟨x, ?_⟩
  rw [hexadPreimage_conjugate, hx, ← ha, map_mul, map_inv, mul_smul]
  change hexadPreimage (c • (a⁻¹ • (a • m22Hexad123))) = parabolic
  rw [inv_smul_smul, hc, ← parabolic_eq_hexadPreimage]

/-- One actual native conjugator simultaneously marks the full hexad preimage,
its original Sylow subgroup, and the fixed line of its original action. -/
theorem exists_flag_marking (b : Finset (Fin 22)) (hb : b ∈ m22Blocks)
    (S : Sylow 2 Group) (hS : (S : Subgroup Group) ≤ hexadPreimage b) :
    ∃ g : Group,
      (hexadPreimage b).map (MulAut.conj g).toMonoidHom = parabolic ∧
      (S : Subgroup Group).map (MulAut.conj g).toMonoidHom = markedSylow ∧
      (fixedSpace representation S).map (actionEquiv g).toLinearMap =
        binaryLine markedVector := by
  obtain ⟨x, hx⟩ := exists_hexad_marking b hb
  have hP : ((x • S : Sylow 2 Group) : Subgroup Group) ≤ parabolic := by
    exact hx ▸ map_mono (f := (MulAut.conj x).toMonoidHom) hS
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq parabolic
    ((x • S).subtype hP) (markedSylow.subtype markedSylow_le_parabolic)
  have hk' : (k : Group) • (x • S) = markedSylow := by
    apply Sylow.subtype_injective
    rw [Sylow.smul_subtype] at hk
    exact hk
  have hSM : ((k : Group) * x) • S = markedSylow := by
    simpa only [mul_smul] using hk'
  have hSM' : (S : Subgroup Group).map (MulAut.conj ((k : Group) * x)).toMonoidHom =
      markedSylow := congrArg Sylow.toSubgroup hSM
  have hcomp : (MulAut.conj ((k : Group) * x)).toMonoidHom =
      (MulAut.conj (k : Group)).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨(k : Group) * x, ?_, hSM', ?_⟩
  · rw [hcomp, ← Subgroup.map_map, hx]
    exact mem_normalizer_iff_map_conj_eq.mp (parabolic.le_normalizer k.property)
  · rw [fixedSpace_map_conjugation, hSM', markedSylow_fixedSpace]

/-- Consumer: the catalogue's actual residual join enters the marked six-space
without a geometric placement hypothesis. The original P and B enter its
stabilizer through the very same conjugation. -/
theorem source_flag_marking (S : Sylow 2 Group) (P B : Subgroup Group)
    (hSP : (S : Subgroup Group) ≤ P) (hSB : (S : Subgroup Group) ≤ B)
    (x : Group)
    (hP : P.map designProjection = Catalogue.partitionAt (designProjection x))
    (hB : B.map designProjection = Catalogue.pairAt (designProjection x)) :
    ∃ g : Group,
      ((S : Subgroup Group) ⊔ twoResidual P ⊔ twoResidual B).map
        (MulAut.conj g).toMonoidHom = parabolic ∧
      (S : Subgroup Group).map (MulAut.conj g).toMonoidHom = markedSylow ∧
      (fixedSpace representation S).map (actionEquiv g).toLinearMap =
        binaryLine markedVector ∧
      P.map (MulAut.conj g).toMonoidHom ≤ parabolic ∧
      B.map (MulAut.conj g).toMonoidHom ≤ parabolic := by
  have hD := generated_eq_hexadPreimage S P B hSP hSB (designProjection x) hP hB
  have hPH : P ≤ hexadPreimage (designProjection x • m22Hexad123) :=
    map_le_iff_le_comap.mp (hP ▸ Catalogue.partitionAt_le_hexad _)
  have hBH : B ≤ hexadPreimage (designProjection x • m22Hexad123) :=
    map_le_iff_le_comap.mp (hB ▸ Catalogue.pairAt_le_hexad _)
  obtain ⟨g, hg, hSg, hline⟩ := exists_flag_marking _
    (conjugate_hexad_mem (designProjection x)) S (hSP.trans hPH)
  exact ⟨g, hD ▸ hg, hSg, hline, hg ▸ map_mono hPH, hg ▸ map_mono hBH⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.DesignFlag

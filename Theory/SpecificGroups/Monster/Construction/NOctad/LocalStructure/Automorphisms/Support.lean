module
public import Theory.SpecificGroups.Monster.Construction.NOctad.Coordinates
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Comparison
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Kernel
public import Theory.Representation.MathieuCodeRestriction.CodeLocal

/-!
# The actual Golay octad support quotient

The coordinate comparison with the native Witt design identifies the literal
support stabilizers and intertwines their restrictions to the eight points.
The proved native action image therefore gives exactly the alternating group
on the Golay support, with no abstract model identification assumed.

Source: Aschbacher, *Sporadic Groups*, 19.1(3) and 29.13(3), printed
pp. 85–86 and 160. The imported ATLAS code comparison retains its license and
attribution in `MathieuCodeRestriction.AtlasComparison`; no port is duplicated.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure.Automorphisms
open LocalC LocalC.ShortFamilies TrialitySpin
open Atlas.Codes Atlas.Fischer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

/-- Stabilizer of the actual Golay support word. -/
def supportStabilizer (c : NOctad.Octad) : Subgroup Mathieu24CodeModel where
  carrier := {g | ∀ i, c.val.val (g.val i) = c.val.val i}
  one_mem' _ := rfl
  mul_mem' := by
    intro g h hg hh i
    exact (hg (h.val i)).trans (hh i)
  inv_mem' := by
    intro g hg i
    change c.val.val (g.val.symm i) = c.val.val i
    simpa only [Equiv.apply_symm_apply] using (hg (g.val.symm i)).symm

theorem mem_supportStabilizer_iff (c : NOctad.Octad) (g : Mathieu24CodeModel) :
    g ∈ supportStabilizer c ↔ parkerCodeEquiv g c.val = c.val := by
  constructor
  · intro h
    apply Subtype.ext
    funext i
    exact (h (g.val.symm i)).symm.trans (congrArg c.val.val (g.val.apply_symm_apply i))
  · intro h i
    have he := congrArg (fun a : golay => a.val (g.val i)) h
    change c.val.val (g.val.symm (g.val i)) = c.val.val (g.val i) at he
    rw [Equiv.symm_apply_apply] at he
    exact he.symm

/-- Literal restriction to the eight support positions. -/
def supportAction (c : NOctad.Octad) : supportStabilizer c →* Equiv.Perm (Support c) where
  toFun g := g.val.val.subtypePerm (fun i => by
    rw [g.prop i])
  map_one' := by apply Equiv.ext; intro i; apply Subtype.ext; rfl
  map_mul' g h := by apply Equiv.ext; intro i; apply Subtype.ext; rfl

@[simp] theorem supportAction_apply (c : NOctad.Octad) (g : supportStabilizer c)
    (i : Support c) : (supportAction c g i).val = g.val.val i.val := rfl

theorem supportAction_kernel_iff (c : NOctad.Octad) (g : supportStabilizer c) :
    g ∈ (supportAction c).ker ↔ ∀ i : Support c, g.val.val i.val = i.val := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i
    exact congrArg Subtype.val (Equiv.congr_fun h i)
  · intro h
    exact Equiv.ext fun i => Subtype.ext (h i)

/-- The same octad in the certified native Witt-design coordinates. -/
def nativeOctad (c : NOctad.Octad) : Sporadic.Mathieu.M24LocalGeometry.Octad :=
  ⟨Atlas.Codes.support (MathieuCode.atlasWordEquiv c.val.val), by
    obtain ⟨u, hu⟩ := MathieuCode.golay_exists_word
      (MathieuCode.atlasWordEquiv_mem_golay c.val.prop)
    have he : Atlas.Codes.support (MathieuCode.atlasWordEquiv c.val.val) =
        Sporadic.Mathieu.m24GolayWord u := by
      rw [hu, ← MathieuCode.wordOfSet_golayWord]
      ext i
      simp [Atlas.Codes.support, MathieuCode.wordOfSet]
    rw [he]
    apply Sporadic.Mathieu.m24GolayWord_mem_blocks_of_card_eq_eight
    rw [← he]
    exact (MathieuCode.hammingNorm_atlasWordEquiv _).trans c.prop⟩

@[simp] theorem mem_nativeOctad (c : NOctad.Octad) (i : Fin 24) :
    i ∈ (nativeOctad c).val ↔ c.val.val (MathieuCode.atlasPointEquiv.symm i) ≠ 0 := by
  unfold nativeOctad
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ i))

/-- This comparison retains each coordinate, rather than choosing an abstract A8 model. -/
def supportEquiv (c : NOctad.Octad) : Support c ≃ (nativeOctad c).val where
  toFun i := ⟨MathieuCode.atlasPointEquiv i.val, by simpa using i.prop⟩
  invFun i := ⟨MathieuCode.atlasPointEquiv.symm i.val, (mem_nativeOctad c i.val).mp i.prop⟩
  left_inv i := Subtype.ext (MathieuCode.atlasPointEquiv.symm_apply_apply i.val)
  right_inv i := Subtype.ext (MathieuCode.atlasPointEquiv.apply_symm_apply i.val)

private theorem bit_eq_iff (a b : Bit) : a = b ↔ (a ≠ 0 ↔ b ≠ 0) := by
  revert a b
  decide

private theorem groupEquiv_point (g : Sporadic.Mathieu.M24) (i : Omega) :
    (Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv g).val i =
      MathieuCode.atlasPointEquiv.symm (g.val (MathieuCode.atlasPointEquiv i)) := rfl

theorem native_stabilizer_iff (c : NOctad.Octad) (g : Sporadic.Mathieu.M24) :
    Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv g ∈ supportStabilizer c ↔
      g ∈ Sporadic.Mathieu.M24LocalGeometry.octadStabilizer (nativeOctad c) := by
  change _ ↔ g ∈ MulAction.stabilizer Sporadic.Mathieu.M24 (nativeOctad c).val
  rw [MulAction.mem_stabilizer_finset]
  change (∀ i, c.val.val ((Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv g).val i) = c.val.val i) ↔ _
  constructor
  · intro h i
    have hi := (bit_eq_iff _ _).mp (h (MathieuCode.atlasPointEquiv.symm i))
    simpa only [groupEquiv_point, Equiv.apply_symm_apply, mem_nativeOctad, Subgroup.smul_def, Equiv.Perm.smul_def] using hi
  · intro h i
    have hi := h (MathieuCode.atlasPointEquiv i)
    apply (bit_eq_iff _ _).mpr
    simpa only [mem_nativeOctad, Equiv.symm_apply_apply, groupEquiv_point, Subgroup.smul_def, Equiv.Perm.smul_def] using hi

/-- Coordinate-compatible equivalence of the literal octad stabilizers. -/
def nativeStabilizerHom (c : NOctad.Octad) :
    Sporadic.Mathieu.M24LocalGeometry.octadStabilizer (nativeOctad c) →*
      supportStabilizer c :=
  (Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv.toMonoidHom.comp
    (Sporadic.Mathieu.M24LocalGeometry.octadStabilizer (nativeOctad c)).subtype).codRestrict _
      (fun g => (native_stabilizer_iff c g.val).mpr g.prop)

theorem nativeStabilizerHom_surjective (c : NOctad.Octad) :
    Function.Surjective (nativeStabilizerHom c) := by
  intro g
  obtain ⟨h, hh⟩ := Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv.surjective g.val
  exact ⟨⟨h, (native_stabilizer_iff c h).mp (hh ▸ g.prop)⟩, Subtype.ext hh⟩

theorem supportAction_native (c : NOctad.Octad)
    (g : Sporadic.Mathieu.M24LocalGeometry.octadStabilizer (nativeOctad c)) :
    (supportEquiv c).permCongr (supportAction c (nativeStabilizerHom c g)) =
      MathieuCode.CocodeOctad.coordinateAction (nativeOctad c) g := by
  apply Equiv.ext
  intro i
  apply Subtype.ext
  change MathieuCode.atlasPointEquiv
    (MathieuCode.atlasPointEquiv.symm (g.val.val
      (MathieuCode.atlasPointEquiv (MathieuCode.atlasPointEquiv.symm i.val)))) = _
  simp only [Equiv.apply_symm_apply]
  rfl

/-- The support image is the actual alternating group on the eight positions. -/
theorem supportAction_range (c : NOctad.Octad) :
    (supportAction c).range = alternatingGroup (Support c) := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨h, rfl⟩ := nativeStabilizerHom_surjective c g
    apply Equiv.Perm.mem_alternatingGroup.mpr
    rw [← Equiv.Perm.sign_permCongr (supportEquiv c), supportAction_native]
    apply Equiv.Perm.mem_alternatingGroup.mp
    rw [← MathieuCode.CocodeOctad.coordinateAction_range]
    exact ⟨h, rfl⟩
  · intro hp
    have hm : (supportEquiv c).permCongr p ∈
        (MathieuCode.CocodeOctad.coordinateAction (nativeOctad c)).range := by
      rw [MathieuCode.CocodeOctad.coordinateAction_range]
      apply Equiv.Perm.mem_alternatingGroup.mpr
      rw [Equiv.Perm.sign_permCongr]
      exact Equiv.Perm.mem_alternatingGroup.mp hp
    obtain ⟨g, hg⟩ := hm
    refine ⟨nativeStabilizerHom c g, (supportEquiv c).permCongr.injective ?_⟩
    rw [supportAction_native, hg]

end Sporadic.Monster.Construction.NOctad.LocalStructure.Automorphisms

module
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.Marking
public import Theory.Mathieu.M22.ChapterHLocalClassification.SextetRestriction
public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadKernels
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility

/-!
# A common ambient, outer and inner Sylow marking for M22

A certified native M24 conjugator aligns the enumerated order-1024 subgroup
with the source octad, sextet and trio. The preimages in the literal setwise
and pointwise stabilizers of {0,9} have orders 256 and 128, respectively,
so they are Sylow subgroups. Their compatibility is expressed through the
original embeddings, including the inner intersection in the outer group.
The sextet translations and intrinsic hexad core lie in these Sylows by
relative normality of the appropriate intrinsic two-cores.

The extra adjustment of the marking matters: simply composing the earlier
three-object marking with m22GeometryConjugator gives pair intersections of
only half these orders. The 12 Golay row checks here certify the corrected
native conjugator; the existing 1024-word enumeration certifies both counts.
No normality of an arbitrary elementary subgroup is used.

Source: Aschbacher--Smith H.14 setup and H.14.3(1), printed pp.396--397,
combined manuscript of 1 March 2004. The generators and Golay certificates
are reused from the native development; no new ATLAS port is used.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open scoped Pointwise
namespace Sporadic.Mathieu.M22ChapterH.CompatibleSylow
open SylowNormalizer.OrderEnumeration PairOvergroups PairOvergroups.QuotientConstruction

def transportPerm : Equiv.Perm (Fin 24) where
  toFun := ![9,12,22,7,20,18,1,11,14,2,21,0,8,5,19,3,13,17,4,23,15,10,16,6]
  invFun := ![11,6,9,15,18,13,23,3,12,0,21,7,1,16,8,20,22,17,5,14,4,10,2,19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def rowMessage : Fin 12 → Fin 4096 :=
  ![840,72,336,2192,2312,2128,338,3400,88,2324,2329,2088]

private theorem transport_rows : ∀ i,
    m24PermuteMask transportPerm (m24GolayRow i) = m24GolayCode (rowMessage i) := by
  decide +kernel

def transport : M24 :=
  ⟨transportPerm, by
    exact AffineLiftConstruction.mem_M24_of_rows _
      (fun i => ⟨rowMessage i, transport_rows i⟩)⟩

def ambient : Sylow 2 M24 := transport • SextetCore.nativeSylow

theorem ambient_coe : ambient.toSubgroup =
    SylowNormalizer.candidate.map (MulAut.conj transport).toMonoidHom := rfl

theorem ambient_le_octad : ambient.toSubgroup ≤ octadStabilizer m22SourceOctad := by
  rw [ambient_coe, Subgroup.map_le_iff_le_comap, SylowNormalizer.candidate,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  change (transportPerm * SylowNormalizer.generatorPerm i * transportPerm⁻¹) •
    m22SourceOctad.val = m22SourceOctad.val
  revert i
  decide +kernel

theorem ambient_le_sextet : ambient.toSubgroup ≤ sextetStabilizer m22SourceSextet := by
  rw [ambient_coe, Subgroup.map_le_iff_le_comap, SylowNormalizer.candidate,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  change (transportPerm * SylowNormalizer.generatorPerm i * transportPerm⁻¹) •
    m22SourceSextet.parts = m22SourceSextet.parts
  revert i
  decide +kernel

theorem ambient_le_trio : ambient.toSubgroup ≤ trioStabilizer m22SourceTrio := by
  rw [ambient_coe, Subgroup.map_le_iff_le_comap, SylowNormalizer.candidate,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  change (transportPerm * SylowNormalizer.generatorPerm i * transportPerm⁻¹) •
    m22SourceTrio.parts = m22SourceTrio.parts
  revert i
  decide +kernel

def innerGroup : Subgroup M22 := ambient.toSubgroup.comap m22Embedding

def outerGroup : Subgroup m22PairStabilizer := ambient.toSubgroup.comap m22PairStabilizer.subtype

def row (i : Fin 1024) : M24 := MulAut.conj transport (element i).val

theorem row_mem (i : Fin 1024) : row i ∈ ambient := ⟨_, (element i).property, rfl⟩

def point (i : Fin 1024) (x : Fin 24) : Fin 24 :=
  transportPerm (SylowNormalizer.OrderEnumeration.point i (transportPerm.symm x))

theorem row_apply (i : Fin 1024) (x : Fin 24) : (row i).val x = point i x := by
  change transportPerm ((element i).val.val (transportPerm.symm x)) = _
  rw [element_apply]
  rfl

theorem row_injective : Function.Injective row := by
  intro i j h
  apply element_injective
  exact Subtype.ext ((MulAut.conj transport).injective h)

theorem row_surjective (g : M24) (hg : g ∈ ambient) : ∃ i, row i = g := by
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨i, hi⟩ := element_surjective ⟨a, ha⟩
  exact ⟨i, congrArg (fun x : SylowNormalizer.candidate =>
    MulAut.conj transport x.val) hi⟩

private theorem source_core_le_ambient : Sextet.sourceCore ≤ ambient.toSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  exact (pCore_isPGroup.le_sylow_of_normal (ambient.subtype ambient_le_sextet)) hx

theorem innerTranslations_le : Sextet.innerTranslations ≤ innerGroup :=
  Subgroup.comap_mono source_core_le_ambient

theorem outerTranslations_le : Sextet.outerTranslations ≤ outerGroup :=
  Subgroup.comap_mono source_core_le_ambient

theorem innerHexad_le : m22InnerHexadKernel m22SourceOctad ≤ innerGroup := by
  intro x hx
  have hm := Subgroup.mem_map_of_mem m22Embedding hx
  rw [Hexad.inner_kernel_image] at hm
  rw [← octad_core_map_eq_pointwise] at hm
  obtain ⟨a, ha, he⟩ := hm
  change m22Embedding x ∈ ambient.toSubgroup
  rw [← he]
  exact (pCore_isPGroup.le_sylow_of_normal (ambient.subtype ambient_le_octad)) ha


abbrev InnerIndex := {i : Fin 1024 // point i 0 = 0 ∧ point i 9 = 9}
abbrev OuterIndex := {i : Fin 1024 // point i 0 ∈ m22Pair ∧ point i 9 ∈ m22Pair}

private theorem innerIndex_card : Fintype.card InnerIndex = 128 := by decide +kernel
private theorem outerIndex_card : Fintype.card OuterIndex = 256 := by decide +kernel

theorem row_inner_iff (i : Fin 1024) : row i ∈ m22Embedding.range ↔
    point i 0 = 0 ∧ point i 9 = 9 := by
  rw [m22Embedding_range]
  change ((row i).val 0 = 0 ∧ (row i).val 9 = 9) ↔ _
  rw [row_apply, row_apply]

theorem row_outer_iff (i : Fin 1024) : row i ∈ m22PairStabilizer ↔
    point i 0 ∈ m22Pair ∧ point i 9 ∈ m22Pair := by
  rw [m22PairStabilizer, MulAction.mem_stabilizer_finset']
  constructor
  · intro h
    have h0 := h (b := 0) (by simp [m22Pair])
    have h9 := h (b := 9) (by simp [m22Pair])
    change (row i).val 0 ∈ m22Pair at h0
    change (row i).val 9 ∈ m22Pair at h9
    simpa only [row_apply] using And.intro h0 h9
  · rintro ⟨h0, h9⟩ a ha
    have ha' : a = 0 ∨ a = 9 := by simpa [m22Pair] using ha
    rcases ha' with rfl | rfl
    · change (row i).val 0 ∈ m22Pair
      rwa [row_apply]
    · change (row i).val 9 ∈ m22Pair
      rwa [row_apply]

def innerElement (i : InnerIndex) : innerGroup := by
  have hi := (row_inner_iff i.val).mpr i.property
  exact ⟨hi.choose, by
    change m22Embedding hi.choose ∈ ambient
    rw [hi.choose_spec]
    exact row_mem _⟩

theorem innerElement_embedding (i : InnerIndex) :
    m22Embedding (innerElement i).val = row i.val :=
  ((row_inner_iff i.val).mpr i.property).choose_spec

def outerElement (i : OuterIndex) : outerGroup :=
  ⟨⟨row i.val, (row_outer_iff i.val).mpr i.property⟩, row_mem i.val⟩

theorem innerElement_bijective : Function.Bijective innerElement := by
  constructor
  · intro i j h
    apply Subtype.ext
    apply row_injective
    simpa only [innerElement_embedding] using
      congrArg (fun g : innerGroup => m22Embedding g.val) h
  · intro g
    obtain ⟨i, hi⟩ := row_surjective (m22Embedding g.val) g.property
    have hp := (row_inner_iff i).mp (hi.symm ▸ (show m22Embedding g.val ∈
      m22Embedding.range from ⟨g.val, rfl⟩))
    refine ⟨⟨i, hp⟩, Subtype.ext (m22Embedding_injective ?_)⟩
    exact (innerElement_embedding _).trans hi

theorem outerElement_bijective : Function.Bijective outerElement := by
  constructor
  · intro i j h
    exact Subtype.ext (row_injective (congrArg (fun g : outerGroup => g.val.val) h))
  · intro g
    obtain ⟨i, hi⟩ := row_surjective g.val.val g.property
    exact ⟨⟨i, (row_outer_iff i).mp (hi.symm ▸ g.val.property)⟩,
      Subtype.ext (Subtype.ext hi)⟩

theorem innerGroup_card : Nat.card innerGroup = 128 := by
  rw [← Nat.card_congr (Equiv.ofBijective innerElement innerElement_bijective),
    Nat.card_eq_fintype_card, innerIndex_card]

theorem outerGroup_card : Nat.card outerGroup = 256 := by
  rw [← Nat.card_congr (Equiv.ofBijective outerElement outerElement_bijective),
    Nat.card_eq_fintype_card, outerIndex_card]

def inner : Sylow 2 M22 := Sylow.ofCard innerGroup (by
  rw [innerGroup_card, m22_order]
  decide +kernel)

def outer : Sylow 2 m22PairStabilizer := Sylow.ofCard outerGroup (by
  rw [outerGroup_card, m22PairStabilizer_card]
  decide +kernel)

@[simp] theorem inner_coe : inner.toSubgroup = ambient.toSubgroup.comap m22Embedding := rfl
@[simp] theorem outer_coe : outer.toSubgroup =
    ambient.toSubgroup.comap m22PairStabilizer.subtype := rfl

/-- The inner Sylow is the literal preimage through the native inclusion. -/
theorem outer_comap_inner : outer.toSubgroup.comap m22ToPairStabilizer =
    inner.toSubgroup := rfl

/-- Inside the pair group the inner Sylow is its actual intersection with M22. -/
theorem inner_map_pair : inner.toSubgroup.map m22ToPairStabilizer =
    outer.toSubgroup ⊓ m22ToPairStabilizer.range := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y, rfl⟩
  · rintro ⟨hx, y, rfl⟩
    exact ⟨y, hx, rfl⟩

private theorem elementary_comap {G J : Type*} [Group G] [Group J]
    (f : G →* J) (hf : Function.Injective f) (D : Subgroup J)
    (hD : IsElementaryAbelian 2 D) : IsElementaryAbelian 2 (D.comap f) := by
  let r : D.comap f →* D :=
    (f.comp (D.comap f).subtype).codRestrict _ (fun g => g.property)
  have hr : Function.Injective r := fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))
  refine { is_comm := ⟨fun x y => hr ?_⟩, exponent_dvd_p := ?_ }
  · simpa only [map_mul] using hD.toIsMulCommutative.is_comm.comm (r x) (r y)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply hr
    simpa only [map_pow, map_one] using
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hD.exponent_dvd_p (r x))

theorem innerTranslations_elementary : IsElementaryAbelian 2 Sextet.innerTranslations :=
  elementary_comap m22Embedding m22Embedding_injective _ Sextet.sourceCore_elementary

theorem outerTranslations_elementary : IsElementaryAbelian 2 Sextet.outerTranslations :=
  elementary_comap m22PairStabilizer.subtype m22PairStabilizer.subtype_injective _
    Sextet.sourceCore_elementary

/-- This is exactly the source's simultaneous ambient/outer/inner Sylow choice. -/
theorem compatible :
    ambient.toSubgroup ≤ octadStabilizer m22SourceOctad ∧
    ambient.toSubgroup ≤ sextetStabilizer m22SourceSextet ∧
    ambient.toSubgroup ≤ trioStabilizer m22SourceTrio ∧
    outer.toSubgroup = ambient.toSubgroup.comap m22PairStabilizer.subtype ∧
    inner.toSubgroup = ambient.toSubgroup.comap m22Embedding ∧
    inner.toSubgroup = outer.toSubgroup.comap m22ToPairStabilizer :=
  ⟨ambient_le_octad, ambient_le_sextet, ambient_le_trio, rfl, rfl, rfl⟩

end Sporadic.Mathieu.M22ChapterH.CompatibleSylow

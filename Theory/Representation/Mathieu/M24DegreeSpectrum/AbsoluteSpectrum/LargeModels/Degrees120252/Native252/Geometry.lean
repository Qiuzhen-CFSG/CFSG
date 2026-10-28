module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Geometry.Forward
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252
public import Theory.Mathieu.M24.LocalGeometry.Stabilizers
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport.Markings

/-!
# The 1771 saved partitions are exactly the native sextets

The checked forward equations make the saved range stable under the native
standard pair, hence under all of M24. The first partition is the standard
sextet. Its actual orbit has 244823040 / 138240 = 1771 elements by the native
orbit-stabilizer theorem. Choosing a saved index for each orbit element gives
an injection into `Fin 1771`; equality of cardinalities makes it bijective.
Thus the literal partition map is injective and each row is a native sextet.
Native sextet transitivity supplies the converse, yielding the equivalence
without any separate cardinality-based model identification.

The all-elements index equation and native-realization application below
consume these unconditional facts. The independent covector certificates
remain the parent's linear-algebra obligation.

Sources: James, J. Algebra 27 (1973), 57–111; GM02 Proposition 5.1;
Aschbacher–Smith H.15.3(1) for native sextet transitivity. Saved data provenance:
`Degrees120252/source/README.md` and `Native252/source/README.md`.
The imported native/ATLAS stabilizer comparison retains its attribution and
license in `SextetCore/Comparison.lean` and `LICENSES/ATLAS.txt`.
-/

open scoped Pointwise
open Sporadic.Mathieu M24LocalGeometry
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Geometry
public noncomputable section
private abbrev Orbit := MulAction.orbit M24 standardSextet.parts
private theorem orbit_card : Nat.card Orbit = 1771 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup M24 standardSextet.parts)
  rw [Nat.card_prod, m24_order] at h
  change Nat.card Orbit * Nat.card (sextetStabilizer standardSextet) = 244823040 at h
  rw [SextetCore.stabilizer_card] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 138240) h

private theorem stable (g : M24) (i : Fin 1771) : ∃ k, pointParts k = g • pointParts i := by
  classical
  let r := Finset.univ.image pointParts
  have hle : Subgroup.closure (Set.range actor) ≤ MulAction.stabilizer M24 r := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    change actor j • r = r
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_smul_finset.mp hp
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hq
      rw [pointParts_forward]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · simp
  have hg : g • r = r := hle (by rw [actors_closure_eq_top]; trivial)
  have hi : g • pointParts i ∈ r := by
    rw [← hg]
    exact Finset.smul_mem_smul_finset (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hi
  exact ⟨k,hk⟩

private theorem seed : pointParts 0 = standardSextet.parts := by decide +kernel

private theorem orbit_covered (p : Orbit) : ∃ i, pointParts i = p.val := by
  obtain ⟨g,hg⟩ := p.property
  obtain ⟨i,hi⟩ := stable g 0
  exact ⟨i, by rw [hi, seed]; exact hg⟩

private def orbitIndex (p : Orbit) : Fin 1771 := (orbit_covered p).choose
private theorem orbitIndex_parts (p : Orbit) : pointParts (orbitIndex p) = p.val :=
  (orbit_covered p).choose_spec
private theorem orbitIndex_bijective : Function.Bijective orbitIndex := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by rw [orbit_card, Nat.card_fin]⟩
  intro p q h
  apply Subtype.ext
  rw [← orbitIndex_parts p, ← orbitIndex_parts q, h]

theorem pointParts_injective : Function.Injective pointParts := by
  intro i k h
  obtain ⟨p,rfl⟩ := orbitIndex_bijective.surjective i
  obtain ⟨q,rfl⟩ := orbitIndex_bijective.surjective k
  apply congrArg orbitIndex
  apply Subtype.ext
  simpa only [orbitIndex_parts] using h

private theorem exists_sextet (i : Fin 1771) : ∃ S : Sextet, S.parts = pointParts i := by
  obtain ⟨p,rfl⟩ := orbitIndex_bijective.surjective i
  obtain ⟨g,hg⟩ := p.property
  refine ⟨Stabilizers.conjugateSextet g standardSextet, ?_⟩
  change g • standardSextet.parts = _
  rw [orbitIndex_parts]; exact hg

private theorem sextet_ext {S T : Sextet} (h : S.parts = T.parts) : S = T := by
  cases S
  cases T
  cases h
  rfl

private def listedSextet (i : Fin 1771) : Sextet := (exists_sextet i).choose
private theorem listedSextet_parts (i : Fin 1771) : (listedSextet i).parts = pointParts i :=
  (exists_sextet i).choose_spec
private theorem listedSextet_bijective : Function.Bijective listedSextet := by
  constructor
  · intro i k h
    apply pointParts_injective
    simpa only [listedSextet_parts] using congrArg Sextet.parts h
  · intro S
    obtain ⟨g,hg⟩ := MathieuCode.SextetLayers.CoordinateTransport.exists_sextet_conjugator S
    obtain ⟨i,hi⟩ := stable g 0
    refine ⟨i, sextet_ext ?_⟩
    rw [listedSextet_parts, hi, seed, hg]

/-- The saved partitions, identified with all actual native sextets. -/
def sextetEquiv : Fin 1771 ≃ Sextet :=
  Equiv.ofBijective listedSextet listedSextet_bijective

/-- The equivalence retains every native point label and literal part. -/
theorem sextetEquiv_parts (i : Fin 1771) : (sextetEquiv i).parts = pointParts i :=
  listedSextet_parts i

/-- The unconditional all-elements equation for the existing index action. -/
theorem pointParts_index (g : M24) (i : Fin 1771) :
    pointParts (Native252.index pointParts_injective pointParts_forward g i) =
      g • pointParts i :=
  Native252.pointParts_index pointParts_injective pointParts_forward g i

/-- The existing index action transports to the literal native sextet action. -/
theorem sextetEquiv_index (g : M24) (i : Fin 1771) :
    sextetEquiv (Native252.index pointParts_injective pointParts_forward g i) =
      Stabilizers.conjugateSextet g (sextetEquiv i) := by
  apply sextet_ext
  change (sextetEquiv (Native252.index pointParts_injective pointParts_forward g i)).parts =
    g • (sextetEquiv i).parts
  rw [sextetEquiv_parts, pointParts_index, sextetEquiv_parts]

/-- Actual realization consumer: the geometric premises are discharged;
only the independent linear certificates remain. -/
def native252OfLinearCertificates
    (hE : Function.Injective Native252.embedding)
    (hEA : ∀ j i k, (embeddingMatrix * matrix252 j) (forward j i) k = embeddingMatrix i k) :
    NativeRealization 252 matrix252 :=
  native252OfCertificates pointParts_injective pointParts_forward hE hEA

end
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Geometry

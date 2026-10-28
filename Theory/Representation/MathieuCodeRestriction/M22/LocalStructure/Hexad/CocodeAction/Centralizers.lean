module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.PairRigidity
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.FixedSpaces
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Pointwise centralizers in the pair-line quotient

An actor fixing the quotient common fixed space must lie in the intrinsic
hexad kernel: apply the geometric pair-class test. Exact fixed-vector lifting
for this actor now excludes a nontrivial shear into the removed pair line.
Consequently the M24 pointwise-centralizer equality descends to M22. Actual
conjugation of both the element and its fixed space gives the class transfer.

The earlier M24 centralizer theorem, H.14 displacement and group conjugacy
facts remain explicit inputs. No M22 centralizer or no-shear conclusion is
assumed. The same argument handles the native inner embedding and the literal
setwise pair stabilizer.

Source: Aschbacher--Smith, H.15.2(5), printed pp.398--399,
combined manuscript of 1 March 2004.
-/

public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
open scoped Pointwise
namespace MathieuCode.Hexad.CocodeAction
noncomputable section
variable {G : Type*} [Group G]

/-- The actual kernel fixes every geometric octad pair class. -/
theorem quotient_pair_mem_fixedSpace {f : G →* m22PairStabilizer}
    {K : Subgroup G} {O : Octad}
    (hK : K.map (m22PairStabilizer.subtype.comp f) = octadPointwiseKernel O)
    (P : PointPair) (hP : P.val ⊆ O.val) :
    m22PairLine.mkQ (pairVector P) ∈ fixedSpace (quotientRepresentation f) K := by
  intro a
  change m22PairLine.mkQ (cocodeRepresentation (f a.val).val (pairVector P)) = _
  congr 1
  apply (pairVector_fixed_iff _ _).mpr
  have ha : (f a.val).val ∈ octadPointwiseKernel O := by
    rw [← hK]
    exact Subgroup.mem_map_of_mem _ a.property
  have hp (i : Fin 24) (hi : i ∈ P.val) : (f a.val).val • i = i :=
    (mem_octadPointwiseKernel O _).mp ha i (hP hi)
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_smul_finset.mp hi
    rwa [hp j hj]
  · intro hi
    exact Finset.mem_smul_finset.mpr ⟨i, hi, hp i hi⟩

/-- Pointwise fixation of the five-dimensional common fixed space forces
membership in the genuine intrinsic kernel. This is the extra rigidity step
needed before applying exact fixed-vector lifting. -/
theorem fixedSpace_pointwiseKernel {f : G →* m22PairStabilizer}
    {K : Subgroup G} {O : Octad} (hf : Function.Injective f)
    (hK : K.map (m22PairStabilizer.subtype.comp f) = octadPointwiseKernel O)
    (hO : m22Pair ⊆ O.val) :
    subspaceKernel (quotientRepresentation f) (fixedSpace (quotientRepresentation f) K) ⊤ = K := by
  apply le_antisymm
  · intro g hg
    have hmem := octad_kernel_of_quotient_pairs_fixed O hO (f g)
      (fun P hP => hg.2 _ (quotient_pair_mem_fixedSpace hK P
        (hP.trans Finset.sdiff_subset)))
    rw [← hK] at hmem
    obtain ⟨a, ha, he⟩ := hmem
    have hval : a = g := (Subtype.val_injective.comp hf) he
    exact hval ▸ ha
  · intro g hg
    exact ⟨Subgroup.mem_top g, fun v hv => hv ⟨g, hg⟩⟩

/-- Descend the M24 pointwise-centralizer theorem through the removed pair
line. Fixing the quotient common fixed space first puts the actor in K;
H.14 displacement then rules out all shears into that line. -/
theorem element_pointwiseCentralizer
    {f : G →* m22PairStabilizer} {K : Subgroup G} {O : Octad}
    (h : RestrictionInput f K O) (hO : m22Pair ⊆ O.val)
    (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (z : G) (hz : z ∈ K)
    (hc : subspaceKernel cocodeRepresentation
      (fixedSpace cocodeRepresentation (Subgroup.zpowers (f z).val)) ⊤ =
        Subgroup.zpowers (f z).val) :
    subspaceKernel (quotientRepresentation f)
      (fixedSpace (quotientRepresentation f) (Subgroup.zpowers z)) ⊤ = Subgroup.zpowers z := by
  apply le_antisymm
  · intro a ha
    have haK : a ∈ K := by
      rw [← fixedSpace_pointwiseKernel h.injective h.kernel_image hO]
      refine ⟨Subgroup.mem_top _, fun v hv => ha.2 v ?_⟩
      exact (mem_fixedSpace_zpowers_iff _ _ _).mpr (hv ⟨z, hz⟩)
    have haf : (f a).val ∈ subspaceKernel cocodeRepresentation
        (fixedSpace cocodeRepresentation (Subgroup.zpowers (f z).val)) ⊤ := by
      refine ⟨Subgroup.mem_top _, ?_⟩
      intro v hv
      have hvq : m22PairLine.mkQ v ∈ fixedSpace (quotientRepresentation f) (Subgroup.zpowers z) := by
        apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
        change m22PairLine.mkQ (cocodeRepresentation (f z).val v) = m22PairLine.mkQ v
        rw [(mem_fixedSpace_zpowers_iff _ _ _).mp hv]
      have hfix := ha.2 _ hvq
      have hva : v ∈ (fixedSpace (quotientRepresentation f) (Subgroup.zpowers a)).comap m22PairLine.mkQ :=
        (mem_fixedSpace_zpowers_iff _ _ _).mpr hfix
      rw [h.fixedSpace_comap hd _ (Subgroup.zpowers_le.mpr haK), MonoidHom.map_zpowers] at hva
      exact (mem_fixedSpace_zpowers_iff _ _ _).mp hva
    rw [hc] at haf
    change (m22PairStabilizer.subtype.comp f) a ∈
      Subgroup.zpowers ((m22PairStabilizer.subtype.comp f) z) at haf
    rw [← MonoidHom.map_zpowers] at haf
    obtain ⟨b, hb, he⟩ := haf
    exact (Subtype.val_injective.comp h.injective) he ▸ hb
  · intro a ha
    exact ⟨Subgroup.mem_top _, fun v hv => hv ⟨a, ha⟩⟩

end
end MathieuCode.Hexad.CocodeAction


open Representation.BinaryOffender
namespace MathieuCode.Hexad.CocodeAction
noncomputable section
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Pointwise centralizers of element fixed spaces transport by the same actual
conjugating element as the involutions. -/
theorem pointwiseCentralizer_conjugate (ρ : Representation (ZMod 2) G V)
    (a z : G) (hz : IsConj a z)
    (ha : subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers a)) ⊤ = Subgroup.zpowers a) :
    subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers z)) ⊤ = Subgroup.zpowers z := by
  obtain ⟨t, rfl⟩ := isConj_iff.mp hz
  have hinv (v : V) : ρ t⁻¹ (ρ t v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  apply le_antisymm
  · intro b hb
    have hba : t⁻¹ * b * t ∈ subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers a)) ⊤ := by
      refine ⟨Subgroup.mem_top _, ?_⟩
      intro v hv
      have htv : ρ t v ∈ fixedSpace ρ (Subgroup.zpowers (t * a * t⁻¹)) := by
        apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
        simp only [map_mul, Module.End.mul_apply, hinv,
          (mem_fixedSpace_zpowers_iff _ _ _).mp hv]
      have hh := congrArg (ρ t⁻¹) (hb.2 _ htv)
      simpa only [map_mul, Module.End.mul_apply, hinv] using hh
    rw [ha] at hba
    have hm := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hba
    rw [MonoidHom.map_zpowers] at hm
    change t * (t⁻¹ * b * t) * t⁻¹ ∈ Subgroup.zpowers (t * a * t⁻¹) at hm
    simpa [mul_assoc] using hm
  · intro b hb
    exact ⟨Subgroup.mem_top _, fun v hv => hv ⟨b, hb⟩⟩
end
end MathieuCode.Hexad.CocodeAction

namespace MathieuCode.Hexad.CocodeAction
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender

/-- Precisely the earlier M24 pointwise-centralizer statement used below.
It concerns the eleven-dimensional cocode, before quotienting by the pair. -/
structure AmbientCentralizerInput (O : Octad) : Prop where
  centralizer : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
    subspaceKernel cocodeRepresentation
      (fixedSpace cocodeRepresentation (Subgroup.zpowers z)) ⊤ = Subgroup.zpowers z

/-- A genuine group-conjugacy witness transfers the kernel calculation to the
specified element. The source two-central class coverage is a separate H.14
input, supplied by the caller, rather than a centralizer hypothesis. -/
theorem pointwiseCentralizer_of_conjugate_kernel
    {G : Type*} [Group G] {f : G →* m22PairStabilizer}
    {K : Subgroup G} {O : Octad}
    (h : RestrictionInput f K O) (hO : m22Pair ⊆ O.val)
    (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (h24 : AmbientCentralizerInput O) (z : G)
    (hz : ∃ a ∈ K, a ≠ 1 ∧ IsConj a z) :
    subspaceKernel (quotientRepresentation f)
      (fixedSpace (quotientRepresentation f) (Subgroup.zpowers z)) ⊤ = Subgroup.zpowers z := by
  obtain ⟨a, ha, ha1, haz⟩ := hz
  have ham : (f a).val ∈ octadPointwiseKernel O := by
    rw [← h.kernel_image]
    exact Subgroup.mem_map_of_mem _ ha
  have ham1 : (f a).val ≠ 1 := by
    intro he
    apply ha1
    exact (Subtype.val_injective.comp h.injective)
      (he.trans (map_one (m22PairStabilizer.subtype.comp f)).symm)
  exact pointwiseCentralizer_conjugate (quotientRepresentation f) a z haz
    (element_pointwiseCentralizer h hO hd a ha (h24.centralizer _ ham ham1))

end MathieuCode.Hexad.CocodeAction

module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.Quotient
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.PairVectors
public import Theory.Representation.MathieuCodeRestriction.CodeLocal

/-!
# Fixed-space transfer from the M24 cocode to M22

The pair line is pointwise fixed. The earlier H.14 displacement four, together
with the M24 displacement four, proves that every fixed quotient class has a
fixed representative. This holds for every subgroup of the hexad kernel and
for the span of its nonidentity element fixed spaces. Rank-nullity subtracts
one from the ambient fixed dimension and preserves the codimension of xi.

`RestrictionInput` retains the actual embedding and the image of the actual
kernel, and only asks for the earlier H.14 element displacement. M24 inputs
are explicit. None of these results asserts those earlier group or module
inputs, the remaining representation identifications, or centralizer rigidity.
The same proofs apply to the inner inclusion and the identity of the outer
setwise pair group.

Source: Aschbacher--Smith, H.15.2(2),(4),(5), printed pp.398--399,
combined manuscript of 1 March 2004.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
namespace MathieuCode.Hexad

variable {G : Type*} [Group G]

abbrev ambientRepresentation (f : G →* m22PairStabilizer) : Representation (ZMod 2) G Cocode :=
  cocodeRepresentation.comp (m22PairStabilizer.subtype.comp f)

abbrev quotientRepresentation (f : G →* m22PairStabilizer) : Representation (ZMod 2) G M22Cocode :=
  m22OuterCocodeRepresentation.comp f

/-- Earlier group marking and H.14.4 displacement, with no H.15 conclusion. -/
structure RestrictionInput (f : G →* m22PairStabilizer) (K : Subgroup G) (O : Octad) : Prop where
  injective : Function.Injective f
  kernel_image : K.map (m22PairStabilizer.subtype.comp f) = octadPointwiseKernel O
  displacement : ∀ a ∈ K, a ≠ 1 → fixedCodim (quotientRepresentation f) (Subgroup.zpowers a) = 4

theorem pairLine_le_fixedSpace (f : G →* m22PairStabilizer) (A : Subgroup G) :
    m22PairLine ≤ fixedSpace (ambientRepresentation f) A := by
  intro v hv a
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  change cocodeRepresentation (f a.val).val (c • m22PairClass) = c • m22PairClass
  rw [map_smul, m22PairClass_invariant]

variable {f : G →* m22PairStabilizer} {K : Subgroup G} {O : Octad}
variable (h : RestrictionInput f K O)
include h

/-- The M24 fixed dimension six rules out a trivial marked kernel. -/
theorem RestrictionInput.kernel_ne_bot
    (h6 : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (octadPointwiseKernel O)) = 6) :
    K ≠ ⊥ := by
  intro hK
  have he : octadPointwiseKernel O = ⊥ := by
    rw [← h.kernel_image, hK, Subgroup.map_bot]
  rw [he, fixedSpace_bot, finrank_top, finrank_cocode] at h6
  exact (by decide : (11 : ℕ) ≠ 6) h6

theorem RestrictionInput.element_codim_eq
    (h24 : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (a : G) (ha : a ∈ K) (ha1 : a ≠ 1) :
    fixedCodim (ambientRepresentation f) (Subgroup.zpowers a) =
      fixedCodim (quotientRepresentation f) (Subgroup.zpowers a) := by
  rw [h.displacement a ha ha1]
  unfold fixedCodim
  rw [fixedSpace_comp_map, MonoidHom.map_zpowers]
  apply h24
  · rw [← h.kernel_image]
    exact Subgroup.mem_map_of_mem _ ha
  · intro he
    apply ha1
    exact (Subtype.val_injective.comp h.injective)
      (he.trans (map_one (m22PairStabilizer.subtype.comp f)).symm)

theorem RestrictionInput.fixedSpace_eq_map
    (h24 : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (A : Subgroup G) (hA : A ≤ K) :
    fixedSpace (quotientRepresentation f) A =
      (fixedSpace cocodeRepresentation (A.map (m22PairStabilizer.subtype.comp f))).map
        m22PairLine.mkQ := by
  rw [← fixedSpace_comp_map]
  symm
  apply HexadTransfer.fixedSpace_map_eq_of_element_codim
    (ambientRepresentation f) (quotientRepresentation f) m22PairLine.mkQ
    m22PairLine.mkQ_surjective (fun _ _ => rfl) K _ (h.element_codim_eq h24) A hA
  rw [Submodule.ker_mkQ]
  exact pairLine_le_fixedSpace f K

theorem RestrictionInput.fixedSpace_comap
    (h24 : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (A : Subgroup G) (hA : A ≤ K) :
    (fixedSpace (quotientRepresentation f) A).comap m22PairLine.mkQ =
      fixedSpace cocodeRepresentation (A.map (m22PairStabilizer.subtype.comp f)) := by
  rw [h.fixedSpace_eq_map h24 A hA, Submodule.comap_map_eq, Submodule.ker_mkQ,
    sup_eq_left.mpr]
  rw [← fixedSpace_comp_map]
  exact pairLine_le_fixedSpace f A

theorem RestrictionInput.fixedSpace_finrank
    (h24 : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (h6 : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (octadPointwiseKernel O)) = 6) :
    Module.finrank (ZMod 2) (fixedSpace (quotientRepresentation f) K) = 5 := by
  have hk : m22PairLine.mkQ.ker ≤
      fixedSpace cocodeRepresentation (octadPointwiseKernel O) := by
    rw [Submodule.ker_mkQ, ← h.kernel_image, ← fixedSpace_comp_map]
    exact pairLine_le_fixedSpace f K
  have hd := HexadTransfer.finrank_map_add_ker m22PairLine.mkQ _ hk
  rw [Submodule.ker_mkQ, finrank_m22PairLine, h6,
    ← h.kernel_image, ← h.fixedSpace_eq_map h24 K le_rfl] at hd
  exact Nat.add_right_cancel hd

theorem RestrictionInput.noncyclic_fixedSpace
    (h24 : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (hA24 : ∀ A : Subgroup M24, A ≤ octadPointwiseKernel O → ¬ IsCyclic A →
      fixedSpace cocodeRepresentation A = fixedSpace cocodeRepresentation (octadPointwiseKernel O))
    (A : Subgroup G) (hA : A ≤ K) (hnc : ¬ IsCyclic A) :
    fixedSpace (quotientRepresentation f) A = fixedSpace (quotientRepresentation f) K := by
  rw [h.fixedSpace_eq_map h24 A hA, h.fixedSpace_eq_map h24 K le_rfl, h.kernel_image]
  congr 1
  apply hA24
  · rw [← h.kernel_image]
    exact Subgroup.map_mono hA
  · intro hc
    let := hc
    apply hnc
    exact isCyclic_of_injective
      (A.equivMapOfInjective (m22PairStabilizer.subtype.comp f)
        (Subtype.val_injective.comp h.injective)).toMonoidHom
      (A.equivMapOfInjective (m22PairStabilizer.subtype.comp f)
        (Subtype.val_injective.comp h.injective)).injective

theorem RestrictionInput.fixedSpaceSpan_eq_map
    (h24 : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4) :
    fixedSpaceSpan (quotientRepresentation f) K =
      (fixedSpaceSpan cocodeRepresentation (octadPointwiseKernel O)).map m22PairLine.mkQ := by
  have he := HexadTransfer.fixedSpaceSpan_map_eq_of_element_codim
    (ambientRepresentation f) (quotientRepresentation f) m22PairLine.mkQ
    m22PairLine.mkQ_surjective (fun _ _ => rfl) K
    (by rw [Submodule.ker_mkQ]; exact pairLine_le_fixedSpace f K) (h.element_codim_eq h24)
  rw [← he]
  congr 1
  have ht := fixedSpaceSpan_map_equivariant (ambientRepresentation f) cocodeRepresentation
    (m22PairStabilizer.subtype.comp f) (Subtype.val_injective.comp h.injective)
    (LinearEquiv.refl (ZMod 2) Cocode) (fun _ _ => rfl) K
  simpa only [LinearEquiv.refl_toLinearMap, Submodule.map_id, h.kernel_image] using ht

theorem RestrictionInput.xi_hyperplane
    (h24 : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (hxi : Module.finrank (ZMod 2)
      (Cocode ⧸ fixedSpaceSpan cocodeRepresentation (octadPointwiseKernel O)) = 1)
    (hK : K ≠ ⊥) :
    Module.finrank (ZMod 2) (M22Cocode ⧸ fixedSpaceSpan (quotientRepresentation f) K) = 1 := by
  obtain hbot | ⟨a, ha, ha1⟩ := K.bot_or_exists_ne_one
  · exact (hK hbot).elim
  have hk : m22PairLine.mkQ.ker ≤ fixedSpaceSpan (ambientRepresentation f) K := by
    rw [Submodule.ker_mkQ]
    intro v hv
    apply fixedSpace_le_fixedSpaceSpan (ambientRepresentation f) ha ha1
    exact (mem_fixedSpace_zpowers_iff _ a v).mpr (pairLine_le_fixedSpace f K hv ⟨a, ha⟩)
  have hm := HexadTransfer.fixedSpaceSpan_map_eq_of_element_codim
    (ambientRepresentation f) (quotientRepresentation f) m22PairLine.mkQ
    m22PairLine.mkQ_surjective (fun _ _ => rfl) K
    (by rw [Submodule.ker_mkQ]; exact pairLine_le_fixedSpace f K) (h.element_codim_eq h24)
  have he : fixedSpaceSpan (ambientRepresentation f) K =
      fixedSpaceSpan cocodeRepresentation (octadPointwiseKernel O) := by
    have ht := fixedSpaceSpan_map_equivariant (ambientRepresentation f) cocodeRepresentation
      (m22PairStabilizer.subtype.comp f) (Subtype.val_injective.comp h.injective)
      (LinearEquiv.refl (ZMod 2) Cocode) (fun _ _ => rfl) K
    simpa only [LinearEquiv.refl_toLinearMap, Submodule.map_id, h.kernel_image] using ht
  have hd := HexadTransfer.finrank_map_add_ker m22PairLine.mkQ _ hk
  rw [hm, Submodule.ker_mkQ, finrank_m22PairLine, he] at hd
  have hdim := (fixedSpaceSpan cocodeRepresentation (octadPointwiseKernel O)).finrank_quotient_add_finrank
  rw [hxi, finrank_cocode] at hdim
  have hdim' := (fixedSpaceSpan (quotientRepresentation f) K).finrank_quotient_add_finrank
  rw [finrank_m22Cocode] at hdim'
  have hten : Module.finrank (ZMod 2)
      (fixedSpaceSpan cocodeRepresentation (octadPointwiseKernel O)) = 10 :=
    Nat.add_left_cancel hdim
  rw [hten] at hd
  have hnine : Module.finrank (ZMod 2) (fixedSpaceSpan (quotientRepresentation f) K) = 9 :=
    Nat.add_right_cancel hd
  rw [hnine] at hdim'
  exact Nat.add_right_cancel hdim'

end MathieuCode.Hexad

module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Octad.Geometry
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Dynamics

/-!
# H.15.2 octad fixed spaces and quotient dynamics

The intrinsic octad kernel fixes exactly the geometric six-space, as does
every noncyclic subgroup. Its nonidentity fixed spaces span the parity
hyperplane, and its quotient action consists of every transvection with that
axis. A genuine group equivalence with the additive axis intertwines native
stabilizer conjugation. The marked M23 kernel and action are transported
through the actual point-stabilizer embedding. Native code calculations and
cyclic duality discharge the codimension-four premise. Earlier conditional
interfaces remain available with their original statements.

These endpoints prove the fixed-space and transvection family of H.15.2;
other clauses and the complete source-theorem assembly remain with the parent.
Source: Aschbacher--Smith, H.15.2(2,4--6), printed pp.398--399.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode MathieuCode.CocodeOctad Representation.BinaryOffender

/-- A nonidentity cyclic octad-kernel element of codimension four has the
seven-dimensional fixed space required by H.15.2(5). -/
theorem octadKernel_cyclic_fixedSpace_finrank (O : Octad) (z : octadKernel O)
    (hcodim : fixedCodim cocodeRepresentation (Subgroup.zpowers z.val) = 4) :
    Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation (Subgroup.zpowers z.val)) = 7 := by
  exact MathieuCode.CocodeOctad.finrank_fixedSpace_of_fixedCodim O z hcodim

/-- The pair-space/fixed-space comparison after the common fixed-space rank is
provided by the native involution calculation. -/
theorem octadPairSpace_eq_fixedSpace_of_finrank (O : Octad) (A : Subgroup M24)
    (hU : octadPairSpace O ≤ fixedSpace cocodeRepresentation A)
    (hF : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation A) = 6) :
    fixedSpace cocodeRepresentation A = octadPairSpace O := by
  exact MathieuCode.CocodeOctad.octadPairSpace_eq_fixedSpace_of_finrank O A hU hF

/-- H.15.2(5), conditional on the common fixed-space rank supplied by the
noncyclic subgroup calculation. -/
theorem octad_noncyclic_fixedSpace_eq (O : Octad) (A : Subgroup M24)
    (hA : A ≤ octadKernel O) (hnc : ¬ IsCyclic A)
    (hU : octadPairSpace O ≤ fixedSpace cocodeRepresentation A)
    (hF : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation A) = 6) :
    fixedSpace cocodeRepresentation A = octadPairSpace O := by
  exact MathieuCode.CocodeOctad.fixedSpace_eq_octadPairSpace_of_noncyclic O A hA hnc hU hF

/-- H.15.2(5--6), span assembly from the cyclic centralizer bounds and the
independent pair-rank identity. -/
theorem octad_fixedSpaceSpan_eq_hyperplane_of_pair
    (O : Octad) (K : Subgroup M24) (hK : K ≤ octadStabilizer O)
    (hcentral : ∀ a ∈ K, a ≠ 1 →
      fixedSpace cocodeRepresentation (Subgroup.zpowers a) ≤ octadHyperplane O)
    {a b : M24} (ha : a ∈ K) (ha1 : a ≠ 1)
    (hb : b ∈ K) (hb1 : b ≠ 1)
    (hd : Module.finrank (ZMod 2) (octadHyperplane O) +
        Module.finrank (ZMod 2)
          ↥(fixedSpace cocodeRepresentation (Subgroup.zpowers a) ⊓
            fixedSpace cocodeRepresentation (Subgroup.zpowers b)) =
      Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (Subgroup.zpowers a)) +
        Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (Subgroup.zpowers b))) :
    fixedSpaceSpan cocodeRepresentation K = octadHyperplane O := by
  exact MathieuCode.CocodeOctad.fixedSpaceSpan_eq_octadHyperplane_of_pair O K hK
    hcentral ha ha1 hb hb1 hd

/-- The M23 fixed-space-span transfer, retained at the chapter endpoint. -/
theorem m23_octad_fixedSpaceSpan_eq_native (O : Octad)
    (hO : (0 : Fin 24) ∈ O.val) :
    fixedSpaceSpan m23CocodeRepresentation (m23OctadKernel O) =
      fixedSpaceSpan cocodeRepresentation (octadKernel O) :=
  m23_octad_fixedSpaceSpan_eq O hO

lemma octadKernel_eq_pointwise (O : Octad) : octadKernel O = octadPointwiseKernel O :=
  octad_core_map_eq_pointwise O

/-- The geometric six-space is exactly the fixed space of the intrinsic two-core. -/
theorem octadPairSpace_eq_fixedSpace (O : Octad) :
    octadPairSpace O = fixedSpace cocodeRepresentation (octadKernel O) := by
  rw [octadKernel_eq_pointwise]
  exact (Dynamics.octad_fixedSpace O).symm

/-- H.15.2(5): every noncyclic subgroup has the same six-dimensional fixed space. -/
theorem octad_noncyclic_fixedSpace_eq_pairSpace (O : Octad) (A : Subgroup M24)
    (hA : A ≤ octadKernel O) (hnc : ¬ IsCyclic A) :
    fixedSpace cocodeRepresentation A = octadPairSpace O := by
  rw [octadKernel_eq_pointwise] at hA
  exact Dynamics.octad_noncyclic_fixedSpace O A hA hnc

/-- H.15.2(4): the full fixed-space span is the actual octad-parity hyperplane. -/
theorem octad_fixedSpaceSpan_eq_hyperplane (O : Octad) :
    fixedSpaceSpan cocodeRepresentation (octadKernel O) = octadHyperplane O := by
  rw [octadKernel_eq_pointwise]
  exact Dynamics.octad_fixedSpaceSpan O

/-- Native code fixed dimensions and cyclic duality discharge the rank premise. -/
theorem octadKernel_cyclic_fixedCodim_native (O : Octad) (z : octadKernel O) (hz : z.val ≠ 1) :
    fixedCodim cocodeRepresentation (Subgroup.zpowers z.val) = 4 :=
  Dynamics.cyclic_fixedCodim O z.val (octadKernel_eq_pointwise O ▸ z.property) hz

theorem octadKernel_cyclic_fixedSpace_finrank_native (O : Octad) (z : octadKernel O)
    (hz : z.val ≠ 1) :
    Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (Subgroup.zpowers z.val)) = 7 :=
  Dynamics.cyclic_finrank O z.val (octadKernel_eq_pointwise O ▸ z.property) hz

def octadKernelPointwiseEquiv (O : Octad) : octadKernel O ≃* octadPointwiseKernel O :=
  MulEquiv.subgroupCongr (octadKernel_eq_pointwise O)

/-- H.15.2(6), on the intrinsic kernel and literal geometric quotient axis. -/
def octadTransvectionEquiv (O : Octad) : octadKernel O ≃* Multiplicative (Dynamics.Axis O) :=
  (octadKernelPointwiseEquiv O).trans (Dynamics.octadTransvectionEquiv O)

def octadKernelConjugate (O : Octad) (g : octadStabilizer O) (a : octadKernel O) : octadKernel O :=
  (octadKernelPointwiseEquiv O).symm
    (Dynamics.kernelConjugate O g (octadKernelPointwiseEquiv O a))

lemma octadKernelConjugate_coe (O : Octad) (g : octadStabilizer O) (a : octadKernel O) :
    (octadKernelConjugate O g a).val = g.val * a.val * g.val⁻¹ := rfl

theorem octadTransvectionEquiv_action (O : Octad) (a : octadKernel O) (v : Cocode) :
    (supportedPairSpace O.val).mkQ (cocodeRepresentation a.val v) =
      (supportedPairSpace O.val).mkQ v + octadParity O v • (octadTransvectionEquiv O a).toAdd.val :=
  Dynamics.octadTransvectionEquiv_action O (octadKernelPointwiseEquiv O a) v

theorem octadTransvectionEquiv_conjugation (O : Octad) (g : octadStabilizer O) (a : octadKernel O) :
    (octadTransvectionEquiv O (octadKernelConjugate O g a)).toAdd.val =
      Dynamics.quotientRepresentation O g (octadTransvectionEquiv O a).toAdd.val := by
  exact Dynamics.octadTransvectionEquiv_conjugation O g (octadKernelPointwiseEquiv O a)

def octadKernelActingElement (O : Octad) (a : octadKernel O) : octadStabilizer O :=
  ⟨a.val, Dynamics.kernel_le_stabilizer O (octadKernel_eq_pointwise O ▸ a.property)⟩

theorem octadTransvectionEquiv_action_quotient (O : Octad) (a : octadKernel O)
    (x : Cocode ⧸ supportedPairSpace O.val) :
    Dynamics.quotientRepresentation O (octadKernelActingElement O a) x =
      x + quotientOctadParity O x • (octadTransvectionEquiv O a).toAdd.val := by
  obtain ⟨v, rfl⟩ := (supportedPairSpace O.val).mkQ_surjective x
  exact octadTransvectionEquiv_action O a v

theorem octad_full_transvection_image (O : Octad) :
    Set.range (fun a : octadKernel O =>
      Dynamics.quotientRepresentation O (octadKernelActingElement O a)) =
    Set.range (fun x : Dynamics.Axis O => quotientTransvection O x.val) := by
  have he (a : octadKernel O) :
      Dynamics.quotientRepresentation O (octadKernelActingElement O a) =
        quotientTransvection O (octadTransvectionEquiv O a).toAdd.val := by
    apply LinearMap.ext
    exact octadTransvectionEquiv_action_quotient O a
  ext f
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(octadTransvectionEquiv O a).toAdd, (he a).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨a, ha⟩ := (octadTransvectionEquiv O).surjective (Multiplicative.ofAdd x)
    refine ⟨a, ?_⟩
    change Dynamics.quotientRepresentation O (octadKernelActingElement O a) = _
    rw [he, ha]
    rfl

/-- The M23 marking is retained: the fixed point belongs to the octad. -/
theorem m23_octad_fixedSpace_eq_pairSpace (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    fixedSpace m23CocodeRepresentation (m23OctadKernel O) = octadPairSpace O := by
  rw [m23_octad_fixedSpace_eq O hO, ← octadPairSpace_eq_fixedSpace]

theorem m23_octad_fixedSpaceSpan_eq_hyperplane (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    fixedSpaceSpan m23CocodeRepresentation (m23OctadKernel O) = octadHyperplane O := by
  rw [m23_octad_fixedSpaceSpan_eq O hO, octad_fixedSpaceSpan_eq_hyperplane]

theorem m23_octad_noncyclic_fixedSpace_eq_pairSpace (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (A : Subgroup M23) (hA : A ≤ m23OctadKernel O) (hnc : ¬ IsCyclic A) :
    fixedSpace m23CocodeRepresentation A = octadPairSpace O := by
  have hmap : A.map pointEmbedding ≤ octadKernel O := by
    rw [← m23OctadKernel_map O hO]
    exact Subgroup.map_mono hA
  have hnc' : ¬ IsCyclic (A.map pointEmbedding) := by
    intro h
    let := h
    let e := A.equivMapOfInjective pointEmbedding pointEmbedding_injective
    exact hnc (isCyclic_of_injective e.toMonoidHom e.injective)
  rw [m23CocodeRepresentation, fixedSpace_comp_map]
  exact octad_noncyclic_fixedSpace_eq_pairSpace O _ hmap hnc'

def m23OctadKernelEquiv (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    m23OctadKernel O ≃* octadKernel O :=
  ((m23OctadKernel O).equivMapOfInjective pointEmbedding pointEmbedding_injective).trans
    (MulEquiv.subgroupCongr (m23OctadKernel_map O hO))

lemma m23OctadKernelEquiv_coe (O : Octad) (hO : (0 : Fin 24) ∈ O.val) (a : m23OctadKernel O) :
    (m23OctadKernelEquiv O hO a).val = pointEmbedding a.val := rfl

def m23OctadTransvectionEquiv (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    m23OctadKernel O ≃* Multiplicative (Dynamics.Axis O) :=
  (m23OctadKernelEquiv O hO).trans (octadTransvectionEquiv O)

def m23OctadStabilizer (O : Octad) : Subgroup M23 := (octadStabilizer O).comap pointEmbedding

def m23OctadStabilizerMap (O : Octad) : m23OctadStabilizer O →* octadStabilizer O :=
  pointEmbedding.restrict (fun _ h => h)

abbrev m23OctadQuotientRepresentation (O : Octad) :
    Representation (ZMod 2) (m23OctadStabilizer O) (Cocode ⧸ supportedPairSpace O.val) :=
  (Dynamics.quotientRepresentation O).comp (m23OctadStabilizerMap O)

def m23OctadKernelConjugate (O : Octad) (g : m23OctadStabilizer O) (a : m23OctadKernel O) :
    m23OctadKernel O :=
  ⟨g.val * a.val * g.val⁻¹, by
    change pointEmbedding (g.val * a.val * g.val⁻¹) ∈ octadKernel O
    rw [octadKernel_eq_pointwise, map_mul, map_mul, map_inv]
    exact (Dynamics.kernelConjugate O (m23OctadStabilizerMap O g)
      ⟨pointEmbedding a.val, octadKernel_eq_pointwise O ▸ a.property⟩).property⟩

lemma m23OctadKernelEquiv_conjugate (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : m23OctadStabilizer O) (a : m23OctadKernel O) :
    m23OctadKernelEquiv O hO (m23OctadKernelConjugate O g a) =
      octadKernelConjugate O (m23OctadStabilizerMap O g) (m23OctadKernelEquiv O hO a) := by
  apply Subtype.ext
  change pointEmbedding (g.val * a.val * g.val⁻¹) =
    pointEmbedding g.val * pointEmbedding a.val * (pointEmbedding g.val)⁻¹
  rw [map_mul, map_mul, map_inv]

theorem m23OctadTransvectionEquiv_action (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (a : m23OctadKernel O) (v : Cocode) :
    (supportedPairSpace O.val).mkQ (m23CocodeRepresentation a.val v) =
      (supportedPairSpace O.val).mkQ v + octadParity O v • (m23OctadTransvectionEquiv O hO a).toAdd.val :=
  octadTransvectionEquiv_action O (m23OctadKernelEquiv O hO a) v

theorem m23OctadTransvectionEquiv_conjugation (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (g : m23OctadStabilizer O) (a : m23OctadKernel O) :
    (m23OctadTransvectionEquiv O hO (m23OctadKernelConjugate O g a)).toAdd.val =
      m23OctadQuotientRepresentation O g (m23OctadTransvectionEquiv O hO a).toAdd.val := by
  change (octadTransvectionEquiv O
    (m23OctadKernelEquiv O hO (m23OctadKernelConjugate O g a))).toAdd.val = _
  rw [m23OctadKernelEquiv_conjugate, octadTransvectionEquiv_conjugation]
  rfl

def m23OctadKernelActingElement (O : Octad) (a : m23OctadKernel O) : m23OctadStabilizer O :=
  ⟨a.val, Dynamics.kernel_le_stabilizer O (octadKernel_eq_pointwise O ▸ a.property)⟩

theorem m23OctadTransvectionEquiv_action_quotient (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (a : m23OctadKernel O) (x : Cocode ⧸ supportedPairSpace O.val) :
    m23OctadQuotientRepresentation O (m23OctadKernelActingElement O a) x =
      x + quotientOctadParity O x • (m23OctadTransvectionEquiv O hO a).toAdd.val := by
  obtain ⟨v, rfl⟩ := (supportedPairSpace O.val).mkQ_surjective x
  exact m23OctadTransvectionEquiv_action O hO a v

theorem m23_octad_full_transvection_image (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    Set.range (fun a : m23OctadKernel O =>
      m23OctadQuotientRepresentation O (m23OctadKernelActingElement O a)) =
    Set.range (fun x : Dynamics.Axis O => quotientTransvection O x.val) := by
  have he (a : m23OctadKernel O) :
      m23OctadQuotientRepresentation O (m23OctadKernelActingElement O a) =
        quotientTransvection O (m23OctadTransvectionEquiv O hO a).toAdd.val := by
    apply LinearMap.ext
    exact m23OctadTransvectionEquiv_action_quotient O hO a
  ext f
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(m23OctadTransvectionEquiv O hO a).toAdd, (he a).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨a, ha⟩ := (m23OctadTransvectionEquiv O hO).surjective (Multiplicative.ofAdd x)
    refine ⟨a, ?_⟩
    change m23OctadQuotientRepresentation O (m23OctadKernelActingElement O a) = _
    rw [he, ha]
    rfl

theorem m23OctadKernel_cyclic_fixedCodim_native (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (a : m23OctadKernel O) (ha : a.val ≠ 1) :
    fixedCodim m23CocodeRepresentation (Subgroup.zpowers a.val) = 4 := by
  have hn : pointEmbedding a.val ≠ 1 := fun h =>
    ha (pointEmbedding_injective (h.trans (map_one pointEmbedding).symm))
  have h := octadKernel_cyclic_fixedCodim_native O (m23OctadKernelEquiv O hO a) hn
  unfold fixedCodim
  rw [m23CocodeRepresentation, fixedSpace_comp_map, MonoidHom.map_zpowers]
  exact h

end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal

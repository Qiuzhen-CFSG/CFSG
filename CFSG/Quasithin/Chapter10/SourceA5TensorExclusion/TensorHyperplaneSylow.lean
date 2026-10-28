module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Normalizer
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Intrinsic
public import Theory.Representation.BinaryConjugationSection.DisplacementPreimage
public import Theory.GroupTheory.SylowLocalCore

/-!
# Sylow stabilizers in the original tensor coordinates

The coordinates identify N_{L₀}(U) with the full preimage of the matrix
stabilizer of its image W. The original index hypothesis makes T ∩ N_M(U)
Sylow in N_M(U); restriction to its normal subgroup N_{L₀}(U) and the
surjective coordinate quotient therefore produce a Sylow of the matrix
stabilizer with every element lifted inside T ∩ N_G(U).

Consequently the fixed-space calculation for every matrix-stabilizer Sylow
transfers to C_V(T ∩ N_G(U)) ≤ U on the original full module. The independent
hyperplane geometry remains the explicit input to this last application.
Source: Aschbacher–Smith, original 9.2.3, printed p.730, using 9.1.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Literal setwise stabilization agrees under the faithful full-module coordinates. -/
theorem quotient_mem_subspaceStabilizer_iff (U : Subgroup G) (hU : U ≤ D.fullModule)
    (l : localOrbit T L) :
    m.quotient l ∈ subspaceStabilizer Binary.action (m.sectionData.imageSpace U) ↔
      (l : G) ∈ normalizer (U : Set G) := by
  have hm (v : D.fullModule) :
      (m.sectionData.coordinates v).toAdd ∈ m.sectionData.imageSpace U ↔ (v : G) ∈ U := by
    simpa only [sup_bot_eq] using m.sectionData.coordinates_mem_imageSpace_iff U hU v
  have ha (v : D.fullModule) :
      Binary.action (m.quotient l) (m.sectionData.coordinates v).toAdd ∈
        m.sectionData.imageSpace U ↔ (l : G) * v * (l : G)⁻¹ ∈ U := by
    change (sourceA5TensorAction m.quotient) l (m.sectionData.coordinates v).toAdd ∈
      m.sectionData.imageSpace U ↔ _
    rw [← m.sectionData.equivariant l v]
    exact hm _
  constructor
  · intro hg
    apply mem_normalizer_iff.mpr
    intro v
    constructor
    · intro hv
      exact (ha ⟨v,hU hv⟩).mp ((hg _).mpr ((hm ⟨v,hU hv⟩).mpr hv))
    · intro hv
      have hvV : v ∈ D.fullModule :=
        (mem_normalizer_iff.mp (m.sectionData.normalized l.property) v).mpr (hU hv)
      exact (hm ⟨v,hvV⟩).mp ((hg _).mp ((ha ⟨v,hvV⟩).mpr hv))
  · intro hn v
    obtain ⟨x,hx⟩ := m.sectionData.onto (Multiplicative.ofAdd v)
    have hx' : (m.sectionData.coordinates x).toAdd = v := congrArg Multiplicative.toAdd hx
    rw [← hx', ha x, hm x]
    exact (mem_normalizer_iff.mp hn x).symm

/-- The matrix stabilizer has a Sylow whose elements lift into the prescribed original Sylow intersection. -/
theorem exists_hyperplane_stabilizer_sylow_lifts (U : Subgroup G)
    (hU : U ≤ D.fullModule)
    (hindex : ¬ 2 ∣ (T : Subgroup G).relIndex (D.maximalLocal ⊓ normalizer (U : Set G))) :
    ∃ S : Sylow 2 (subspaceStabilizer Binary.action (m.sectionData.imageSpace U)),
      ∀ g ∈ (S : Subgroup (subspaceStabilizer Binary.action (m.sectionData.imageSpace U))).map
          (subspaceStabilizer Binary.action (m.sectionData.imageSpace U)).subtype,
        ∃ l : localOrbit T L, (l : G) ∈ (T : Subgroup G) ⊓ normalizer (U : Set G) ∧
          m.quotient l = g := by
  let N := D.maximalLocal ⊓ normalizer (U : Set G)
  let K := localOrbit T L ⊓ normalizer (U : Set G)
  let B := subspaceStabilizer Binary.action (m.sectionData.imageSpace U)
  let P : Sylow 2 N := (T.isPGroup'.comap_subtype :
    IsPGroup 2 ((T : Subgroup G).subgroupOf N)).toSylow hindex
  have hKN : K ≤ N := inf_le_inf_right _ (localOrbit T L).le_normalizer
  have hnK : N ≤ normalizer (K : Set G) :=
    (le_inf (show N ≤ normalizer (localOrbit T L : Set G) from inf_le_left)
      (inf_le_right.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_inf_of_normalizes hKN hnK
  have hQT : (Q : Subgroup K).map K.subtype ≤
      (T : Subgroup G) ⊓ normalizer (U : Set G) := by
    rw [hQ]
    have hPT : (P : Subgroup N).map N.subtype ≤ (T : Subgroup G) := by
      change ((T : Subgroup G).subgroupOf N).map N.subtype ≤ _
      exact map_comap_le _ _
    exact le_inf (inf_le_left.trans hPT) (inf_le_right.trans inf_le_right)
  let q₀ : K →* Binary.G := m.quotient.comp (inclusion (show K ≤ localOrbit T L from inf_le_left))
  have hq₀ (k : K) : q₀ k ∈ B :=
    (m.quotient_mem_subspaceStabilizer_iff U hU ⟨k,k.property.1⟩).mpr k.property.2
  let q : K →* B := q₀.codRestrict B hq₀
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨l,hl⟩ := m.onto b.val
    have hn : (l : G) ∈ normalizer (U : Set G) :=
      (m.quotient_mem_subspaceStabilizer_iff U hU l).mp (hl ▸ b.property)
    refine ⟨⟨l,l.property,hn⟩,?_⟩
    exact Subtype.ext hl
  refine ⟨Q.mapSurjective hq,?_⟩
  rintro g ⟨b,⟨k,hk,rfl⟩,rfl⟩
  exact ⟨⟨k,k.property.1⟩,hQT (mem_map_of_mem K.subtype hk),rfl⟩

/-- Apply the matrix Sylow fixed-space bound to the original tensor subgroup. -/
theorem fullModule_centralizer_le_of_stabilizer_sylow_fixed (U : Subgroup G)
    (hU : U ≤ D.fullModule)
    (hindex : ¬ 2 ∣ (T : Subgroup G).relIndex (D.maximalLocal ⊓ normalizer (U : Set G)))
    (hfix : ∀ S : Sylow 2 (subspaceStabilizer Binary.action (m.sectionData.imageSpace U)),
      fixedSpace Binary.action
        ((S : Subgroup (subspaceStabilizer Binary.action (m.sectionData.imageSpace U))).map
          (subspaceStabilizer Binary.action (m.sectionData.imageSpace U)).subtype) ≤
        m.sectionData.imageSpace U) :
    D.fullModule ⊓ centralizer ((T : Subgroup G) ⊓ normalizer (U : Set G) : Set G) ≤ U := by
  obtain ⟨S,hS⟩ := m.exists_hyperplane_stabilizer_sylow_lifts U hU hindex
  rintro v ⟨hv,hvc⟩
  have hw : (m.sectionData.coordinates ⟨v,hv⟩).toAdd ∈ m.sectionData.imageSpace U := by
    apply hfix S
    intro a
    obtain ⟨l,hl,he⟩ := hS a a.property
    have hconj : (⟨(l : G)*v*(l : G)⁻¹,
      (mem_normalizer_iff.mp (m.sectionData.normalized l.property) v).mp hv⟩ : D.fullModule) = ⟨v,hv⟩ := by
      apply Subtype.ext
      change (l : G)*v*(l : G)⁻¹ = v
      rw [hvc l hl,mul_inv_cancel_right]
    have h := m.sectionData.equivariant l ⟨v,hv⟩
    rw [hconj] at h
    change _ = Binary.action (m.quotient l) _ at h
    change Binary.action a.val (m.sectionData.coordinates ⟨v,hv⟩).toAdd = _
    simpa only [he] using h.symm
  have hh := (m.sectionData.coordinates_mem_imageSpace_iff U hU ⟨v,hv⟩).mp hw
  simpa only [sup_bot_eq] using hh

end CFSG.Quasithin.Chapter10.SourceA5TensorModel

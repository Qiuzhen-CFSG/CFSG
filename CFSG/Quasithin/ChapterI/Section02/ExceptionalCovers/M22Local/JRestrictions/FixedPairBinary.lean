module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary.Recognition
public import Theory.Alternating.theorem_5_2_1_2
public import Theory.Representation.BinaryPermutation.SixCoreExtension

/-!
# The binary residual at the fixed native pair

In the six-letter augmentation core, the displacements of two vectors by the
pentad images of (012) and (013) sum to the constant vector. Both original
cubics fix labels 4 and 5. A section of the literal hexad quotient therefore
lifts them into the stabilizer of that native incident pair. The radical fixes
the same pair pointwise. The two resulting commutators lie in the two-residual,
since the actors have order dividing three. Their product is the central vector.

Native two-transitivity transports this pair to {0,4}, with one lifted
conjugator for the hexad and pair preimages. The resulting hexad contains
{0,4}; it is not the original standard hexad, which is disjoint from that pair.
The pair two-core is never identified with the hexad pointwise kernel.

`Recognition` retains an actual section, a radical isomorphism, the ambient
center line and the precise pentad marking `GLS3.Chapter5.outerHom` of the
native quotient labels. Its section is an actual complement by
`hexadSection_isComplement`. Recognition remains an input to this conditional
calculation, to be discharged by the binary-hexad source assembly. In
particular, an arbitrary unmarked identification with a permutation core does
not supply this input.

Source: Aschbacher–Smith, I.2.2(6a), printed pp.410 and 412 / PDF pp.421
and 423, combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairBinary
open BinaryPermutation Equiv GLS3.Chapter5
/-- The actor of the actual six-point hexad quotient. -/
abbrev A := alternatingGroup (Fin 6)
private def a : A := ⟨swap 0 1 * swap 1 2, by simp [Perm.mem_alternatingGroup]⟩
private def b : A := ⟨swap 0 1 * swap 1 3, by simp [Perm.mem_alternatingGroup]⟩
private def v : core (Fin 6) := ⟨![1,0,1,0,0,0], by rw [mem_core]; decide⟩
private def w : core (Fin 6) := ⟨![1,0,1,1,1,0], by rw [mem_core]; decide⟩
private theorem cubic : a ^ 3 = 1 ∧ b ^ 3 = 1 := by decide +kernel
private theorem fixes : a.val 4 = 4 ∧ a.val 5 = 5 ∧ b.val 4 = 4 ∧ b.val 5 = 5 := by
  decide +kernel
private theorem displacement : coreRepresentation (Fin 6) (outerHom a.val) v - v +
    (coreRepresentation (Fin 6) (outerHom b.val) w - w) =
      SixCoreExtension.constant := by
  apply Subtype.ext
  funext i
  fin_cases i <;> decide +kernel

variable {K : Type*} [Group K]
private theorem cubic_commutator (X : Subgroup K) (g r : K)
    (hg : g ∈ X) (hr : r ∈ X) (hc : g ^ 3 = 1) :
    g * r * g⁻¹ * r⁻¹ ∈ (pResidual 2 X).map X.subtype := by
  let x : X := ⟨g, hg⟩
  let y : X := ⟨r, hr⟩
  have hx : x ∈ pResidual 2 X := mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one (show x ^ 3 = 1 from Subtype.ext hc)))
  have h := (pResidual 2 X).mul_mem hx
    ((inferInstance : (pResidual 2 X).Normal).conj_mem x⁻¹
      ((pResidual 2 X).inv_mem hx) y)
  exact ⟨x * (y * x⁻¹ * y⁻¹), h, by simp [x, y, mul_assoc]⟩

/-- The input is an actual section and radical coordinates with the pentad marking.
It contains no residual assertion. The six-point quotient retains its native labels. -/
structure Recognition (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) where
  sectionMap : A →* hexadPreimage e B
  section_eq : ∀ g, hexadSixMap e hB (sectionMap g) = g
  coordinates : hexadRadical e B ≃* Multiplicative (core (Fin 6))
  equivariant : ∀ g r, (coordinates (hexadConjugation e B (sectionMap g) r)).toAdd =
    coreRepresentation (Fin 6) (outerHom g.val) (coordinates r).toAdd
  center_eq : ∀ r, r.val ∈ center K ↔
    (coordinates r).toAdd.val ∈ constants (Fin 6)

/-- The two native hexad points with labels 4 and 5. -/
noncomputable def incidentPair {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Finset (Fin 22) := {((m22HexadLabels hB).symm 4).val, ((m22HexadLabels hB).symm 5).val}

private theorem fix_pair {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) (g : M22)
    (h4 : g • ((m22HexadLabels hB).symm 4).val = ((m22HexadLabels hB).symm 4).val)
    (h5 : g • ((m22HexadLabels hB).symm 5).val = ((m22HexadLabels hB).symm 5).val) :
    g ∈ MulAction.stabilizer M22 (incidentPair hB) := by
  change g • incidentPair hB = incidentPair hB
  simp only [incidentPair, Finset.smul_finset_insert, Finset.smul_finset_singleton, h4, h5]

private theorem radical_pair {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (e : (K ⧸ center K) ≃* M22) :
    hexadRadical e B ≤ preimage e (MulAction.stabilizer M22 (incidentPair hB)) := by
  intro r hr
  apply fix_pair hB
  · exact (mem_m22HexadPointwiseKernel B (projection e r)).mp hr _
      ((m22HexadLabels hB).symm 4).property
  · exact (mem_m22HexadPointwiseKernel B (projection e r)).mp hr _
      ((m22HexadLabels hB).symm 5).property

private theorem section_pair {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (e : (K ⧸ center K) ≃* M22) (rec : Recognition e hB) (g : A)
    (h4 : g.val 4 = 4) (h5 : g.val 5 = 5) :
    (rec.sectionMap g).val ∈ preimage e (MulAction.stabilizer M22 (incidentPair hB)) := by
  have he : m22HexadAction hB
      (localProjection e (MulAction.stabilizer M22 B) (rec.sectionMap g)) = g.val := by
    exact congrArg Subtype.val (rec.section_eq g)
  have hf (i : Fin 6) (hi : g.val i = i) :
      projection e (rec.sectionMap g).val • ((m22HexadLabels hB).symm i).val =
        ((m22HexadLabels hB).symm i).val := by
    have hh := m22HexadAction_apply hB
      (localProjection e (MulAction.stabilizer M22 B) (rec.sectionMap g))
      ((m22HexadLabels hB).symm i)
    rw [he, Equiv.apply_symm_apply, hi] at hh
    have hh' : m22SetAction B
        (localProjection e (MulAction.stabilizer M22 B) (rec.sectionMap g))
        ((m22HexadLabels hB).symm i) = (m22HexadLabels hB).symm i :=
      (m22HexadLabels hB).injective (by simpa only [Equiv.apply_symm_apply] using hh.symm)
    exact congrArg Subtype.val hh'
  exact fix_pair hB _ (hf 4 h4) (hf 5 h5)

/-- The pentad-marked incident intersection contains the constant line in its residual. -/
theorem incident_residual (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) (rec : Recognition e hB) :
    center K ≤ (pResidual 2
      (hexadPreimage e B ⊓ preimage e (MulAction.stabilizer M22 (incidentPair hB)) : Subgroup K)).map
        (hexadPreimage e B ⊓ preimage e (MulAction.stabilizer M22 (incidentPair hB))).subtype := by
  let X := hexadPreimage e B ⊓ preimage e (MulAction.stabilizer M22 (incidentPair hB))
  let N := (pResidual 2 X).map X.subtype
  let E := rec.coordinates
  let r := E.symm (Multiplicative.ofAdd v)
  let t := E.symm (Multiplicative.ofAdd w)
  let d (g : A) (u : hexadRadical e B) := hexadConjugation e B (rec.sectionMap g) u * u⁻¹
  have hd (g : A) (u : hexadRadical e B) :
      (E (d g u)).toAdd = coreRepresentation (Fin 6) (outerHom g.val) (E u).toAdd -
        (E u).toAdd := by
    simp only [d, map_mul, map_inv, toAdd_mul, toAdd_inv]
    rw [rec.equivariant, sub_eq_add_neg]
  have hN (g : A) (u : hexadRadical e B) (hg : g ^ 3 = 1)
      (h4 : g.val 4 = 4) (h5 : g.val 5 = 5) : (d g u).val ∈ N := by
    exact cubic_commutator X (rec.sectionMap g).val u.val
      ⟨(rec.sectionMap g).property, section_pair hB e rec g h4 h5⟩
      ⟨hexadRadical_le e B u.property, radical_pair hB e u.property⟩
      (by change ((rec.sectionMap g) ^ 3).val = 1; rw [← map_pow, hg, map_one]; rfl)
  have hprod : (d a r * d b t).val ∈ N := N.mul_mem
    (hN a r cubic.1 fixes.1 fixes.2.1) (hN b t cubic.2 fixes.2.2.1 fixes.2.2.2)
  have hcoord : E (d a r * d b t) = Multiplicative.ofAdd SixCoreExtension.constant := by
    apply Multiplicative.toAdd.injective
    rw [map_mul]
    change (E (d a r)).toAdd + (E (d b t)).toAdd = _
    rw [hd, hd]
    simpa only [r, t, MulEquiv.apply_symm_apply, toAdd_ofAdd] using displacement
  intro z hz
  let zR : hexadRadical e B := ⟨z, center_le_hexadRadical e B hz⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((rec.center_eq zR).mp hz)
  have hcases : c = 0 ∨ c = 1 := by
    have all : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
    exact all c
  rcases hcases with rfl | rfl
  · have hzero : E zR = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      change (E zR).toAdd.val = 0
      simpa only [zero_smul] using hc.symm
    have hz1 : z = 1 := congrArg Subtype.val (E.injective (hzero.trans (map_one E).symm))
    rw [hz1]
    exact N.one_mem
  · have hone : E zR = Multiplicative.ofAdd SixCoreExtension.constant := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      have hc' : (E zR).toAdd.val = allOne (Fin 6) := by
        simpa only [one_smul] using hc.symm
      rw [hc']
      funext i
      fin_cases i <;> rfl
    have hzprod : z = (d a r * d b t).val := congrArg Subtype.val (E.injective (hone.trans hcoord.symm))
    rw [hzprod]
    exact hprod

/-- The pair selected by the calculation really has two distinct native points. -/
theorem incidentPair_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (incidentPair hB).card = 2 := by
  apply Finset.card_pair
  intro h
  have hs : (m22HexadLabels hB).symm 4 = (m22HexadLabels hB).symm 5 := Subtype.ext h
  have hf := (m22HexadLabels hB).symm.injective hs
  exact (by decide : (4 : Fin 6) ≠ 5) hf

/-- The chosen relative position is incident, with the literal pair contained in B. -/
theorem incidentPair_subset {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    incidentPair hB ⊆ B := by
  intro x hx
  simp only [incidentPair, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ((m22HexadLabels hB).symm 4).property
  · exact ((m22HexadLabels hB).symm 5).property

variable [Finite K]

/-- The fixed native pair admits an incident hexad whose lifted intersection
contains the ambient center in its two-residual. Only the explicitly marked
binary recognition remains an input. -/
theorem fixed_pair_incident_residual (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) (rec : Recognition e hB) :
    ∃ C ∈ m22Blocks, m22DisjointPair04 ⊆ C ∧
      center K ≤ (pResidual 2
        (hexadPreimage e C ⊓ preimage e m22DisjointPairStabilizer : Subgroup K)).map
          (hexadPreimage e C ⊓ preimage e m22DisjointPairStabilizer).subtype := by
  rcases Finset.card_eq_two.mp (incidentPair_card hB) with ⟨x, y, hxy, hpair⟩
  obtain ⟨g, hgx, hgy⟩ := (MulAction.is_two_pretransitive_iff.mp m22_isTwoPretransitive)
    hxy (by decide : (0 : Fin 22) ≠ 4)
  have hg : g • incidentPair hB = m22DisjointPair04 := by
    rw [hpair, Finset.smul_finset_insert, Finset.smul_finset_singleton, hgx, hgy]
    rfl
  obtain ⟨k, rfl⟩ := projection_surjective e g
  have hJ : preimage e m22DisjointPairStabilizer =
      (preimage e (MulAction.stabilizer M22 (incidentPair hB))).map
        (MulAut.conj k).toMonoidHom := by
    rw [m22DisjointPairStabilizer, ← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      preimage_map_conj]
  have hI : hexadPreimage e (projection e k • B) =
      (hexadPreimage e B).map (MulAut.conj k).toMonoidHom := by
    rw [hexadPreimage, MulAction.stabilizer_smul_eq_stabilizer_map_conj, preimage_map_conj]
    rfl
  have hX : hexadPreimage e (projection e k • B) ⊓ preimage e m22DisjointPairStabilizer =
      (hexadPreimage e B ⊓ preimage e (MulAction.stabilizer M22 (incidentPair hB))).map
        (MulAut.conj k).toMonoidHom := by
    rw [hI, hJ, map_inf _ _ _ (MulAut.conj k).injective]
  refine ⟨projection e k • B, m22_smul_block_mem _ _ hB, ?_, ?_⟩
  · rw [← hg]
    exact Finset.smul_finset_subset_smul_finset (incidentPair_subset hB)
  · rw [hX]
    exact center_le_residual_conjugate _ k (incident_residual e hB rec)

/-- The exact fixed-pair input consumed by sourceJ_residual_of_fixed_pair.
The binary-hexad source assembly must discharge the recognition premise. -/
theorem fixed_pair_residual (e : (K ⧸ center K) ≃* M22)
    (rec : Recognition e m22Hexad123_mem) :
    ∃ B ∈ m22Blocks,
      center K ≤ (pResidual 2
        (hexadPreimage e B ⊓ preimage e m22DisjointPairStabilizer : Subgroup K)).map
          (hexadPreimage e B ⊓ preimage e m22DisjointPairStabilizer).subtype := by
  obtain ⟨B, hB, _, hz⟩ := fixed_pair_incident_residual e m22Hexad123_mem rec
  exact ⟨B, hB, hz⟩

/-- Apply the existing arbitrary-J transport to this calculation. This discharges
its fixed-pair premise; compatible binary recognition remains explicit. -/
theorem sourceJ_residual (e : (K ⧸ center K) ≃* M22)
    (rec : Recognition e m22Hexad123_mem)
    (H : Subgroup M22) (hH : IsSourceJ H) :
    center K ≤ (pResidual 2 (preimage e H)).map (preimage e H).subtype :=
  (sourceJ_residual_of_fixed_pair e H hH (fixed_pair_residual e rec)).2

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairBinary

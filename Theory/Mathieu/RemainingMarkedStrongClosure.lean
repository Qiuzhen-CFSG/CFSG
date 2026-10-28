module

public import Theory.SpecificGroups.EvenCharacteristic.InvolutionFusion
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion
public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Fusion
public import Theory.Mathieu.M23.Properties.PointStabilizer
public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions

/-!
# Marked returning conjugates in M₂₂, M₂₃ and M₂₄

The actual pair-plane embedding of PSL₃(4) in M₂₃ supplies noncommuting
involutions in a two-subgroup. Conjugating a fixed point to point 9 factors
this embedding through the literal M₂₂ point stabilizer. The actual M₂₃
point-stabilizer embedding then supplies the M₂₄ pair.

In M₂₂ and M₂₃ the existing involution-fusion theorems identify the marked
class. In M₂₄ the embedded involutions have a fixed point, so belong to 2A;
the actual Sylow-central marker also belongs to 2A. Sylow conjugacy places
each pair in the supplied Sylow subgroup without changing its marked class.

Source: Aschbacher--Smith 1.1.5(3)(f), pp.501--503, and the Bender inspection
in Proposition 2.2.2, pp.519--520 (combined 1 March 2004 manuscript).
-/

public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu

private theorem pair_of_psl3Four_embedding
    {K : Type*} [Group K] [Finite K]
    (f : Matrix.PSL3Four.PSL →* K) (hf : Function.Injective f)
    (R : Sylow 2 K) (v : K)
    (hclass : ∀ x : Matrix.PSL3Four.PSL, orderOf x = 2 → IsConj v (f x)) :
    ∃ a b : R, IsConj v (a : K) ∧ IsConj v (b : K) ∧ ¬Commute a b := by
  let P : Sylow 2 Matrix.PSL3Four.PSL := Classical.choice inferInstance
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Theory.GroupTheory.EvenCharacteristicInvolutionFusion.psl3_sylow_noncommuting_involutions
      Matrix.PSL3Four.F (n := 2) (by decide)
      (by simpa using Matrix.PSL3Four.card_F) P
  have ha' : orderOf (a : Matrix.PSL3Four.PSL) = 2 := by
    simpa only [Subgroup.orderOf_coe] using ha
  have hb' : orderOf (b : Matrix.PSL3Four.PSL) = 2 := by
    simpa only [Subgroup.orderOf_coe] using hb
  obtain ⟨Q, hQ⟩ := (P.isPGroup'.map f).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q R
  let j : Matrix.PSL3Four.PSL →* K := (MulAut.conj g).toMonoidHom.comp f
  have hj : Function.Injective j := (MulAut.conj g).injective.comp hf
  have hjP : (P : Subgroup Matrix.PSL3Four.PSL).map j ≤ (R : Subgroup K) := by
    rintro _ ⟨x, hx, rfl⟩
    change (MulAut.conj g) (f x) ∈ (R : Subgroup K)
    rw [← hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hQ (mem_map_of_mem f hx))
  have hconj (x : Matrix.PSL3Four.PSL) (hx : orderOf x = 2) : IsConj v (j x) :=
    (hclass x hx).trans (isConj_iff.mpr ⟨g, rfl⟩)
  refine ⟨⟨j a, hjP (mem_map_of_mem j a.property)⟩,
    ⟨j b, hjP (mem_map_of_mem j b.property)⟩, hconj a ha', hconj b hb', ?_⟩
  intro hcomm
  apply hab
  have hh := hcomm.map (R : Subgroup K).subtype
  change Commute (j (a : Matrix.PSL3Four.PSL)) (j (b : Matrix.PSL3Four.PSL)) at hh
  exact Subtype.ext (Commute.of_map hj hh).eq

private theorem exists_psl3Four_m22_embedding :
    ∃ f : Matrix.PSL3Four.PSL →* M22, Function.Injective f := by
  let f := M23Geometry.PairPlane.pslToM23
  have hfix (x : Matrix.PSL3Four.PSL) :
      f x • M23Geometry.label 5 = M23Geometry.label 5 :=
    ((M23Geometry.mem_pointwisePairStabilizer
      (M23Geometry.PairPlane.pointwiseEquiv.symm x).val).mp
        (M23Geometry.PairPlane.pointwiseEquiv.symm x).property).1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M23 (M23Geometry.label 5) (9 : Fin 23)
  let j : Matrix.PSL3Four.PSL →* M23 := (MulAut.conj g).toMonoidHom.comp f
  have hj : Function.Injective j :=
    (MulAut.conj g).injective.comp M23Geometry.PairPlane.pslToM23_injective
  have hjfix (x : Matrix.PSL3Four.PSL) : j x ∈ MulAction.stabilizer M23 (9 : Fin 23) := by
    rw [MulAction.mem_stabilizer_iff]
    change (g * f x * g⁻¹) • (9 : Fin 23) = (9 : Fin 23)
    rw [← hg, mul_smul, mul_smul, inv_smul_smul, hfix]
  let j' := j.codRestrict (MulAction.stabilizer M23 (9 : Fin 23)) hjfix
  have hj' : Function.Injective j' := by
    intro x y hxy
    exact hj (congrArg Subtype.val hxy)
  exact ⟨m23EquivM22PointStabilizer.symm.toMonoidHom.comp j',
    m23EquivM22PointStabilizer.symm.injective.comp hj'⟩

/-- Every M₂₂ involution has noncommuting conjugates in every supplied Sylow
two-subgroup, obtained from the genuine pair-plane embedding of PSL₃(4). -/
theorem m22_sylow_noncommuting_conjugates (R : Sylow 2 M22)
    (v : M22) (ho : orderOf v = 2) :
    ∃ a b : R, IsConj v (a : M22) ∧ IsConj v (b : M22) ∧ ¬Commute a b := by
  obtain ⟨f, hf⟩ := exists_psl3Four_m22_embedding
  exact pair_of_psl3Four_embedding f hf R v (fun x hx =>
    m22_involutions_isConj v (f x) ho ((orderOf_injective f hf x).trans hx))

/-- Every M₂₃ involution has noncommuting conjugates in every supplied Sylow
two-subgroup, using the actual pair-plane embedding and proved fusion. -/
theorem m23_sylow_noncommuting_conjugates (R : Sylow 2 M23)
    (v : M23) (ho : orderOf v = 2) :
    ∃ a b : R, IsConj v (a : M23) ∧ IsConj v (b : M23) ∧ ¬Commute a b := by
  let f := M23Geometry.PairPlane.pslToM23
  have hf : Function.Injective f := M23Geometry.PairPlane.pslToM23_injective
  exact pair_of_psl3Four_embedding f hf R v (fun x hx =>
    M23Geometry.involutions_isConj v (f x) ho ((orderOf_injective f hf x).trans hx))

/-- Every two-central M₂₄ marker has noncommuting conjugates in its supplied
Sylow subgroup. Both the embedded pair and the marker are proved to lie in 2A. -/
theorem m24_sylow_noncommuting_conjugates (R : Sylow 2 M24)
    (v : M24) (hv : v ∈ R) (ho : orderOf v = 2)
    (hc : ∀ x ∈ R, Commute v x) :
    ∃ a b : R, IsConj v (a : M24) ∧ IsConj v (b : M24) ∧ ¬Commute a b := by
  let f23 : M23 →* M24 :=
    (MulAction.stabilizer M24 (24 : Fin 24)).subtype.comp m23ToM24PointStabilizer
  have hf23 : Function.Injective f23 :=
    (MulAction.stabilizer M24 (24 : Fin 24)).subtype_injective.comp
      m23ToM24PointStabilizer_injective
  let f : Matrix.PSL3Four.PSL →* M24 := f23.comp M23Geometry.PairPlane.pslToM23
  have hf : Function.Injective f := hf23.comp M23Geometry.PairPlane.pslToM23_injective
  have hmarker : IsConj M24InvolutionCentralizers.involution2A v :=
    M24ChapterHStabilizers.sylowCentral_class2A
      ⟨ho, R, hv, fun x hx => mem_centralizer_singleton_iff.mpr (hc x hx).symm.eq⟩
  apply pair_of_psl3Four_embedding f hf R v
  intro x hx
  have hfx : orderOf (f x) = 2 := (orderOf_injective f hf x).trans hx
  rcases M24InvolutionCentralizers.involution_classes (f x) hfx with hA | hB
  · exact hmarker.symm.trans hA
  · have hp : (24 : Fin 24) ∈ M24ChapterHStabilizers.fixedPoints (f x) := by
      apply (M24ChapterHStabilizers.mem_fixedPoints _ _).mpr
      exact MulAction.mem_stabilizer_iff.mp
        (m23ToM24PointStabilizer (M23Geometry.PairPlane.pslToM23 x)).property
    rw [M24ChapterHStabilizers.class2B_fixed_empty hB] at hp
    exact (Finset.notMem_empty _ hp).elim

end Sporadic.Mathieu

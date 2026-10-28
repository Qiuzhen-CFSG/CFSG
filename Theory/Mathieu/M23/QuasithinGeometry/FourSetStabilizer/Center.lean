module

public import Theory.Mathieu.M23.QuasithinGeometry.FourSetStabilizer.Basic
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore


/-!
# Center of the four-group inverse image in M23

The concrete inverse image contains the self-centralizing elementary abelian
heptad kernel, so its center lies in that kernel. The split heptad stabilizer
then identifies central kernel elements with the common fixed elements of the
two double transpositions. Evaluation at the complementary point 0 identifies
those elements with the common fixed complementary points of their certified
lifts, namely 0, 10, 16 and 22.

The two lifts are words in the certified alternating-section generators; their
label actions and the four common fixed points are checked in the Lean kernel.
No identification of the inverse image with a two-core is needed here.

Source: the M23 local configuration used by Aschbacher–Smith, Proposition 1.3.4,
printed p.511 (PDF p.528 of `refs/quasithin.pdf`), and GLS3, Table 5.3d;
the heptad geometry is that of Aschbacher–Smith §5.2, printed p.655.
-/

open Subgroup Equiv
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.FourSetStabilizer
open AlternatingSection

private def firstAlt : alternatingGroup (Fin 7) := r * r * r * c * r * c * r * r * r
private def secondAlt : alternatingGroup (Fin 7) := r * r * c * r⁻¹ * c * r⁻¹ * c * r * r
private theorem firstAlt_val : (firstAlt : Perm (Fin 7)) = firstDoubleSwap := by decide +kernel
private theorem secondAlt_val : (secondAlt : Perm (Fin 7)) = secondDoubleSwap := by decide +kernel
private def firstPerm : Perm (Fin 23) :=
  rotationLift * rotationLift * rotationLift * cycleLift * rotationLift * cycleLift *
    rotationLift * rotationLift * rotationLift
private def secondPerm : Perm (Fin 23) :=
  rotationLift * rotationLift * cycleLift * rotationLift⁻¹ * cycleLift * rotationLift⁻¹ *
    cycleLift * rotationLift * rotationLift
private theorem first_perm : ((s firstAlt : M23) : Perm (Fin 23)) = firstPerm := by
  simp only [firstAlt, map_mul, Subgroup.coe_mul, s_r_perm, s_c_perm, firstPerm]
private theorem second_perm : ((s secondAlt : M23) : Perm (Fin 23)) = secondPerm := by
  simp only [secondAlt, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
    s_r_perm, s_c_perm, secondPerm]
private theorem common_fixed : ∀ q : Fin 23, q ∉ omega →
    (firstPerm q = q ∧ secondPerm q = q ↔ q ∈ ({0, 10, 16, 22} : Finset (Fin 23))) := by
  decide +kernel

private noncomputable def intoHeptad : coreCandidate →* heptadStabilizer :=
  (inclusion fourStabilizer_le).comp coreCandidate.subtype

private theorem intoHeptad_injective : Function.Injective intoHeptad := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun g : heptadStabilizer => (g : M23)) h

private noncomputable def kernelIntoCore : heptadKernel →* coreCandidate where
  toFun u :=
    let hu : (u : heptadStabilizer).val ∈ heptadKernelAmbient :=
      ⟨u.val, u.property, rfl⟩
    ⟨⟨u.val.val, heptadKernelAmbient_le_fourStabilizer hu⟩,
      heptadKernel_le_coreCandidate hu⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem intoHeptad_kernel (u : heptadKernel) :
    intoHeptad (kernelIntoCore u) = u := rfl

private theorem central_mem_kernel (z : center coreCandidate) :
    intoHeptad z.val ∈ heptadKernel := by
  apply heptadKernel_selfCentralizing
  intro u hu
  have hc := mem_center_iff.mp z.property (kernelIntoCore ⟨u, hu⟩)
  exact congrArg intoHeptad hc

private theorem section_mem_four (a : alternatingGroup (Fin 7))
    (ha : (a : Perm (Fin 7)) ∈ labelKlein) : (s a : M23) ∈ fourStabilizer := by
  apply MulAction.mem_stabilizer_finset'.mpr
  intro q hq
  simp only [lambda, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> rw [s_label]
  all_goals
    rcases ha with ha | ha | ha | ha <;> rw [ha] <;> decide +kernel

private noncomputable def sectionIntoCore (a : alternatingGroup (Fin 7))
    (ha : (a : Perm (Fin 7)) ∈ labelKlein) : coreCandidate :=
  ⟨⟨(s a : M23), section_mem_four a ha⟩, by
    change heptadAction (s a) ∈ labelKlein
    rwa [heptadAction_s]⟩

private theorem firstAlt_mem : (firstAlt : Perm (Fin 7)) ∈ labelKlein := by
  rw [firstAlt_val, mem_labelKlein]
  exact Or.inr (Or.inl rfl)

private theorem secondAlt_mem : (secondAlt : Perm (Fin 7)) ∈ labelKlein := by
  rw [secondAlt_val, mem_labelKlein]
  exact Or.inr (Or.inr (Or.inl rfl))

private theorem klein_cases (a : alternatingGroup (Fin 7))
    (ha : (a : Perm (Fin 7)) ∈ labelKlein) :
    a = 1 ∨ a = firstAlt ∨ a = secondAlt ∨ a = firstAlt * secondAlt := by
  rcases ha with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext (h.trans firstAlt_val.symm)))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext (h.trans secondAlt_val.symm))))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by
      simpa only [Subgroup.coe_mul, firstAlt_val, secondAlt_val] using h))))

private theorem kernel_central_iff (u : heptadKernel) :
    kernelIntoCore u ∈ center coreCandidate ↔
      heptadConjugation firstAlt u = u ∧ heptadConjugation secondAlt u = u := by
  constructor
  · intro hz
    have h (a : alternatingGroup (Fin 7)) (ha : (a : Perm (Fin 7)) ∈ labelKlein) :
        heptadConjugation a u = u := by
      apply Subtype.ext
      rw [heptadConjugation_coe]
      apply (mul_inv_eq_iff_eq_mul).mpr
      exact congrArg intoHeptad (mem_center_iff.mp hz (sectionIntoCore a ha))
    exact ⟨h firstAlt firstAlt_mem, h secondAlt secondAlt_mem⟩
  · rintro ⟨hfirst, hsecond⟩
    apply mem_center_iff.mpr
    intro g
    apply intoHeptad_injective
    simp only [map_mul, intoHeptad_kernel]
    obtain ⟨w, hw⟩ := heptadSplitEquiv.surjective (intoHeptad g)
    have ha : (w.right : Perm (Fin 7)) ∈ labelKlein := by
      have hg : heptadAction (intoHeptad g) ∈ labelKlein := g.property
      rw [← hw] at hg
      change heptadAction (heptadSplitHom w) ∈ labelKlein at hg
      rwa [heptadAction_split] at hg
    have hc : heptadConjugation w.right u = u := by
      rcases klein_cases w.right ha with h | h | h | h
      · rw [h, map_one]; rfl
      · exact h.symm ▸ hfirst
      · exact h.symm ▸ hsecond
      · rw [h, map_mul, MulAut.mul_apply, hsecond, hfirst]
    have hc' : s w.right * (u : heptadStabilizer) = u * s w.right := by
      exact (mul_inv_eq_iff_eq_mul).mp
        ((heptadConjugation_coe w.right u).symm.trans (congrArg Subtype.val hc))
    have hu : (w.left : heptadStabilizer) * u = u * w.left :=
      congrArg Subtype.val (heptadKernel_mul_comm w.left u)
    rw [← hw]
    change (w.left * s w.right) * (u : heptadStabilizer) = u * (w.left * s w.right)
    rw [mul_assoc, hc', ← mul_assoc, hu, mul_assoc]

private def origin : pairComplement omega := ⟨0, by decide +kernel⟩

private noncomputable def evaluation (u : heptadKernel) : Fin 23 :=
  ((u : heptadStabilizer) : M23) • (0 : Fin 23)

private theorem evaluation_conjugation (a : alternatingGroup (Fin 7)) (u : heptadKernel) :
    evaluation (heptadConjugation a u) = (s a : M23) • evaluation u := by
  simp only [evaluation, heptadConjugation_coe, Subgroup.coe_mul, Subgroup.coe_inv,
    mul_smul]
  have hi : (s a : M23)⁻¹ • (0 : Fin 23) = 0 := by
    rw [inv_smul_eq_iff, s_zero]
  rw [hi]

private theorem conjugation_fixed_iff (a : alternatingGroup (Fin 7)) (u : heptadKernel) :
    heptadConjugation a u = u ↔ (s a : M23) • evaluation u = evaluation u := by
  rw [← evaluation_conjugation]
  exact (heptadKernel_eval_injective 0 (by decide +kernel)).eq_iff.symm

private theorem kernel_central_iff_evaluation (u : heptadKernel) :
    kernelIntoCore u ∈ center coreCandidate ↔
      evaluation u ∈ ({0, 10, 16, 22} : Finset (Fin 23)) := by
  rw [kernel_central_iff, conjugation_fixed_iff, conjugation_fixed_iff]
  change ((s firstAlt : M23) : Perm (Fin 23)) (evaluation u) = evaluation u ∧
    ((s secondAlt : M23) : Perm (Fin 23)) (evaluation u) = evaluation u ↔ _
  rw [first_perm, second_perm]
  exact common_fixed _ (Finset.mem_sdiff.mp (heptadKernel_smul_mem_complement u
    origin.property)).2

private noncomputable def centerKernel (z : center coreCandidate) : heptadKernel :=
  ⟨intoHeptad z.val, central_mem_kernel z⟩

private theorem kernel_centerKernel (z : center coreCandidate) :
    kernelIntoCore (centerKernel z) = z.val := rfl

private noncomputable def centerPoint (z : center coreCandidate) :
    ({0, 10, 16, 22} : Finset (Fin 23)) :=
  ⟨evaluation (centerKernel z), (kernel_central_iff_evaluation _).mp (by
    rw [kernel_centerKernel]
    exact z.property)⟩

private theorem centerPoint_bijective : Function.Bijective centerPoint := by
  constructor
  · intro z w h
    have he : centerKernel z = centerKernel w :=
      heptadKernel_eval_injective 0 (by decide +kernel) (congrArg Subtype.val h)
    apply Subtype.ext
    rw [← kernel_centerKernel z, ← kernel_centerKernel w, he]
  · intro q
    have hq : q.val ∈ pairComplement omega := by
      have hsub : ({0, 10, 16, 22} : Finset (Fin 23)) ⊆ pairComplement omega := by
        decide +kernel
      exact hsub q.property
    obtain ⟨u, hu⟩ := (heptadKernelEvaluation_bijective origin).surjective ⟨q.val, hq⟩
    have he : evaluation u = q.val := congrArg Subtype.val hu
    have hc : kernelIntoCore u ∈ center coreCandidate :=
      (kernel_central_iff_evaluation u).mpr (he.symm ▸ q.property)
    refine ⟨⟨kernelIntoCore u, hc⟩, ?_⟩
    apply Subtype.ext
    exact he

/-- The center of the actual four-group inverse image has order four. -/
public theorem coreCandidate_center_card : Nat.card (Subgroup.center coreCandidate) = 4 := by
  calc
    _ = Nat.card ({0, 10, 16, 22} : Finset (Fin 23)) :=
      Nat.card_congr (Equiv.ofBijective centerPoint centerPoint_bijective)
    _ = 4 := by rw [Nat.card_eq_fintype_card]; decide +kernel

end Sporadic.Mathieu.M23Geometry.FourSetStabilizer

module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.NormalForms.Centralizer.Normality
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.OrbitKernels.UnionKernel
public import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# The centralizer preimage in the Parker triality group

The quotient in Aschbacher's Lemma 14.4(2) is essential: the desired preimage
is `K ⊔ ⟨z1N⟩`, with commutators taken in `K`. Collection and `z2N ∈ Q1`
are the only two unproved presentation inputs retained by the theorem here.

Relative normality of `Q1` puts those commutators in `Q1 ∩ K = K1`.
On the two-point `k1` orbits of the union of axes, they therefore commute
pointwise. The subgroup `Q1` is transitive on that union. At the basepoint on
axis 2, its stabilizer contains `z2N` and all even cocode automorphisms.
The former excludes axis 3; perfect cocode duality restricts the image's code
to the all-ones line. There remain just the basepoint's orbit and its image
under `z1N`. Dividing by the appropriate power of `z1N` thus fixes every orbit.
The independently proved orbit kernel is `J`, whose generators lie in
`K ⊔ ⟨z1N⟩`. The reverse inclusion follows from normality of `K` and the
definition `N1 = C_N(z1N)`.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.4(2) and the axis action used
in Lemma 14.6, printed pp. 61–63. The normality input is Lemma 14.3(2).
Products act by left composition. No extraspeciality assumption is used.
-/

public section
open Atlas.Fischer Atlas.Codes
open scoped commutatorElement
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin

attribute [local instance] K_normal

private def modKCentralizer : Subgroup N :=
  (Subgroup.centralizer (Q1.map (QuotientGroup.mk' K) : Set (N ⧸ K))).comap
    (QuotientGroup.mk' K)

private theorem mem_modKCentralizer (g : N) :
    g ∈ modKCentralizer ↔ ∀ q : N, q ∈ Q1 → ⁅g,q⁆ ∈ K := by
  change (QuotientGroup.mk' K) g ∈ Subgroup.centralizer _ ↔ _
  rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
  constructor
  · intro h q hq
    have he := h _ (Subgroup.mem_map_of_mem (QuotientGroup.mk' K) hq)
    rw [← map_commutatorElement] at he
    exact (QuotientGroup.eq_one_iff _).mp he
  · intro h y hy
    obtain ⟨q,hq,hqy⟩ := hy
    rw [← hqy, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (h q hq)

private theorem z1_mem_N1 : z1N ∈ N1 :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

private theorem z1_mem_modKCentralizer : z1N ∈ modKCentralizer := by
  apply (mem_modKCentralizer _).mpr
  intro q hq
  have hc : Commute z1N q :=
    (Subgroup.mem_centralizer_singleton_iff.mp (Q1_le_N1 hq)).symm
  rw [hc.commutator_eq]
  exact K.one_mem

private theorem target_le_modKCentralizer : K ⊔ Subgroup.zpowers z1N ≤ modKCentralizer := by
  apply sup_le
  · intro k hk
    change (QuotientGroup.mk' K) k ∈ Subgroup.centralizer _
    have he : (QuotientGroup.mk' K) k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    rw [he]
    exact Subgroup.one_mem _
  · exact Subgroup.zpowers_le.mpr z1_mem_modKCentralizer

private def orbitEq (x y : Triple) : Prop := x = y ∨ x = k1.val y

private theorem orbitEq_trans {x y z : Triple} (hxy : orbitEq x y) (hyz : orbitEq y z) :
    orbitEq x z := by
  have hs (t : Triple) : k1.val (k1.val t) = t := by
    have he := congrArg (fun k : N => k.val t) k1_sq
    exact he
  rcases hxy with rfl | rfl <;> rcases hyz with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (hs _)

private theorem orbitEq_map (g : N) (hg : Commute g k1) {x y : Triple}
    (h : orbitEq x y) : orbitEq (g.val x) (g.val y) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · right
    exact congrArg (fun k : N => k.val y) hg.eq

private theorem cocode_mem_Q1 (c : Cocode) : psiAut1N (parkerCocodeStandard c) ∈ Q1 := by
  apply Subgroup.subset_closure
  exact Or.inr ⟨_, (parkerStandardProjection_eq_one_iff _).mp
    (parkerCocodeStandard_projection c), rfl⟩

private theorem cocode_even (c : Cocode) (hc : cocodeDualEquiv c golayOne = 0) :
    (parkerCocodeStandard c).val parkerOmega = parkerOmega := by
  change (golayOne, 0 + cocodeDualEquiv c golayOne) = (golayOne,0)
  rw [hc, add_zero]

private theorem even_duals_separate (a : golay)
    (ha : ∀ c : Cocode, cocodeDualEquiv c golayOne = 0 → cocodeDualEquiv c a = 0) :
    a = 0 ∨ a = golayOne := by
  have hm : a ∈ Submodule.span Bit ({golayOne} : Set golay) := by
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp
    intro f hf
    obtain ⟨c,rfl⟩ := cocodeDualEquiv.surjective f
    apply ha
    exact (Submodule.mem_dualAnnihilator _).mp hf _ (Submodule.subset_span (by simp))
  obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hm
  have hb : ∀ t : Bit, t = 0 ∨ t = 1 := by decide
  rcases hb t with rfl | rfl
  · left; simpa using ht.symm
  · right; simpa using ht.symm

private theorem Q1_transitive_axes (x : Triple) (hx : x ∈ A) :
    ∃ q : N, q ∈ Q1 ∧ q.val (axis2 loopOne) = x := by
  have hpsi (b : ParkerLoop) : psi1N b ∈ Q1 :=
    Subgroup.subset_closure (Or.inl ⟨b,rfl⟩)
  rcases hx with ⟨b,rfl⟩ | ⟨b,rfl⟩
  · refine ⟨psi1N b,hpsi b,?_⟩
    change psi1 b (axis2 loopOne) = axis2 b
    simp [loopOne, parkerLoopMultiply_one_right]
  · obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one Bit golayOne_ne_zero
    obtain ⟨c,hc⟩ := cocodeDualEquiv.surjective f
    have ho : (parkerCocodeStandard c).val parkerOmega ≠ parkerOmega := by
      intro he
      have he' := congrArg Prod.snd he
      change 0 + cocodeDualEquiv c golayOne = 0 at he'
      rw [hc, hf, zero_add] at he'
      exact one_ne_zero he'
    refine ⟨psi1N b * psiAut1N (parkerCocodeStandard c),
      Q1.mul_mem (hpsi b) (cocode_mem_Q1 c),?_⟩
    change psi1 b (psiAut1 (parkerCocodeStandard c).val (axis2 loopOne)) = axis3 b
    rw [psiAut1_axis2_odd _ ho]
    simp [loopOne, loopInverse, cocodePairing, parkerLoopMultiply_one_left]

private theorem orbitEq_axis2_sign (a : ParkerLoop) (s : ParkerBit)
    (h : orbitEq (axis2 a) (axis2 (parkerSign s a))) : s = 0 := by
  rcases h with h | h
  · have he := congrArg Prod.snd (axis2_injective h)
    change a.2 = a.2 + s at he
    exact (add_left_cancel ((add_zero a.2).trans he)).symm
  · rw [k1_axis2] at h
    have he := congrArg Prod.fst (axis2_injective h)
    change a.1 = a.1 + golayOne at he
    exact (golayOne_ne_zero (add_left_cancel (he.symm.trans (add_zero a.1).symm))).elim

private theorem not_orbitEq_axis3_sign (a : ParkerLoop) :
    ¬ orbitEq (axis3 a) (axis3 (parkerSign 1 a)) := by
  rintro (h | h)
  · exact parkerSign_one_ne a (axis3_injective h).symm
  · rw [k1_axis3] at h
    have he := congrArg Prod.fst (axis3_injective h)
    change a.1 = a.1 + golayOne at he
    exact golayOne_ne_zero (add_left_cancel (he.symm.trans (add_zero a.1).symm))

private theorem J_le_centralizer_target : J ≤ K ⊔ Subgroup.zpowers z1N := by
  apply (Subgroup.closure_le _).mpr
  have hk (i : N) (hi : i ∈ K) : i * z1N ∈ K ⊔ Subgroup.zpowers z1N :=
    Subgroup.mul_mem _ ((le_sup_left : K ≤ K ⊔ Subgroup.zpowers z1N) hi)
      ((le_sup_right : Subgroup.zpowers z1N ≤ K ⊔ Subgroup.zpowers z1N)
        (Subgroup.mem_zpowers _))
  have h2 : psi2N (parkerSign 1 parkerOmega) = k2 * z1N := by
    apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi2 (parkerSign 1 parkerOmega) (a,b,c) = k2.val (z1 (a,b,c))
    simp [k2_apply]
  have h3 : psi3N parkerOmega = k3 * z1N := by
    apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi3 parkerOmega (a,b,c) = k3.val (z1 (a,b,c))
    simp [k3_apply]
  rintro g (rfl | rfl)
  · rw [h2]; exact hk k2 ((mem_K_iff _).mpr (by simp))
  · rw [h3]; exact hk k3 ((mem_K_iff _).mpr (by simp))

variable
  (hs : Function.Surjective
    (fun x : ParkerLoop × ParkerLoop × ParkerStandardGroup => normalForm x.1 x.2.1 x.2.2))
  (hz2 : z2N ∈ Q1)

include hs hz2

private theorem presentation : OrbitPresentation where
  normalForm_bijective := ⟨normalForm_injective,hs⟩
  normalForm_mem_Q1 := normalForm_mem_Q1_iff_of_z2 hz2
  normalForm_mem_NPlus := normalForm_mem_NPlus_iff

private theorem centralizer_orbit_commute (g : N) (hg : g ∈ N1)
    (hc : g ∈ modKCentralizer) (q : N) (hq : q ∈ Q1) (x : Triple) :
    orbitEq (g.val (q.val x)) (q.val (g.val x)) := by
  have hQ : ⁅g,q⁆ ∈ Q1 := by
    have hnorm := Q1_normal_in_N1_of_collection hs hz2
    have hh := hnorm.conj_mem (⟨q,Q1_le_N1 hq⟩ : N1) hq (⟨g,hg⟩ : N1)
    exact Q1.mul_mem hh (Q1.inv_mem hq)
  have hK : ⁅g,q⁆ ∈ K := (mem_modKCentralizer g).mp hc q hq
  have he : g*q = ⁅g,q⁆ * (q*g) := by simp [commutatorElement_def, mul_assoc]
  have he' := congrArg (fun k : N => k.val x) he
  change g.val (q.val x) = (⁅g,q⁆).val (q.val (g.val x)) at he'
  rcases (mem_K_iff _).mp hK with hk | hk | hk | hk
  · left
    rw [hk] at he'
    exact he'
  · right
    exact hk ▸ he'
  · exact (k2_not_mem_Q1 (hk ▸ hQ)).elim
  · exact (k3_not_mem_Q1 (hk ▸ hQ)).elim

private theorem centralizer_fixes_orbits_of_basepoint (g : N) (hg : g ∈ N1)
    (hc : g ∈ modKCentralizer) (h0 : orbitEq (g.val (axis2 loopOne)) (axis2 loopOne)) :
    FixesK1Orbits g := by
  intro x hx
  obtain ⟨q,hq,rfl⟩ := Q1_transitive_axes x hx
  exact orbitEq_trans (centralizer_orbit_commute hs hz2 g hg hc q hq _)
    (orbitEq_map q (N1_commutes_k1 (presentation hs hz2) q (Q1_le_N1 hq)) h0)

private theorem centralizer_basepoint_axis (g : N) (hg : g ∈ N1)
    (hc : g ∈ modKCentralizer) : ∃ a, g.val (axis2 loopOne) = axis2 a := by
  have hA := N1_preserves_A (presentation hs hz2) g hg
    (show axis2 loopOne ∈ A from Or.inl ⟨_,rfl⟩)
  rcases hA with ⟨a,ha⟩ | ⟨a,ha⟩
  · exact ⟨a,ha.symm⟩
  · have hh := centralizer_orbit_commute hs hz2 g hg hc z2N hz2 (axis2 loopOne)
    have hfix : z2N.val (axis2 loopOne) = axis2 loopOne := by
      change z2 (axis2 loopOne) = _
      simp [axis2]
    rw [hfix, ← ha] at hh
    apply False.elim
    apply not_orbitEq_axis3_sign a
    change orbitEq (axis3 a) (z2 (axis3 a)) at hh
    simpa only [axis3, z2_apply, signZero_some, signZero_none] using hh

private theorem centralizer_basepoint_code (g : N) (hg : g ∈ N1)
    (hc : g ∈ modKCentralizer) (a : ParkerLoop)
    (ha : g.val (axis2 loopOne) = axis2 a) : a.1 = 0 ∨ a.1 = golayOne := by
  apply even_duals_separate
  intro c hc0
  have heven := cocode_even c hc0
  have hh := centralizer_orbit_commute hs hz2 g hg hc
    (psiAut1N (parkerCocodeStandard c)) (cocode_mem_Q1 c) (axis2 loopOne)
  have hfix : (psiAut1N (parkerCocodeStandard c)).val (axis2 loopOne) = axis2 loopOne := by
    change psiAut1 (parkerCocodeStandard c).val (axis2 loopOne) = _
    rw [psiAut1_axis2_even _ heven]
    simp [loopOne,cocodePairing]
  rw [hfix,ha] at hh
  change orbitEq (axis2 a) (psiAut1 (parkerCocodeStandard c).val (axis2 a)) at hh
  rw [psiAut1_axis2_even _ heven] at hh
  exact orbitEq_axis2_sign a (cocodeDualEquiv c a.1) hh

private theorem centralizer_basepoint (g : N) (hg : g ∈ N1)
    (hc : g ∈ modKCentralizer) : ∃ z : N, z ∈ Subgroup.zpowers z1N ∧
      orbitEq (g.val (axis2 loopOne)) (z.val (axis2 loopOne)) := by
  obtain ⟨a,ha⟩ := centralizer_basepoint_axis hs hz2 g hg hc
  have hd := centralizer_basepoint_code hs hz2 g hg hc a ha
  have hb : ∀ t : ParkerBit, t = 0 ∨ t = 1 := by decide
  have ha0 : a.1 = 0 → a = loopOne ∨ a = loopPi := by
    intro h
    rcases hb a.2 with ht | ht
    · left; exact Prod.ext h ht
    · right; exact Prod.ext h ht
  have ha1 : a.1 = golayOne → a = parkerOmega ∨ a = parkerSign 1 parkerOmega := by
    intro h
    rcases hb a.2 with ht | ht
    · left; exact Prod.ext h ht
    · right; exact Prod.ext h (by simpa [parkerSign,parkerOmega] using ht)
  rcases hd with hd | hd
  · rcases ha0 hd with rfl | rfl
    · exact ⟨1,Subgroup.one_mem _,Or.inl ha⟩
    · refine ⟨z1N,Subgroup.mem_zpowers _,Or.inl ?_⟩
      rw [ha]
      change axis2 loopPi = z1 (axis2 loopOne)
      simp [z1_axis2,loopOne,loopPi,parkerSign]
  · rcases ha1 hd with rfl | rfl
    · refine ⟨1,Subgroup.one_mem _,Or.inr ?_⟩
      rw [ha]
      change axis2 parkerOmega = k1.val (axis2 loopOne)
      rw [k1_axis2]
      simp [loopOne,parkerLoopMultiply_one_left]
    · refine ⟨z1N,Subgroup.mem_zpowers _,Or.inr ?_⟩
      rw [ha]
      change axis2 (parkerSign 1 parkerOmega) = k1.val (z1 (axis2 loopOne))
      rw [z1_axis2,k1_axis2,parkerLoopMultiply_sign_left]
      simp [loopOne,parkerLoopMultiply_one_left]

/-- The preimage in `N1` of the centralizer of the image of `Q1` in `N/K`.
The only presentation inputs are collection and membership of `z2N` in `Q1`. -/
theorem centralizer_preimage_of_collection (g : N) (hg : g ∈ N1) :
    (∀ q : N, q ∈ Q1 → ⁅g,q⁆ ∈ K) ↔ g ∈ K ⊔ Subgroup.zpowers z1N := by
  rw [← mem_modKCentralizer]
  constructor
  · intro hc
    obtain ⟨z,hz,h0⟩ := centralizer_basepoint hs hz2 g hg hc
    have hzN : z ∈ N1 := (Subgroup.zpowers_le.mpr z1_mem_N1) hz
    have hzC : z ∈ modKCentralizer :=
      (Subgroup.zpowers_le.mpr z1_mem_modKCentralizer) hz
    have huN : z⁻¹*g ∈ N1 := N1.mul_mem (N1.inv_mem hzN) hg
    have huC : z⁻¹*g ∈ modKCentralizer :=
      modKCentralizer.mul_mem (modKCentralizer.inv_mem hzC) hc
    have hu0 : orbitEq ((z⁻¹*g).val (axis2 loopOne)) (axis2 loopOne) := by
      have hh := orbitEq_map z⁻¹
        (N1_commutes_k1 (presentation hs hz2) z⁻¹ (N1.inv_mem hzN)) h0
      change orbitEq (z.val.symm (g.val (axis2 loopOne)))
        (z.val.symm (z.val (axis2 loopOne))) at hh
      change orbitEq (z.val.symm (g.val (axis2 loopOne))) (axis2 loopOne)
      simpa only [Equiv.symm_apply_apply] using hh
    have hJ : z⁻¹*g ∈ J :=
      (fixesK1Orbits_iff_mem_J (presentation hs hz2) _ huN).mp
        (centralizer_fixes_orbits_of_basepoint hs hz2 _ huN huC hu0)
    have hh := (K ⊔ Subgroup.zpowers z1N).mul_mem
      ((le_sup_right : Subgroup.zpowers z1N ≤ K ⊔ Subgroup.zpowers z1N) hz)
      (J_le_centralizer_target hJ)
    simpa only [mul_inv_cancel_left] using hh
  · intro h
    exact target_le_modKCentralizer h

end Sporadic.Monster.Construction.TrialitySpin

module
public import Theory.GroupAction.BinaryPlaneCubicDisplacement
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Coordinates.Decomposition

/-!
# Actual residual commutators generate the second covering plane

The full quotient centralizer P of the selected u maps onto SL₂(2) on the
other plane. Surjectivity on two-residuals lifts cubic matrices to O²(P).
Two cubic displacements of a nonzero vector span the binary plane. Equivariance
and the exact coordinate kernel Z lift this to generation by the actual
commutators [b,r] modulo Z, for the literal embedded residual in G.

Source: Aschbacher--Smith 14.6.17(5), printed p.1036.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open Chapter15.Section03 BinaryWreathPointStabilizer
attribute [local instance] orthogonalAction
attribute [local instance] FourGroupMatrixCoordinates.naturalAction
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}

/-- Commutators of any nonzero second-plane lift with the literal residual
of C_H(u mod Z) generate the entire second plane modulo Z. -/
theorem suitable_second_plane_generated
    (h : D.Hypothesis) [IsElementaryAbelian 2 D.UH]
    (o : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (i j : OrthogonalPlaneIndex) (hji : j ≠ i)
    (u : (⁅D.UH,D.H⁆ : Subgroup G))
    (hu : (u : G) ∈ o.plane i) (huz : (u : G) ∉ D.V₁)
    (b : G) (hb : b ∈ o.plane j) (hbz : b ∉ D.V₁) :
    o.plane j ≤ D.V₁ ⊔ closure {x : G | ∃ r ∈
      (pResidual 2 (h.kernel (zpowers (u : G)))).map (h.kernel (zpowers (u : G))).subtype,
      x = ⁅b,r⁆} := by
  let K := ⁅D.UH,D.H⁆
  let P := h.kernel (zpowers (u : G))
  let R := (pResidual 2 P).map P.subtype
  let J := closure {x : G | ∃ r ∈ R, x = ⁅b,r⁆}
  have hKU : K ≤ D.UH := le_normalizer_iff_commutator_le_left.mp o.normalized
  have huH := h.UH_le_H (hKU u.property)
  have hPH : P ≤ D.H := fun x hx => ((h.mem_kernel_iff (zpowers_le.mpr huH)).mp hx).1
  have hPN := suitable_kernel_normalizes_planes h o i j u hu huz
  have hu2 : (u : G)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := D.UH) (u : G) (hKU u.property)
  obtain ⟨a,ha⟩ := suitable_binary_plane_action h o i j hji u hu2 hu huz
  let e := BinaryLinear.OuterCyclic.slEquivLinear 2
  let f : P →* MatrixActor := e.symm.toMonoidHom.comp a.actor
  have hf : Function.Surjective f := e.symm.surjective.comp a.surjective
  have hfe (r : P) : f r = (o.actor ⟨r,hPH r.property⟩).left j := by
    change e.symm (a.actor r) = _
    rw [ha r (hPH r.property)]
    exact e.symm_apply_apply _
  let q : K →* Plane := (Pi.evalMonoidHom (fun _ : Index => Plane) j).comp o.coordinates
  have hker (w : K) (hw : (w : G) ∈ o.plane j) (he : q w = 1) : (w : G) ∈ D.V₁ := by
    have hs := (o.mem_plane_iff j w).mp hw
    have hz : w ∈ o.coordinates.ker := by
      change o.coordinates w = 1
      funext k
      by_cases hk : k = j
      · subst k
        exact he
      · exact hs k hk
    rwa [o.vector_kernel] at hz
  let bK : K := ⟨b,o.plane_le j hb⟩
  have hbq : q bK ≠ 1 := fun he => hbz (hker bK hb he)
  let c (r : P) : K := bK *
    ((K.normalizerMonoidHom ⟨r,normalizer_commutator_ge_right D.UH D.H (hPH r.property)⟩) bK)⁻¹
  have hc (r : P) : (c r : G) = ⁅b,(r : G)⁆ := by
    change b*((r : G)*b*(r : G)⁻¹)⁻¹ = _
    rw [commutatorElement_def]
    group
  have hcW (r : P) : (c r : G) ∈ o.plane j := by
    rw [hc]
    exact (le_normalizer_iff_commutator_le_left.mp hPN) (commutator_mem_commutator hb r.property)
  have hcq (r : P) : q (c r) = q bK * (f r • q bK)⁻¹ := by
    rw [show q (c r) = q bK *
      (o.coordinates ((K.normalizerMonoidHom
        ⟨r,normalizer_commutator_ge_right D.UH D.H (hPH r.property)⟩) bK) j)⁻¹ by
      exact q.map_mul _ _ |>.trans (congrArg (q bK * ·) (q.map_inv _))]
    have he := congrFun (o.compatible ⟨r,hPH r.property⟩ bK) j
    have hs : (o.actor ⟨r,hPH r.property⟩).right = 1 := by
      apply fixed_no_shift ((o.mem_plane_iff i u).mp hu)
      · intro hz
        have hk : u ∈ o.coordinates.ker := hz
        rw [o.vector_kernel] at hk
        exact huz hk
      · exact (o.fixed_iff_commutator_mem ⟨r,hPH r.property⟩ u).mpr
          (((h.mem_kernel_iff (zpowers_le.mpr huH)).mp r.property).2 u (mem_zpowers _))
    change _ = (o.actor ⟨r,hPH r.property⟩).left j •
      o.coordinates bK ((o.actor ⟨r,hPH r.property⟩).right⁻¹*j) at he
    rw [hs,inv_one,one_mul,←hfe] at he
    rw [he]
    rfl
  intro y hy
  let yK : K := ⟨y,o.plane_le j hy⟩
  obtain ⟨m,n,hm,hn,he⟩ := plane_cubic_displacements (q bK) hbq (q yK)
  have lift (m : MatrixActor) (hm : m^3=1) : ∃ r ∈ pResidual 2 P, f r=m := by
    have hmR : m ∈ pResidual 2 MatrixActor := mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hm))
    rw [←map_pResidual_of_surjective 2 f hf] at hmR
    exact hmR
  obtain ⟨r,hr,hrf⟩ := lift m hm
  obtain ⟨s,hs,hsf⟩ := lift n hn
  have hrJ : (c r : G) ∈ J := subset_closure ⟨r,mem_map_of_mem _ hr,hc r⟩
  have hsJ : (c s : G) ∈ J := subset_closure ⟨s,mem_map_of_mem _ hs,hc s⟩
  let z : K := yK*(c r*c s)⁻¹
  have hzW : (z : G) ∈ o.plane j := (o.plane j).mul_mem hy
    ((o.plane j).inv_mem ((o.plane j).mul_mem (hcW r) (hcW s)))
  have hzq : q z=1 := by
    rw [show q z = q yK * (q (c r)*q (c s))⁻¹ by simp only [z,map_mul,map_inv],
      hcq,hcq,hrf,hsf,he,mul_inv_cancel]
  have hzZ := hker z hzW hzq
  have hh := (D.V₁ ⊔ J).mul_mem ((le_sup_left : D.V₁ ≤ D.V₁ ⊔ J) hzZ)
    ((le_sup_right : J ≤ D.V₁ ⊔ J) (J.mul_mem hrJ hsJ))
  simpa only [z,coe_mul,coe_inv,mul_assoc,inv_mul_cancel,mul_one] using hh

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair

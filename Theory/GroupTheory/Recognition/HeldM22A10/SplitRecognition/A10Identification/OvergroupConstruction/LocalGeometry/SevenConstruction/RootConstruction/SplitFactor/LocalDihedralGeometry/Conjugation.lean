module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.RootQuotient

/-!
# Conjugating Held's root intersection into the known involution centralizer

Conjugation by tau-prime sends pi*mu to mu and uv to the inverse of v.
It therefore gives an actual equivalence from the full ambient intersection
C_G(pi*mu) ∩ C_G(uv) to C_{C_G(mu)}(v). The marked involution and root are
tracked explicitly, for the subsequent finite centralizer calculation and
central quotient. No root factor or quotient recognition is assumed.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237.
-/

open Subgroup Equiv
open Theory.GroupTheory.HeldM22A10
open Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry
open Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry

noncomputable section

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer) (L : Source.SixLocalData D e)

public abbrev intersection : Subgroup G :=
  centralizer ({pi D e * mu D e} : Set G) ⊓ rootCentralizer D e L

@[expose] public def involution : rootCentralizer D e L :=
  ⟨pi D e * mu D e, A_le_rootCentralizer D e L L.pi_mu_mem⟩

public theorem involution_order : orderOf (involution D e L) = 2 := by
  rw [← Subgroup.orderOf_coe]
  change orderOf (element D e 0 * element D e 1) = 2
  simp only [element, ← map_mul]
  rw [orderOf_injective _ (D.a10ModelEmbedding_injective e)]
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

public theorem tau'_pi_mu : (MulAut.conj (tau' D e)) (pi D e * mu D e) = mu D e := by
  have h : modelElement 4 * (modelElement 0 * modelElement 1) *
      (modelElement 4)⁻¹ = modelElement 1 := by decide +kernel
  change tau' D e * (pi D e * mu D e) * (tau' D e)⁻¹ = mu D e
  simpa only [element, map_mul, map_inv] using
    congrArg (D.a10ModelEmbedding e) h

public theorem tau'_root : (MulAut.conj (tau' D e)) (L.u * L.v) = L.v⁻¹ := by
  have hu : (MulAut.conj (tau' D e)) L.u = L.u := by
    rw [MulAut.conj_apply, L.u_tau'_commute.symm.eq, mul_inv_cancel_right]
  have hv : (MulAut.conj (tau' D e)) L.v = (L.u * L.v)⁻¹ := by
    simpa only [MulAut.conj_apply, coordinate_inv D e 4 (by decide)] using tau'_v D e L
  rw [map_mul, hu, hv, mul_inv_rev, ← mul_assoc, L.u_v_commute.inv_right.eq, mul_inv_cancel_right]

public abbrev muCentralizer : Subgroup G := centralizer ({mu D e} : Set G)
@[expose] public def vInMuCentralizer : muCentralizer D e :=
  ⟨L.v, mem_centralizer_singleton_iff.mpr L.v_mu_commute.eq⟩

@[expose] public def intersectionToMuV : intersection D e L ≃*
    centralizer ({vInMuCentralizer D e L} : Set (muCentralizer D e)) where
  toFun x := ⟨⟨(MulAut.conj (tau' D e)) x, by
    apply mem_centralizer_singleton_iff.mpr
    have hc := (show Commute (x : G) (pi D e * mu D e) from
      mem_centralizer_singleton_iff.mp x.property.1).map (MulAut.conj (tau' D e))
    rw [tau'_pi_mu] at hc
    exact hc.eq⟩, by
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    have hc := (show Commute (x : G) (L.u * L.v) from
      mem_centralizer_singleton_iff.mp x.property.2).map (MulAut.conj (tau' D e))
    rw [tau'_root D e L] at hc
    exact (Commute.inv_right_iff.mp hc).eq⟩
  invFun x := ⟨(MulAut.conj (tau' D e)).symm (x : G), by
    constructor
    · apply mem_centralizer_singleton_iff.mpr
      apply (MulAut.conj (tau' D e)).injective
      rw [map_mul, tau'_pi_mu, map_mul, tau'_pi_mu, MulEquiv.apply_symm_apply]
      exact mem_centralizer_singleton_iff.mp x.val.property
    · apply mem_centralizer_singleton_iff.mpr
      apply (MulAut.conj (tau' D e)).injective
      rw [map_mul, tau'_root, map_mul, tau'_root, MulEquiv.apply_symm_apply]
      exact (show Commute (x : G) L.v from
        congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property)).inv_right.eq⟩
  left_inv x := Subtype.ext ((MulAut.conj (tau' D e)).symm_apply_apply x)
  right_inv x := Subtype.ext (Subtype.ext ((MulAut.conj (tau' D e)).apply_symm_apply x))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul (MulAut.conj (tau' D e)) _ _))


@[expose] public def intersectionInvolution : intersection D e L :=
  ⟨pi D e * mu D e, mem_centralizer_singleton_iff.mpr rfl,
    (involution D e L).property⟩

@[expose] public def intersectionRoot : intersection D e L :=
  ⟨L.u * L.v, mem_centralizer_singleton_iff.mpr (L.root_centralizes _ L.pi_mu_mem).eq,
    (centralRoot D e L).property⟩

@[expose] public def centralMu : muCentralizer D e :=
  ⟨mu D e, mem_centralizer_singleton_iff.mpr rfl⟩

@[simp] public theorem intersectionToMuV_involution :
    ((intersectionToMuV D e L (intersectionInvolution D e L) : muCentralizer D e) : G) =
      mu D e := tau'_pi_mu D e

@[simp] public theorem intersectionToMuV_root :
    ((intersectionToMuV D e L (intersectionRoot D e L) : muCentralizer D e) : G) =
      L.v⁻¹ := tau'_root D e L

public abbrev centralizerInRoot : Subgroup (rootCentralizer D e L) :=
  centralizer ({involution D e L} : Set (rootCentralizer D e L))

@[expose] public def centralizerInRootEquiv : centralizerInRoot D e L ≃* intersection D e L where
  toFun x := ⟨x, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property)), x.val.property⟩
  invFun x := ⟨⟨x, x.property.2⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.1))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry

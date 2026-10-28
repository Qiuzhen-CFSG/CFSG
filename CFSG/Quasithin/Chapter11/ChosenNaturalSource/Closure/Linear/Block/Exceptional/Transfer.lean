module
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PCoreCentralKernelTransfer
public import Theory.GroupTheory.NormalCentralQuotientAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Action

/-!
# From the point-image kernel to the central-quotient kernel

Automorphisms fixing the center of a finite two-group and its central
quotient form a two-group. For an action whose original kernel is central
modulo O₂, its central-quotient kernel therefore maps into the two-core
of the action image. The central-kernel core-transfer theorem pulls this
back into O₂,Z of the actor. The application uses the original K and U.

The point-kernel premise of this transfer is proved in PointKernel; final
assembly discharges it using the special-structure fixed-space equality.
Source: Aschbacher--Smith 11.5.7, refs/quasithin.pdf, printed p.782.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional

/-- The central quotient kernel is central modulo the two-core whenever the
original action kernel is, provided the actor fixes the center pointwise. -/
private theorem central_quotient_kernel_transfer
    {K U : Type*} [Group K] [Group U] [Finite K] [Finite U]
    (f : K →* MulAut U) (hU : IsPGroup 2 U)
    (hz : ∀ k : K, ∀ z : center U, f k z = z)
    (hk : f.ker ≤ centralPreimage (pCore 2 K)) :
    ((quotientAut (center U)).comp f).ker ≤ centralPreimage (pCore 2 K) := by
  let a := (quotientAut (center U)).comp f
  let r := f.rangeRestrict
  have hpair : a.ker.map r ≤ (automorphismPair (center U)).ker.comap f.range.subtype := by
    rintro _ ⟨k,hk,rfl⟩
    change automorphismPair (center U) (f k) = 1
    rw [automorphismPair_apply]
    apply Prod.ext
    · apply MulEquiv.ext
      intro z
      apply Subtype.ext
      exact hz k z
    · exact hk
  have hp : IsPGroup 2 (a.ker.map r) :=
    ((isPGroup_automorphism_pair_kernel (center U) (hU.to_subgroup _)).comap_of_injective
      f.range.subtype f.range.subtype_injective).to_le hpair
  have hn : (a.ker.map r).Normal := Normal.map inferInstance r f.rangeRestrict_surjective
  have hc : a.ker.map r ≤ pCore 2 f.range := le_sSup ⟨hn,hp⟩
  have hcore : pCore 2 K ≤ (pCore 2 f.range).comap r := by
    apply map_le_iff_le_comap.mp
    exact le_sSup ⟨Normal.map inferInstance r f.rangeRestrict_surjective,
      pCore_isPGroup.map r⟩
  have hkr : r.ker.map (QuotientGroup.mk' (pCore 2 K)) ≤ center (K ⧸ pCore 2 K) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact map_le_iff_le_comap.mpr hk
  have hb := r.coreMap_ker_le_center_of_map_ker f.rangeRestrict_surjective hcore hkr
  intro k hk
  apply hb
  change QuotientGroup.mk' (pCore 2 f.range) (r k) = 1
  exact (QuotientGroup.eq_one_iff _).mpr (hc (mem_map_of_mem r hk))


open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

theorem conjugation_kernel_le_pointAction_kernel :
    (conjugation E).ker ≤ (pointAction E).ker := by
  intro k hk
  apply (mem_pointAction_kernel_iff E k).mpr
  intro u hu
  have he := congrArg (fun a : MulAut E.W => (a ⟨u,hu⟩ : G)) (MonoidHom.mem_ker.mp hk)
  change (k : G) * u * (k : G)⁻¹ = u at he
  rw [commutatorElement_def,he,mul_inv_cancel]
  exact E.V₁.one_mem

/-- Transfer from the original point-action kernel to the central-action
kernel. The only group-theoretic input here is pointwise fixation of Z(U). -/
theorem centralAction_kernel_le_of_pointAction_kernel_le
    (hUT : E.W ≤ (T : Subgroup G))
    (hz : E.K ≤ centralizer (closureCenter E : Set G))
    (hk : (pointAction E).ker ≤ centralPreimage (pCore 2 E.K)) :
    (centralAction E).ker ≤ centralPreimage (pCore 2 E.K) := by
  apply central_quotient_kernel_transfer (conjugation E) (T.isPGroup'.to_le hUT) ?_
    ((conjugation_kernel_le_pointAction_kernel E).trans hk)
  intro k z
  apply Subtype.ext
  rw [conjugation_apply]
  have hc := hz k.property (z.val : G) (mem_map_of_mem E.W.subtype z.property)
  rw [← hc,mul_inv_cancel_right]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional

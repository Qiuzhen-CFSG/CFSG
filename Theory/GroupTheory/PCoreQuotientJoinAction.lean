module

public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.PGroupCore

/-!
# The core quotient action of a normal subgroup with a p-group supplement

Let U normalize L and be a p-group. Conjugation gives an action of LU on
L/O_p(L). If this quotient is centerless, the action kernel is exactly O_p(LU).
Its intersection with L is O_p(L); its remaining quotient embeds in LU/L,
which is a p-group. Conversely, normality puts the commutators of O_p(LU)
with L inside O_p(L). The first isomorphism theorem then identifies the
literal core quotient with the action image.

This is the elementary extension argument used in Aschbacher–Smith,
combined manuscript (1 March 2004), proof of 15.4.20, printed p.1164.
Surjectivity onto the full automorphism group remains a separate obligation.
-/

@[expose] public section
open Subgroup
namespace Subgroup

variable {G : Type*} [Group G] {L U : Subgroup G}
variable (p : ℕ)

/-- The actual conjugation action on the intrinsic core quotient. -/
def pCoreJoinAction (hUL : U ≤ normalizer L) :
    (L ⊔ U : Subgroup G) →* MulAut (L ⧸ pCore p L) :=
  (quotientAut (pCore p L)).comp
    (L.normalizerMonoidHom.comp (inclusion (sup_le L.le_normalizer hUL)))

/-- Conjugation on representatives computes the quotient action. -/
theorem pCoreJoinAction_mk (hUL : U ≤ normalizer L) (g : (L ⊔ U : Subgroup G)) (l : L) :
    pCoreJoinAction p hUL g (QuotientGroup.mk' (pCore p L) l) =
      QuotientGroup.mk' (pCore p L)
        (L.normalizerMonoidHom (inclusion (sup_le L.le_normalizer hUL) g) l) :=
  quotientAut_apply_mk _ _ _

/-- Restriction to the normal factor induces its inner automorphisms. -/
theorem pCoreJoinAction_on_component (hUL : U ≤ normalizer L) (l : L) :
    pCoreJoinAction p hUL (inclusion le_sup_left l) =
      MulAut.conj (QuotientGroup.mk' (pCore p L) l) := by
  ext x
  induction x using Quotient.inductionOn with | h x =>
    rw [show (⟦x⟧ : L ⧸ pCore p L) = QuotientGroup.mk' (pCore p L) x from rfl,
      pCoreJoinAction_mk p]
    change QuotientGroup.mk' (pCore p L) (l * x * l⁻¹) = _
    simp only [map_mul, map_inv, MulAut.conj_apply]

/-- The range contains every inner automorphism of the core quotient. -/
theorem inner_le_pCoreJoinAction_range (hUL : U ≤ normalizer L) :
    MulAut.innerSubgroup (L ⧸ pCore p L) ≤ (pCoreJoinAction p hUL).range := by
  rintro a ⟨x, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore p L) x
  exact ⟨inclusion le_sup_left l, pCoreJoinAction_on_component p hUL l⟩

/-- Centerlessness identifies the kernel of the restriction to L. -/
theorem pCoreJoinAction_restrict_ker (hUL : U ≤ normalizer L)
    (hc : center (L ⧸ pCore p L) = ⊥) :
    ((pCoreJoinAction p hUL).comp (inclusion le_sup_left)).ker = pCore p L := by
  ext l
  change pCoreJoinAction p hUL (inclusion le_sup_left l) = 1 ↔ l ∈ pCore p L
  rw [pCoreJoinAction_on_component p]
  have he : MulAut.conj (QuotientGroup.mk' (pCore p L) l) = 1 ↔
      QuotientGroup.mk' (pCore p L) l ∈ center (L ⧸ pCore p L) := by
    constructor
    · intro h
      apply mem_center_iff.mpr
      intro x
      have hx := DFunLike.congr_fun h x
      change _ * x * _⁻¹ = x at hx
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm
    · intro h
      ext x
      change _ * x * _⁻¹ = x
      rw [← mem_center_iff.mp h x, mul_inv_cancel_right]
  rw [he, hc, mem_bot]
  exact QuotientGroup.eq_one_iff l

/-- Restricting the map to LU/L expresses the kernel as an extension of p-groups. -/
theorem pCoreJoinAction_kernel_isPGroup (hUL : U ≤ normalizer L) (hU : IsPGroup p U)
    (hc : center (L ⧸ pCore p L) = ⊥) : IsPGroup p (pCoreJoinAction p hUL).ker := by
  let M := L ⊔ U
  let N := L.subgroupOf M
  let _ : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le L.le_normalizer hUL)
  have hgen : N ⊔ U.subgroupOf M = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  have hquot : IsPGroup p (M ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (U.subgroupOf M) hU.comap_subtype hgen
  let f := pCoreJoinAction p hUL
  let q := (QuotientGroup.mk' N).comp f.ker.subtype
  have hqker : IsPGroup p q.ker := by
    let r : q.ker →* L :=
      (M.subtype.comp (f.ker.subtype.comp q.ker.subtype)).codRestrict L (by
        intro x
        change x.val.val ∈ N
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore p L := by
      intro x
      exact (pCoreJoinAction_restrict_ker p hUL hc).le x.val.property
    let r' : q.ker →* pCore p L := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore p L => (x.val : G)) hab
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv

/-- Normality makes the ambient core act trivially on the local core quotient. -/
theorem pCore_le_pCoreJoinAction_kernel (hUL : U ≤ normalizer L) :
    pCore p (L ⊔ U : Subgroup G) ≤ (pCoreJoinAction p hUL).ker := by
  let M := L ⊔ U
  let i : L →* M := inclusion le_sup_left
  have hcore : (pCore p M).comap i ≤ pCore p L :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective i
      (inclusion_injective le_sup_left)⟩
  intro g hg
  apply MulEquiv.ext
  intro x
  induction x using Quotient.inductionOn with | h l =>
    rw [show (⟦l⟧ : L ⧸ pCore p L) = QuotientGroup.mk' (pCore p L) l from rfl,
      pCoreJoinAction_mk p]
    let b := L.normalizerMonoidHom (inclusion (sup_le L.le_normalizer hUL) g) l
    have hb : b * l⁻¹ ∈ pCore p L := by
      apply hcore
      change i (b * l⁻¹) ∈ pCore p M
      exact (commutator_le_left (pCore p M) ⊤)
        (commutator_mem_commutator hg (mem_top (i l)))
    have he := (QuotientGroup.eq_one_iff (N := pCore p L) (b * l⁻¹)).mpr hb
    change QuotientGroup.mk' (pCore p L) (b * l⁻¹) = 1 at he
    rw [map_mul, map_inv] at he
    exact mul_inv_eq_one.mp he

/-- The exact kernel, derived from centerlessness and the p-group supplement. -/
theorem pCoreJoinAction_kernel (hUL : U ≤ normalizer L) (hU : IsPGroup p U)
    (hc : center (L ⧸ pCore p L) = ⊥) :
    (pCoreJoinAction p hUL).ker = pCore p (L ⊔ U : Subgroup G) :=
  le_antisymm (le_sSup ⟨inferInstance, pCoreJoinAction_kernel_isPGroup p hUL hU hc⟩)
    (pCore_le_pCoreJoinAction_kernel p hUL)

/-- The literal core quotient is isomorphic to the actual action image. -/
noncomputable def pCoreJoinQuotientEquivRange (hUL : U ≤ normalizer L) (hU : IsPGroup p U)
    (hc : center (L ⧸ pCore p L) = ⊥) :
    ((L ⊔ U : Subgroup G) ⧸ pCore p (L ⊔ U : Subgroup G)) ≃* (pCoreJoinAction p hUL).range :=
  (QuotientGroup.quotientMulEquivOfEq (pCoreJoinAction_kernel p hUL hU hc).symm).trans
    (QuotientGroup.quotientKerEquivRange (pCoreJoinAction p hUL))

end Subgroup

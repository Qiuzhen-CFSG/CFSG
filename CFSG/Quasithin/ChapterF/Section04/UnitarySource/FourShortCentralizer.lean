module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourLongCentralizer
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourShortTransport
public import Theory.GroupTheory.SylowKernelCore
import all CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourLongCentralizer

/-!
# The full-extension centralizer of the marked unitary short root

Every middle automorphism preserves the plane parabolic and its actual
two-core. Factor an extension automorphism fixing the marked short root
into an inner automorphism and a middle actor. The inverse inner factor
then carries that short root into the plane core, so the proved native
short-root transporter places it in the plane parabolic. This places
the whole extension centralizer in the corresponding full endpoint.

Source: Aschbacher–Smith F.4.27(4)(ii) and the model choice in F.4.42,
printed pp.288,295. The Chapter6 companion identifies this centralizer
with the original local short centralizer on the same extension marking.
The ambient short-centralizer containment remains a separate argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open GreenBook.LieModels.UnitaryFour
open UnitarySource.FourShortTransport UnitarySource.FourPlacement

/-- The marked short root has its full extension centralizer in the plane
endpoint, including all outer actors of the extension. -/
theorem FourExtension.short_root_centralizer_le (m : ℕ) (hm : 1 ≤ m)
    (E : FourExtension m hm) :
    centralizer ({E.baseHom (shortRoot m hm)} : Set E.carrier) ≤
      E.right.subgroupOf E.carrier := by
  intro a ha
  have he : a.val * MulAut.conj (shortRoot m hm) = MulAut.conj (shortRoot m hm) * a.val :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
  have hfix : a.val (shortRoot m hm) = shortRoot m hm := by
    apply four_conj_injective m hm
    rw [←aut_conjugate_inner,he,mul_inv_cancel_right]
  obtain ⟨b,k,hk,hak⟩ := E.factor a.val a.property
  have hkP : (planeParabolic m hm).map k.toMonoidHom = planeParabolic m hm := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (E.middle_preserves_right (four_conj_injective m hm) ⟨k,hk⟩ y).mpr hy
    · intro hx
      refine ⟨k.symm x,?_,k.apply_symm_apply x⟩
      exact (E.middle_preserves_right (four_conj_injective m hm) ⟨k,hk⟩ (k.symm x)).mp
        (by simpa only [k.apply_symm_apply] using hx)
  have hkQ : (planeCore m hm).map k.toMonoidHom = planeCore m hm := by
    rw [planeCore_eq_twoCore,map_pCoreIn_of_injective 2 _ k.toMonoidHom k.injective,hkP]
  have hkt : k (shortRoot m hm) ∈ planeCore m hm :=
    hkQ ▸ mem_map_of_mem k.toMonoidHom (shortRoot_mem_core m hm)
  have hfix' : b * k (shortRoot m hm) * b⁻¹ = shortRoot m hm := by
    rw [hak] at hfix
    exact hfix
  have hbinv : b⁻¹ * shortRoot m hm * (b⁻¹)⁻¹ ∈ planeCore m hm := by
    rw [←hfix']
    simpa only [inv_inv,inv_mul_cancel_left,mul_inv_cancel_right,mul_assoc,inv_mul_cancel,mul_one] using hkt
  have hb : b ∈ planeParabolic m hm :=
    inv_mem_iff.mp (conjugator_short_to_core m hm b⁻¹ hbinv)
  change a.val ∈ E.right
  rw [hak]
  exact E.right.mul_mem ((E.conj_mem_right_iff (four_conj_injective m hm) b).mpr hb) hk.2
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary

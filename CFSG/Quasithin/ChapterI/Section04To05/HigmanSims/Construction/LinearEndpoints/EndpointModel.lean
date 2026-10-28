module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PointParabolic
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PointParabolic

/-!
# Canonical model marking for a specified actual natural endpoint

This internal interface retains a previously specified endpoint and its
quotient/kernel marking. It reuses the canonical affine coordinate changes
from PointParabolic through an intentional same-package import-all edge;
no private helper appears in the public statement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G]
local notation "SL" => Representation.SL2FourNatural.SL
local notation "W" => Representation.SL2FourNatural.V

/-- The specified natural extension is the full canonical point parabolic,
with its original kernel equal to the whole two-core. -/
theorem point_parabolic_of_natural_endpoint
    (A P K : Subgroup G) (hAP : A ≤ P) (hPN : P ≤ normalizer (A : Set G))
    (q : P →* SL) (hq : Function.Surjective q) (hk : q.ker = A.subgroupOf P)
    (c : A ≃* Multiplicative W)
    (hc : ∀ (g : P) (a : A), c (A.normalizerMonoidHom (inclusion hPN g) a) =
      Multiplicative.ofAdd (Representation.SL2FourNatural.action (q g) (c a).toAdd))
    (hcomp : (A.subgroupOf P).IsComplement' (K.subgroupOf P)) :
    P.pCoreIn 2 = A ∧
      ∃ e : P ≃* Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F,
        (A.subgroupOf P).map e.toMonoidHom =
          pCore 2 (Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F) := by
  let a : q.ker ≃* A := (MulEquiv.subgroupCongr hk).trans (subgroupOfEquivOfLe hAP)
  let w := a.trans c
  have hw (g : P) (u : q.ker) :
      w (MulAut.conjNormal g u) = Matrix.SL2.naturalAction Representation.SL2FourNatural.F (q g) (w u) := by
    have he : a (MulAut.conjNormal g u) = A.normalizerMonoidHom (inclusion hPN g) (a u) := by
      apply Subtype.ext
      rfl
    change c (a (MulAut.conjNormal g u)) = _
    rw [he]
    exact hc g (a u)
  obtain ⟨f, hfq, _, _, _⟩ := exists_marked_semidirect_equiv_of_given_complement
    q hq w (Matrix.SL2.naturalAction Representation.SL2FourNatural.F) hw
    (K.subgroupOf P) (hk ▸ hcomp)
  have hfcore : pCore 2 P = q.ker := by
    apply (Subgroup.map_injective (f := f.toMonoidHom) f.injective)
    rw [pCore_map_iso, Matrix.SL2.affine_twoCore_eq]
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := f.surjective y
      refine ⟨x, ?_, rfl⟩
      change q x = 1
      exact (hfq x).symm.trans hy
    · rintro y ⟨x, hx, rfl⟩
      change (f x).right = 1
      exact (hfq x).trans hx
  have hcore : pCore 2 P = A.subgroupOf P := hfcore.trans hk
  have hambient : P.pCoreIn 2 = A := by
    change (pCore 2 P).map P.subtype = A
    rw [hcore, map_subgroupOf_eq_of_le hAP]
  let e := (f.trans standard_affine_equiv).trans canonical_point_affine_equiv.symm
  refine ⟨hambient, e, ?_⟩
  rw [← hcore, pCore_map_iso]


end CFSG.Quasithin.HigmanSims

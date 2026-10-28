module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Eliminating the ambient extension in the Janko-four case

For finite G with simple L = F*(G) and an actual equivalence L ≃ Janko4.Model,
the literal noncommuting generators make Z(L) trivial. Self-centralization
of F*(G) then makes the conjugation action on L faithful. The proved full
innerness theorem for the model forces every element of G into L.
Consequently G itself is isomorphic to the model.

This accounts for every extension allowed by E.1.14(5); neither the SQTK
hypothesis nor G = LT is needed for this reduction. It uses full innerness
from AdequateLocal, not merely the weaker outer-two-group assertion.
It asserts no E-generation bound.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
E.1.14(5), printed p.214; GLS3, Table 5.3i, Out(J4) = 1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.JankoFour

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem center_eq_bot (L : Subgroup G) [IsSimpleGroup L]
    (e : L ≃* Janko4.Model) : center L = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center L) inferInstance with h | h
  · exact h
  · have : IsMulCommutative L := center_eq_top_iff.mp h
    apply False.elim
    apply Janko4.a_mul_b_ne_b_mul_a
    have hc := congrArg e (mul_comm' (e.symm Janko4.a) (e.symm Janko4.b))
    simpa only [map_mul, e.apply_symm_apply] using hc

/-- The simple generalized Fitting subgroup has trivial ambient centralizer. -/
theorem fitting_centralizer_eq_bot (L : Subgroup G) [IsSimpleGroup L]
    (hL : generalizedFitting G = L) (e : L ≃* Janko4.Model) :
    centralizer (L : Set G) = ⊥ := by
  apply bot_unique
  intro c hc
  have hcle : centralizer (L : Set G) ≤ L :=
    hL ▸ centralizer_generalizedFitting_le G
  let l : L := ⟨c, hcle hc⟩
  have hl : l ∈ center L := by
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (hc x x.property)
  have heq : l = 1 := by simpa only [center_eq_bot L e, mem_bot] using hl
  exact congrArg Subtype.val heq

/-- Full innerness of the actual model eliminates every ambient extension. -/
theorem fitting_eq_top (L : Subgroup G) [IsSimpleGroup L]
    (hL : generalizedFitting G = L) (e : L ≃* Janko4.Model) : L = ⊤ := by
  let _ : L.Normal := hL ▸ inferInstance
  let f : G →* MulAut Janko4.Model :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := L))
  have hf : Function.Injective f := (MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot L
      (fitting_centralizer_eq_bot L hL e))
  have hi (l : L) : f l = MulAut.conj (e l) := by
    change MulAut.congr e (MulAut.conjNormal (l : G)) = _
    rw [MulAut.conjNormal_val, MulAut.congr_conj]
  apply top_unique
  intro g _
  obtain ⟨x, hx⟩ := Janko4.AdequateLocal.conj_surjective (f g)
  have hg : (e.symm x : G) = g := hf (by rw [hi, e.apply_symm_apply, hx])
  exact hg ▸ (e.symm x).property

/-- The source socle equivalence extends to an equivalence on the whole group. -/
noncomputable def ambientEquiv (L : Subgroup G) [IsSimpleGroup L]
    (hL : generalizedFitting G = L) (e : L ≃* Janko4.Model) : G ≃* Janko4.Model :=
  (Subgroup.topEquiv.symm.trans
    (MulEquiv.subgroupCongr (fitting_eq_top L hL e).symm)).trans e


end CFSG.Quasithin.ChapterE.JankoFour

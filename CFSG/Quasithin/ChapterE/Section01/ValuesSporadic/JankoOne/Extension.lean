module

public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne

/-!
# Elimination of extensions of the J₁ generalized Fitting subgroup

If F*(G) is the concrete J₁ group, every conjugation action on it is inner.
Removing an inner conjugating element leaves an element centralizing F*(G),
which lies in F*(G) by the generalized Fitting centralizer theorem. Thus
F*(G) = G. This applies to every extension in E.1.14(5); the additional
source hypotheses SQTK and G = LT are unnecessary for this reduction.

The actual automorphism calculation is reused from the narrow J₁ certificate
in Chapter 1, without importing that chapter's classification interfaces.
Source: Aschbacher--Smith, E.1.14(5), printed p.214; GLS3, Table 5.3f,
Out(J₁) = 1.
-/

public section
namespace CFSG.Quasithin.ChapterE.JankoOne
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Every finite group whose generalized Fitting subgroup is J₁ is that subgroup. -/
theorem socle_eq_top (L : Subgroup G) (hL : L = generalizedFitting G)
    (e : L ≃* Janko1.Model) : L = ⊤ := by
  have hn : L.Normal := hL ▸ inferInstance
  let := hn
  have hC : centralizer (L : Set G) ≤ L := by
    rw [hL]
    exact centralizer_generalizedFitting_le G
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨g, hg⟩ := Janko1.OuterCertificate.aut_inner
    (MulAut.congr e (MulAut.conjNormal x))
  let l : L := e.symm g
  have hl : MulAut.conj l = MulAut.conjNormal x := by
    apply (MulAut.congr e).injective
    rw [← hg]
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply, l]
  have hk : MulAut.conjNormal ((l : G)⁻¹ * x) = (1 : MulAut L) := by
    rw [map_mul, map_inv, MulAut.conjNormal_val, hl, inv_mul_cancel]
  have hc : (l : G)⁻¹ * x ∈ centralizer (L : Set G) := by
    intro y hy
    have he := congrArg (fun f : MulAut L => ((f ⟨y, hy⟩ : L) : G)) hk
    change ((l : G)⁻¹ * x) * y * ((l : G)⁻¹ * x)⁻¹ = y at he
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  have hm := L.mul_mem l.property (hC hc)
  simpa only [mul_inv_cancel_left] using hm

end CFSG.Quasithin.ChapterE.JankoOne

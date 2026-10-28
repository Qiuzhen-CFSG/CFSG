module
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.ElementaryEightParabolicRecognition
public import Theory.GroupAction.QuotientConjugation
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Full action on an elementary-eight generalized Fitting subgroup

If F*(P) is elementary abelian of order eight and its quotient has order
168, conjugation induces the full automorphism group on F*(P). The
self-centralization theorem identifies the kernel, and counting ordered
binary bases proves surjectivity. Thus the seven nonidentity elements form
one conjugacy orbit, with centralizers of order 192.

The quotient isomorphism retains the literal quotient map and conjugation
formula. This is the local action calculation required by (G2) in
Aschbacher–Smith, *The Classification of Quasithin Groups*, §I.4, printed
p.417. It does not identify the surrounding group from its local subgroups.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.GeneralizedFittingEight
variable {P : Type*} [Group P] [Finite P]
variable (V : Subgroup P) [V.Normal] [IsElementaryAbelian 2 V]
variable (hfit : V = generalizedFitting P) (hV : Nat.card V = 8)
variable (hquot : Nat.card (P ⧸ V) = 168)

omit [V.Normal] in
include hfit in
theorem centralizer_eq : centralizer (V : Set P) = V := by
  apply le_antisymm
  · rw [hfit]
    exact centralizer_generalizedFitting_le P
  · exact V.le_centralizer

include hfit in
theorem pCore_eq : pCore 2 P = V := by
  apply le_antisymm
  · exact (pCore_le_fitting P 2).trans ((fitting_le_generalizedFitting P).trans hfit.symm.le)
  · exact le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 V⟩

omit [Finite P] [V.Normal] [IsElementaryAbelian 2 V] in
include hV hquot in
theorem card_group : Nat.card P = 1344 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup V, hquot, hV]

include hfit in
theorem conjugation_kernel : (MulAut.conjNormal : P →* MulAut V).ker = V := by
  rw [MulAut.conjNormal_ker_eq_centralizer, centralizer_eq V hfit]

include hfit hV hquot in
theorem conjugation_surjective : Function.Surjective (MulAut.conjNormal : P →* MulAut V) := by
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.eq_top_of_card_eq
  rw [← Subgroup.index_ker, conjugation_kernel V hfit, Subgroup.index_eq_card,
    hquot, card_mulAut_of_elementary_eight V hV]

noncomputable def quotientConjugationEquiv : (P ⧸ V) ≃* MulAut V :=
  (QuotientGroup.quotientMulEquivOfEq (conjugation_kernel V hfit).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (conjugation_surjective V hfit hV hquot))

theorem quotientConjugationEquiv_mk (g : P) (v : V) :
    (quotientConjugationEquiv V hfit hV hquot (QuotientGroup.mk' V g) v : P) =
      g * (v : P) * g⁻¹ := rfl

include hfit hV hquot in
theorem nonidentity_conjugate (x y : V) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ g : P, g * (x : P) * g⁻¹ = (y : P) := by
  obtain ⟨a,ha⟩ := ElementaryEightParabolic.automorphism_transitive x y hx hy
  obtain ⟨g,hg⟩ := conjugation_surjective V hfit hV hquot a
  exact ⟨g, congrArg Subtype.val (show (MulAut.conjNormal g : MulAut V) x = y by rw [hg,ha])⟩

include hfit hV hquot in
theorem point_centralizer_card (x : V) (hx : x ≠ 1) :
    Nat.card (centralizer ({(x : P)} : Set P)) = 192 := by
  let f : P →* MulAut V := MulAut.conjNormal
  let : MulDistribMulAction P V := MulDistribMulAction.compHom V f
  have horbit : MulAction.orbit P x = {y : V | y ≠ 1} := by
    ext y
    constructor
    · rintro ⟨g,rfl⟩ hy
      apply hx
      exact (f g).injective (hy.trans (map_one (f g)).symm)
    · intro hy
      obtain ⟨g,hg⟩ := nonidentity_conjugate V hfit hV hquot x y hx hy
      exact ⟨g, Subtype.ext hg⟩
  have hc : Nat.card (MulAction.orbit P x) = 7 := by
    rw [horbit]
    classical
    let : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card]
    have he : Fintype.card V = 8 := by simpa only [Nat.card_eq_fintype_card] using hV
    change Fintype.card {y : V // y ≠ 1} = 7
    rw [Fintype.card_subtype_compl (fun y : V => y = 1)]
    simp [he]
  have hstab : MulAction.stabilizer P x = centralizer ({(x : P)} : Set P) := by
    ext g
    change f g x = x ↔ _
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hg
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hg)
    · intro hg
      apply Subtype.ext
      change g * (x : P) * g⁻¹ = (x : P)
      exact mul_inv_eq_iff_eq_mul.mpr hg
  have hm := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup P x)
  rw [Nat.card_prod, hc, hstab, card_group V hV hquot] at hm
  omega

end Theory.GroupTheory.GeneralizedFittingEight

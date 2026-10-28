module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Quotients

public import Theory.GroupTheory.CommutatorImageLifting

/-!
# Placement of the marked partners

The actual partner X = (U ∩ Hʸ)ʸ lies in YU when y ∈ Y. T-normality
preserves this placement under the source element t. It also preserves
membership in T ∩ K once X ≤ K has been established.

The final lemma gives a valid lift of a marked actor commutator identity,
using X ∩ Q_H = E ≤ U and a subgroup of K which actually normalizes X.
Constructing that normalizing actor, or an alternative sufficient lift,
remains part of the marked calculation. This lemma does not infer X ≤ K
merely from X* ≤ K*.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.56 and 15.3.59, printed pp.1147–1150.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
variable {G : Type*} [Group G]

/-- The literal conjugate defining X belongs to YU when its conjugator belongs to Y. -/
theorem partnerX_le_pair (Z ZS Y : Subgroup G) (y : G) (hy : y ∈ Y) :
    partnerX Z ZS y ≤ Y ⊔ closureU Z ZS := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hy' : y ∈ Y ⊔ closureU Z ZS := (le_sup_left : Y ≤ Y ⊔ closureU Z ZS) hy
  have hx' : x ∈ Y ⊔ closureU Z ZS :=
    (le_sup_right : closureU Z ZS ≤ Y ⊔ closureU Z ZS) hx.1
  exact (Y ⊔ closureU Z ZS).mul_mem
    ((Y ⊔ closureU Z ZS).mul_mem ((Y ⊔ closureU Z ZS).inv_mem hy') hx') hy'

/-- The t-conjugate partner also belongs to YU, using the two actual normalizers. -/
theorem conjugate_partnerX_le_pair (T Z ZS Y : Subgroup G) (y t : G)
    (hy : y ∈ Y) (ht : t ∈ T) (hTH : T ≤ centralizerH Z)
    (hTY : T ≤ normalizer (Y : Set G)) :
    rightConjugate (partnerX Z ZS y) t ≤ Y ⊔ closureU Z ZS := by
  have htn : t ∈ normalizer ((Y ⊔ closureU Z ZS : Subgroup G) : Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup Y (closureU Z ZS)
      ⟨hTY ht, H_normalizes_closureU Z ZS (hTH ht)⟩
  rintro _ ⟨x, hx, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  simpa only [inv_inv] using
    (mem_normalizer_iff.mp ((normalizer ((Y ⊔ closureU Z ZS : Subgroup G) : Set G)).inv_mem htn) x).mp
      (partnerX_le_pair Z ZS Y y hy hx)


variable [Finite G]
/-- Conjugation by a member of T preserves containment in the residual Sylow group. -/
theorem conjugate_le_residualSylow (T Z A : Subgroup G) (t : G)
    (ht : t ∈ T) (hTH : T ≤ centralizerH Z) (hA : A ≤ residualSylow T Z) :
    rightConjugate A t ≤ residualSylow T Z := by
  have hHK := (normal_subgroupOf_iff_le_normalizer (residual_le_H Z)).mp
    (residual_normal_in_H Z)
  have htn : t ∈ normalizer (residualSylow T Z : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨T.le_normalizer ht, hHK (hTH ht)⟩
  rintro _ ⟨a, ha, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  simpa only [inv_inv] using
    (mem_normalizer_iff.mp ((normalizer (residualSylow T Z : Set G)).inv_mem htn) a).mp (hA ha)


/-- Lift the actor commutator using an actual normalizing subgroup B ≤ K.
The required B and its action identity must be supplied by the marked calculation. -/
theorem partnerX_le_residual_of_normalized_actor_commutator (Z ZS B : Subgroup G) (y : G)
    (hXH : partnerX Z ZS y ≤ centralizerH Z)
    (hUK : closureU Z ZS ≤ residualK Z) (hBK : B ≤ residualK Z)
    (hBX : B ≤ normalizer (partnerX Z ZS y : Set G))
    (hXQ : partnerX Z ZS y ⊓ coreQ Z = intersectionE Z ZS y)
    (himage : actorImage Z (partnerX Z ZS y) =
      ⁅actorImage Z (partnerX Z ZS y), actorImage Z B⁆) :
    partnerX Z ZS y ≤ residualK Z := by
  let H := centralizerH Z
  let A := (partnerX Z ZS y).subgroupOf H
  let B' := B.subgroupOf H
  let K := (residualK Z).subgroupOf H
  let : K.Normal := residual_normal_in_H Z
  have hBK' : B' ≤ K := fun _ hb => hBK hb
  have hn : B' ≤ normalizer (A : Set H) := by
    intro b hb
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hBX hb) (x : G)
  have hk : A ⊓ (actorProjection Z).ker ≤ K := by
    intro a ha
    have haQ : (a : G) ∈ coreQ Z := (actorProjection_eq_one_iff Z a).mp ha.2
    have haE : (a : G) ∈ intersectionE Z ZS y := hXQ ▸ ⟨ha.1, haQ⟩
    exact hUK haE.1.1
  have h := le_of_commutator_image_of_normalized (actorProjection Z) A B' K hBK' hn himage hk
  intro x hx
  exact h (show (⟨x, hXH hx⟩ : H) ∈ A from hx)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration

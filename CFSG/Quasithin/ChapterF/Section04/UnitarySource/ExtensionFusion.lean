module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Models
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Counts

/-!
# Sylow placement and core normalizers in a full unitary extension

The native coset bijections make the plane endpoint have odd index in the
full extension, including all outer actors. Its Sylow subgroups are therefore
Sylow in the extension. The inner-times-middle factorization also transports
the native core normalizer exactly, once the endpoint normalizes that core.

These are the extension-side inputs to Burnside fusion and the same-carrier
Thompson comparison in Aschbacher--Smith F.4.35,43, pp.292,296.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.UnitarySource.ExtensionFusion
open SourceCompletion.UnitaryNonbinary
variable {B : Type*} [Group B] {P₀ P₁ : Subgroup B}

theorem normalizer_inner (E : SourceExtension P₀ P₁)
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (Q : Subgroup B) (hQ : normalizer (Q : Set B) = P₁)
    (hn : E.right.subgroupOf E.carrier ≤ normalizer (Q.map E.baseHom : Set E.carrier)) :
    normalizer (Q.map E.baseHom : Set E.carrier) = E.right.subgroupOf E.carrier := by
  apply le_antisymm ?_ hn
  intro a ha
  obtain ⟨b,d,hd,he⟩ := E.factor a a.property
  let dE : E.carrier := ⟨d,E.right_le hd.2⟩
  have hdN : dE ∈ normalizer (Q.map E.baseHom : Set E.carrier) := hn hd.2
  have hbN : E.baseHom b ∈ normalizer (Q.map E.baseHom : Set E.carrier) := by
    have hh := (normalizer (Q.map E.baseHom : Set E.carrier)).mul_mem ha
      ((normalizer (Q.map E.baseHom : Set E.carrier)).inv_mem hdN)
    have he' : a = E.baseHom b * dE := Subtype.ext he
    rwa [he',mul_inv_cancel_right] at hh
  have hc : (normalizer (Q.map E.baseHom : Set E.carrier)).comap E.baseHom =
      normalizer (Q : Set B) := by
    rw [comap_normalizer_eq_of_le_range (Q.map_le_range E.baseHom),
      comap_map_eq_self_of_injective (E.baseHom_injective hi)]
  have hb : b ∈ P₁ := hQ ▸ (hc ▸ hbN)
  change a.val ∈ E.right
  rw [he]
  exact E.right.mul_mem ((E.conj_mem_right_iff hi b).mpr hb) hd.2

open GreenBook.LieModels.UnitaryFour
theorem four_right_odd_index (m : ℕ) (hm : 1 ≤ m) (E : FourExtension m hm) :
    ¬ 2 ∣ (E.right.subgroupOf E.carrier).index := by
  rw [show (E.right.subgroupOf E.carrier).index = (planeParabolic m hm).index from
    E.card_coset_eq_native (four_conj_injective m hm) true]
  exact fun hh => (projectiveSylow m hm).not_dvd_index
    (hh.trans (index_dvd_of_le (projectiveSylow_le_parabolics m hm).2))

theorem four_right_sylow_index {X : Type*} [Group X] [Finite X]
    (m : ℕ) (hm : 1 ≤ m) (E : FourExtension m hm)
    (j : X →* E.carrier) (hj : Function.Injective j)
    (hr : j.range = E.right.subgroupOf E.carrier) (S : Sylow 2 X) :
    ¬ 2 ∣ ((S : Subgroup X).map j).index := by
  rw [(S : Subgroup X).index_map_of_injective hj,hr]
  exact Nat.Prime.not_dvd_mul Nat.prime_two S.not_dvd_index (four_right_odd_index m hm E)

end CFSG.Quasithin.ChapterF.UnitarySource.ExtensionFusion

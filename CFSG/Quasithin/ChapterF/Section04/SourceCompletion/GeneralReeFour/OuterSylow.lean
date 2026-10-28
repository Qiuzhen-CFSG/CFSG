module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.FullNormalizer
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ExtensionSylow

/-!
# The whole Ree overlap carries a Sylow of the full extension

The native Sylow embeds in both marked endpoints of the extension, hence
in their entire intersection. Its already proved Sylow property in the
extension makes the whole intersection have odd index. Consequently every
Sylow carried through an actual comparison with this intersection is still
Sylow in the same full extension carrier. This uses the literal inclusions
and makes no claim that the source normalizers generate the ambient group.

Source: Aschbacher–Smith F.4.29,33,38, printed pp.289,291,294.
-/

public noncomputable section
open Subgroup Theory.GroupTheory ReeF4.Parabolics
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
open GreenBook.LieModels
variable {m : ℕ} (E : GeneralReeExtension.SourceExtension m)

/-- The full overlap has odd index in the same extension carrier. -/
theorem extension_middle_index_odd (hm : 0 < m) :
    Odd (E.middle.subgroupOf E.carrier).index := by
  obtain ⟨S,hS⟩ := ReeF4.SourceCompletion.extension_sylow hm E.carrier E.contains_inner
    (ReeFour.sylow m)
  have hle : (S : Subgroup E.carrier) ≤ E.middle.subgroupOf E.carrier := by
    rw [hS]
    rintro _ ⟨x,hx,rfl⟩
    change MulAut.conj x ∈ E.left ⊓ E.right
    exact ⟨(E.conj_mem_left_iff (ReeF4.SmallCompletion.conj_injective m hm) x).mpr
      ((ReeFour.sylow_le_localFactor m .linear).trans (localFactor_le_parabolic m .linear) hx),
      (E.conj_mem_right_iff (ReeF4.SmallCompletion.conj_injective m hm) x).mpr
      ((ReeFour.sylow_le_localFactor m .suzuki).trans (localFactor_le_parabolic m .suzuki) hx)⟩
  exact Nat.not_even_iff_odd.mp (by
    rw [even_iff_two_dvd]
    exact fun hd => S.not_dvd_index (hd.trans (index_dvd_of_le hle)))

private theorem mapped_sylow {A B : Type*} [Group A] [Group B] [Finite A]
    (S : Sylow 2 A) (f : A →* B) (hf : Function.Injective f) (ho : Odd f.range.index) :
    ∃ T : Sylow 2 B, (T : Subgroup B) = (S : Subgroup A).map f := by
  have hn : ¬ 2 ∣ ((S : Subgroup A).map f).index := by
    rw [index_map_of_injective _ hf]
    exact Nat.Prime.not_dvd_mul Nat.prime_two S.not_dvd_index ho.not_two_dvd_nat
  exact ⟨(S.isPGroup'.map f).toSylow hn,rfl⟩

/-- Transport a common-normalizer Sylow through its literal whole-overlap map. -/
theorem extension_middle_sylow (hm : 0 < m)
    {I : Type*} [Group I] [Finite I] (e : I ≃* E.middle) (S : Sylow 2 I) :
    ∃ T : Sylow 2 E.carrier, (T : Subgroup E.carrier) = (S : Subgroup I).map
      ((inclusion (inf_le_left.trans E.left_le)).comp e.toMonoidHom) := by
  let j : E.middle →* E.carrier := inclusion (inf_le_left.trans E.left_le)
  let f := j.comp e.toMonoidHom
  have hr : f.range = E.middle.subgroupOf E.carrier := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.surjective,
      ←MonoidHom.range_eq_map,inclusion_range]
  exact mapped_sylow S f
    ((inclusion_injective (inf_le_left.trans E.left_le)).comp e.injective)
    (hr.symm ▸ extension_middle_index_odd E hm)

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour

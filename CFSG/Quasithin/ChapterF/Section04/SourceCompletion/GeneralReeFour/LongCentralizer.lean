module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.LongCentralizer
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.OuterSylow
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.CartanTransport

/-!
# Full long-root centralizers in the same Ree extension

The whole common endpoint preserves the native Suzuki parabolic and its
solvable residual. Factoring an extension element as inner times common
therefore detects membership in the full right endpoint by preservation
of that residual. A centralizer element fixes the native long-root element,
so the intrinsic centralizer residual calculation supplies that preservation.

The conclusion concerns the full centralizer in this very extension
carrier, including its outer part. It uses neither an ambient order bound
nor an ambient recognition premise. Source: Aschbacher–Smith F.4.27,43,
printed pp.288,296 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds ReeF4.EvenInvolutionGeometry
variable {m : ℕ} (E : GeneralReeExtension.SourceExtension m)

/-- Preserving the actual native Suzuki factor detects the full right endpoint. -/
theorem extension_preserving_suzuki_mem_right (hm : 0 < m)
    (a : MulAut (Model m)) (ha : a ∈ E.carrier)
    (hK : (localFactor m .suzuki).map a.toMonoidHom = localFactor m .suzuki) :
    a ∈ E.right := by
  have hi := ReeF4.SmallCompletion.conj_injective m hm
  obtain ⟨g,b,hb,rfl⟩ := E.factor a ha
  have hP : (parabolic m .suzuki).map b.toMonoidHom = parabolic m .suzuki := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (E.middle_preserves_right hi ⟨b,hb⟩ x).mpr hx
    · intro x hx
      exact ⟨b.symm x,(E.middle_preserves_right hi ⟨b,hb⟩ (b.symm x)).mp
        (by simpa using hx),b.apply_symm_apply x⟩
  have hbK : (localFactor m .suzuki).map b.toMonoidHom = localFactor m .suzuki := by
    rw [←parabolic_solvableResidual_map hm .suzuki,
      map_embedded_solvableResidual_of_hom,hP]
  have hgK : (localFactor m .suzuki).map (MulAut.conj g).toMonoidHom =
      localFactor m .suzuki := by
    change (localFactor m .suzuki).map
      ((MulAut.conj g).toMonoidHom.comp b.toMonoidHom) = _ at hK
    rwa [←map_map,hbK] at hK
  have hg : g ∈ parabolic m .suzuki := by
    rw [←ReeF4.SourceCompletion.suzuki_localFactor_normalizer hm]
    exact mem_normalizer_iff_map_conj_eq.mpr hgK
  exact E.right.mul_mem ((E.conj_mem_right_iff hi g).mpr hg) hb.2

private theorem aut_conj {X : Type*} [Group X] (a : MulAut X) (x : X) :
    a * MulAut.conj x * a⁻¹ = MulAut.conj (a x) := by
  ext y
  simp [MulAut.conj_apply]

/-- The full long-root centralizer in the marked extension lies in its full right endpoint. -/
theorem extension_long_centralizer_le_right (hm : 0 < m)
    {z : Model m} (hz : z ∈ longRootGroup m) (hz1 : z ≠ 1) :
    centralizer ({E.baseHom z} : Set E.carrier) ≤ E.right.subgroupOf E.carrier := by
  intro a ha
  have hc : a.val * MulAut.conj z = MulAut.conj z * a.val :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
  have hfix : a.val z = z := by
    apply ReeF4.SmallCompletion.conj_injective m hm
    rw [←aut_conj,hc,mul_inv_cancel_right]
  exact extension_preserving_suzuki_mem_right E hm a.val a.property
    (ReeF4.SourceCompletion.automorphism_fixing_long_preserves_suzuki hm hz hz1 a.val hfix)

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour

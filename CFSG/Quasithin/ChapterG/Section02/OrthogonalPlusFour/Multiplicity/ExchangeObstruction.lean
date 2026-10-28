module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange

/-!
# The factor-interchange witness must lie outside I

The two ordered S₃ factors are distinct normal subgroups of I/O₂(I), so
their ambient preimages are each preserved by I. Any element interchanging
them therefore lies outside I. In particular, T <= I excludes this proof
route; it does not exclude equality of the two multiplicities.

The literal Chapter 15 application constructs an element of T outside I
using the previously proved interchange from the compatible earlier
orthogonal action and local Sylow condition. This makes explicit the
additional symmetry supplied by that source configuration.

Source: Aschbacher–Smith, G.2.6(5) and 15.3.54–56, printed pp.336,
1146–1147 (combined manuscript, 1 March 2004).
-/

@[expose] public section
open Subgroup InvertedCubicTensor Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- An interchange of the actual ordered factor preimages cannot be inner in I. -/
theorem Hypothesis.exchange_not_mem_I (d : Hypothesis D g) {t : G}
    (he : conjugate
      (factorPreimage d.quotientSymmetricEquiv ProductDecomposition.leftFactor) t =
        factorPreimage d.quotientSymmetricEquiv ProductDecomposition.rightFactor) :
    t ∉ D.I g := by
  intro ht
  have hn : D.I g ≤ normalizer
      (factorPreimage d.quotientSymmetricEquiv ProductDecomposition.leftFactor : Set G) := by
    let K := ProductDecomposition.leftFactor.comap (moduleProjection d.quotientSymmetricEquiv)
    have : K.Normal := inferInstance
    have h := K.le_normalizer_map (D.I g).subtype
    rw [normalizer_eq_top] at h
    rw [← MonoidHom.range_eq_map, range_subtype] at h
    exact h
  have hc := mem_normalizer_iff_map_conj_eq.mp (hn ((D.I g).inv_mem ht))
  change conjugate
    (factorPreimage d.quotientSymmetricEquiv ProductDecomposition.leftFactor) t =
      factorPreimage d.quotientSymmetricEquiv ProductDecomposition.leftFactor at hc
  have hp := congrArg (fun A : Subgroup G =>
    (A.subgroupOf (D.I g)).map (moduleProjection d.quotientSymmetricEquiv)) (hc.symm.trans he)
  rw [factorPreimage_image, factorPreimage_image] at hp
  obtain ⟨x, hx⟩ := exists_ne (1 : S₃)
  have hm : (x, 1) ∈ ProductDecomposition.leftFactor := ⟨mem_top x, one_mem _⟩
  rw [hp] at hm
  exact hx hm.1

/-- When T lies in I, an additional factor interchange is impossible.
This is an obstruction to the interchange route, not to common multiplicity. -/
theorem Hypothesis.not_factorExchange_of_T_le_I (d : Hypothesis D g)
    (hTI : D.T ≤ D.I g) : ¬ FactorExchange d := by
  rintro ⟨t, ht, he⟩
  exact d.exchange_not_mem_I he (hTI ht)

namespace Multiplicity.Chapter15Exchange
open CFSG.Quasithin.Chapter15.Section03

/-- The stronger earlier Chapter 15 action supplies a genuine element outside I. -/
theorem literal_exists_outside_I
    {M Z Zperp V Y T : Subgroup G} {g : G}
    (a : NaturalOrthogonalAction M V) (hTM : T ≤ M)
    (hSyl : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = T)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) :
    ∃ t ∈ T, t ∉ (Chapter15.setup Z Zperp Y T).I g := by
  obtain ⟨t, ht, he⟩ := literal_factorExchange a hTM hSyl hspan d
  exact ⟨t, ht, d.exchange_not_mem_I he⟩

end Multiplicity.Chapter15Exchange
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour

module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.Inputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal.Transport
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SixResidual

/-!
# Degree two in the larger-field Borel branch

The moved subgroup W = [V,Y₊] lies in V ∩ L, hence in the marked Sylow
subgroup S ∩ L. Its image in L/Z(L) is nontrivial: otherwise every cubic
generator of Y₊ would have central displacement on V of exponent dividing
both two and three, so Y₊ would centralize V. Here the cubic generators
come from the earlier equality θ(M ∩ I) = Y₊.

B normalizes W and its literal {2,3}-residual centralizes W. The intrinsic
PSL₃ Borel calculation now forces n = 2. We use the actual equivalence
L/Z(L) ≃ componentImage I L L, retaining the central kernel throughout.
The natural-action interface is imported directly, independently of the
larger-field assembly module.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the final
proof of 15.3.35, printed p.1139, using 15.3.2(1), 15.3.11, 15.3.36 and
15.3.39--41. The subsequent PSL₃(4) Borel-rank contradiction belongs to
the larger-field assembly.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField.FieldDegree
variable {G : Type*} [Group G]

private theorem commute_of_cubic_of_central_displacement (y v : G)
    (hy : y ^ 3 = 1) (h2 : ⁅y, v⁆ ^ 2 = 1)
    (hc : y * ⁅y, v⁆ = ⁅y, v⁆ * y) : Commute y v := by
  have hfix : y * ⁅y,v⁆ * y⁻¹ = ⁅y,v⁆ := by rw [hc, mul_inv_cancel_right]
  have hs : ⁅y ^ 2,v⁆ = 1 := by
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hfix, ← pow_two, h2]
  have ht : ⁅y ^ 3,v⁆ = ⁅y,v⁆ := by
    rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one,
      commutatorElement_mul_left_eq_conj_mul, hs, mul_one, mul_inv_cancel, one_mul]
  rw [hy] at ht
  exact commutatorElement_eq_one_iff_commute.mp (by simpa using ht.symm)

variable {I L M Y S V V₁ V₂ Yplus B : Subgroup G} [(L.subgroupOf I).Normal]

private theorem yplus_le_M (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S) : Yplus ≤ M := by
  rw [← c.theta_eq]
  exact (closure_le _).2 (fun _ h => h.1.1)

private theorem moved_le_vector (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (a : ActionInputs M Y S V V₁ V₂ Yplus B) : ⁅V,Yplus⁆ ≤ V :=
  le_normalizer_iff_commutator_le_left.mp ((yplus_le_M c).trans a.earlier.normalized)

private theorem moved_le_component (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (a : ActionInputs M Y S V V₁ V₂ Yplus B) : ⁅V,Yplus⁆ ≤ L := by
  have hSI : S ≤ I := c.join_eq ▸ le_sup_right
  have hnorm : I ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance
  exact (commutator_mono le_rfl c.yplus_le).trans
    (le_normalizer_iff_commutator_le_right.mp ((a.earlier.le_sylow.trans hSI).trans hnorm))

private theorem moved_not_le_center (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (a : ActionInputs M Y S V V₁ V₂ Yplus B) :
    ¬ ⁅V,Yplus⁆ ≤ (center L).map L.subtype := by
  intro hZ
  apply a.noncentral
  rw [← c.theta_eq]
  apply (closure_le _).2
  rintro y ⟨hy,hy3⟩
  have hyY : y ∈ Yplus := c.theta_eq ▸ subset_closure ⟨hy,hy3⟩
  apply mem_centralizer_iff.mpr
  intro v hv
  have hd : ⁅y,v⁆ ∈ ⁅V,Yplus⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hyY hv
  have hc : y * ⁅y,v⁆ = ⁅y,v⁆ * y := by
    obtain ⟨z,hz,hze⟩ := hZ hd
    have hh := congrArg L.subtype (mem_center_iff.mp hz ⟨y,c.yplus_le hyY⟩)
    change y * (z : G) = (z : G) * y at hh
    change (z : G) = ⁅y,v⁆ at hze
    rwa [hze] at hh
  have : IsElementaryAbelian 2 V := a.earlier.elementary
  have h2 : ⁅y,v⁆ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ (moved_le_vector c a hd)
  exact (commute_of_cubic_of_central_displacement y v
    (hy3 ▸ pow_orderOf_eq_one y) h2 hc).eq.symm

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField.FieldDegree

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField
open FieldDegree
variable {G : Type*} [Group G] [Finite G]
variable {I L M Y S V V₁ V₂ Yplus B : Subgroup G} [(L.subgroupOf I).Normal]

/-- The Borel-action deduction in the larger-field paragraph of 15.3.35.
The genuine earlier action and cubic-generation inputs force the degree;
no parity, three-rank, or centerless-cover premise is needed. -/
theorem field_degree_eq_two
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (a : ActionInputs M Y S V V₁ V₂ Yplus B)
    (hB : BorelOverSylow L S B)
    {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL (componentImage I L L) 3 (2 ^ n)) : n = 2 := by
  have hmodel' := hmodel.of_mulEquiv (componentImageCenterEquiv I L c.component_le)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel'
  obtain ⟨P,hPS,hB⟩ := hB
  let W := (⁅V,Yplus⁆).subgroupOf L
  have hWL := moved_le_component c a
  have hWV := moved_le_vector c a
  have hmap : W.map L.subtype = ⁅V,Yplus⁆ := map_subgroupOf_eq_of_le hWL
  have hWP : W ≤ (P : Subgroup L) := by
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [hmap,hPS]
    exact le_inf (hWV.trans a.earlier.le_sylow) hWL
  have hWZ : ¬ W ≤ center L := by
    intro h
    exact moved_not_le_center c a (hmap ▸ map_mono h)
  have hWN : normalizer (P : Set L) ≤ normalizer (W : Set L) := by
    rw [← subgroupOf_normalizer_eq hWL]
    intro b hb
    exact a.borel_normalizes_moved (hB ▸ mem_map_of_mem L.subtype hb)
  apply Matrix.PSL3.LinearThree.RootScalars.field_degree_eq_two_of_central_cover
    hF hn e P W hWP hWZ hWN
  intro b hb hcop
  have hbB : (b : G) ∈ B := hB ▸ mem_map_of_mem L.subtype hb
  have hfix : (b : G) ∈ centralizer (V : Set G) :=
    a.residual_centralizes (subset_closure ⟨hbB, by simpa using hcop⟩)
  apply mem_centralizer_iff.mpr
  intro w hw
  exact Subtype.ext (mem_centralizer_iff.mp hfix w (hWV hw))

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField

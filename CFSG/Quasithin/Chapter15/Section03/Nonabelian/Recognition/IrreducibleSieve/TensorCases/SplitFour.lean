module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Input
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Reductions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases.Models
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases.Placement
public import Theory.SpecificGroups.PSL2.ProductSylowPointwiseInner
public import Theory.Representation.OrthogonalFourPlusMatrix.FieldDisplacement

/-!
# Exclusion of the split orthogonal-four alternative

Conjugation by the marked involution fixes the genuine Sylow intersection
with the normal component join pointwise. The actual elementary orthogonal
group is SL₂(F) × SL₂(F); its pointwise Sylow fixers are inner. Centerlessness
and the faithful irreducible binary action therefore place the involution in
the component join. Determinant coordinates give binary displacement rank at
least 2n for every nonidentity element. Since n > 1, this contradicts rank two.

The proof retains the original `SourceData`, `ComponentData`, and `PlusCase`
interfaces. It uses the established coordinate comparison with the
Siegel-generated elementary orthogonal carrier.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.9.3(15),
printed pp.354–356, and the exclusion in 15.3.58, printed p.1149.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section09
open ClassicalOrthogonal.FourPlusMatrix

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- G.9.3(15) is incompatible with the marked central involution of 15.3.58.
All placement and actual-action displacement premises are discharged. -/
theorem not_plusCase (h : SourceData ρ X T v s) (hK : ComponentData ρ K) :
    ¬ PlusCase ρ K (s + 1) := by
  rintro ⟨n, hn, ⟨e, f, hf⟩, _, _⟩
  have hvK := MathieuCases.marked_mem_component_of_pointwise_fixers h hK
    (e.trans (elementaryEquiv (F := GaloisField 2 n)).symm)
    (fun a S hS => Theory.PSL2.product_aut_fixing_sylow_inner S a hS)
  let u : K := ⟨v, hvK⟩
  have hu : u ≠ 1 := by
    intro he
    have hv : v = 1 := congrArg K.subtype he
    have hi := h.involution
    rw [hv, orderOf_one] at hi
    contradiction
  have hne : e u ≠ 1 := fun he => hu (e.injective (he.trans e.map_one.symm))
  have hd := FieldDisplacement.elementary_binary_displacement_rank (e u) hne
  rw [GaloisField.finrank 2 (by omega : n ≠ 0)] at hd
  have hr := fixedCodim_map_equivariant (ρ.comp K.subtype) (TwoComponents.fourOrthogonal n)
    e.toMonoidHom f hf (zpowers u)
  rw [MonoidHom.map_zpowers, fixedCodim_zpowers_eq_displacement_rank,
    fixedCodim_zpowers_eq_displacement_rank] at hr
  change Module.finrank (ZMod 2) (displacement ρ v) =
    Module.finrank (ZMod 2) (LinearMap.range (TwoComponents.fourOrthogonal n (e u) -
      LinearMap.id)) at hr
  change 2 * n ≤ Module.finrank (ZMod 2)
    (LinearMap.range (TwoComponents.fourOrthogonal n (e u) - LinearMap.id)) at hd
  have hb : 2 * n ≤ 2 := hd.trans_eq (hr.symm.trans h.displacement_rank)
  omega

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases

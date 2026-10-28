module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Noncyclic
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# The literal extension in the noncyclic alternative

The marked recognition theorem constructs the ambient Heisenberg semidirect
product with its specified four-group action. Transporting the projection
through that isomorphism supplies the actual normal kernel and quotient used
in F.6.18(2). Its kernel has order 27, exponent three, and is extraspecial.

Source: Aschbacher–Smith, F.6.16 and F.6.18(2), printed pp.308–310.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G : Type u} [Group G]
/-- The kernel of the transported four-group projection is the original Heisenberg group. -/
noncomputable def heisenbergKernelEquiv
    (e : G ≃* MarkedCubicRecognition.HeisenbergExtension) :
    (SemidirectProduct.rightHom.comp e.toMonoidHom).ker ≃* HeisenbergPrime 3 := by
  let i : HeisenbergPrime 3 →* MarkedCubicRecognition.HeisenbergExtension :=
    SemidirectProduct.inl
  let k := (SemidirectProduct.rightHom : MarkedCubicRecognition.HeisenbergExtension →*
    MarkedCubicRecognition.Four).ker
  have he : (SemidirectProduct.rightHom.comp e.toMonoidHom).ker =
      k.map e.symm.toMonoidHom := MonoidHom.ker_comp_mulEquiv _ e
  exact ((MulEquiv.subgroupCongr he).trans (e.symm.subgroupMap k).symm).trans
    ((MulEquiv.subgroupCongr SemidirectProduct.range_inl_eq_ker_rightHom.symm).trans
      (MonoidHom.ofInjective (f := i) SemidirectProduct.inl_injective).symm)

/-- The source extension is realized by a surjection with its literal kernel.
The original ambient equivalence retains the prescribed action. -/
theorem heisenberg_extension_data
    (e : G ≃* MarkedCubicRecognition.HeisenbergExtension) :
    ∃ f : G →* MarkedCubicRecognition.Four,
      Function.Surjective f ∧ Nonempty (f.ker ≃* HeisenbergPrime 3) ∧
      IsExtraspecial 3 f.ker ∧ Nat.card f.ker = 27 ∧ Monoid.exponent f.ker = 3 ∧
      Nonempty ((G ⧸ f.ker) ≃* MarkedCubicRecognition.Four) := by
  let f := SemidirectProduct.rightHom.comp e.toMonoidHom
  have hf : Function.Surjective f := SemidirectProduct.rightHom_surjective.comp e.surjective
  let j := heisenbergKernelEquiv e
  refine ⟨f, hf, ⟨j⟩, IsExtraspecial.of_mulEquiv j.symm
    (HeisenbergPrime.isExtraspecial (by decide)), ?_, ?_,
    ⟨QuotientGroup.quotientKerEquivOfSurjective f hf⟩⟩
  · exact (Nat.card_congr j.toEquiv).trans HeisenbergPrime.card
  · exact (Monoid.exponent_eq_of_mulEquiv j).trans (HeisenbergPrime.exponent (by decide))

end CFSG.Quasithin.ChapterF.SourceAssembly

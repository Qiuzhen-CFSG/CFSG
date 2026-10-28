module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen.LocalGeometry.Actors
public import Theory.SpecificGroups.PSL2.SeventeenNoDiagonal
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The degree-eight action excludes diagonal outer actors

The actual conjugation image contains every inner automorphism of PSL₂(17).
The binary degree bound excludes order sixteen in this image, so the
prime-field diagonal calculation shows the image is inner. The generalized
Fitting centralizer theorem then places every ambient element in F*(G).

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript p.9; Aschbacher--Smith K.2, printed p.453.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- There is no surviving diagonal extension in binary degree at most eight. -/
theorem source_component_eq_top
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    (hd : Module.finrank (ZMod 2) V ≤ 8) : generalizedFitting G = ⊤ := by
  obtain ⟨e⟩ := source_component_equiv_seventeen ρ h hm
  let L := generalizedFitting G
  let f : G →* MulAut Theory.PSL2.SeventeenGeometry.Model :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : G →* MulAut L)
  have hi : (MulAut.conj : Theory.PSL2.SeventeenGeometry.Model →*
      MulAut Theory.PSL2.SeventeenGeometry.Model).range ≤ f.range := by
    rintro _ ⟨s, rfl⟩
    refine ⟨(e.symm s : G), ?_⟩
    change MulAut.congr e (MulAut.conjNormal (e.symm s : G)) = MulAut.conj s
    rw [MulAut.conjNormal_val, MulAut.congr_conj, e.apply_symm_apply]
  have hj := Theory.PSL2.SeventeenGeometry.le_inner_of_no_order_sixteen f.range hi
    (by rintro _ ⟨g, rfl⟩; exact source_image_order_ne_sixteen ρ h hd f g)
  apply top_unique
  intro g _
  obtain ⟨s, hs⟩ := hj ⟨g, rfl⟩
  obtain ⟨l, hl⟩ := (MulAut.congr_inner_iff e
    (MulAut.conjNormal g : MulAut L)).mp ⟨s, hs.symm⟩
  have hmemb : g ∈ (MulAut.innerSubgroup L).comap MulAut.conjNormal := ⟨l, hl.symm⟩
  rw [MulAut.conjNormal_comap_innerSubgroup] at hmemb
  exact (sup_le le_rfl (centralizer_generalizedFitting_le G)) hmemb

/-- The original ambient group, after excluding the covering
kernel and diagonal extension, is genuinely isomorphic to PSL₂(ZMod 17). -/
theorem source_ambient_equiv_seventeen
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    (hd : Module.finrank (ZMod 2) V ≤ 8) :
    Nonempty (G ≃* Theory.PSL2.SeventeenFrobenius.Model) := by
  obtain ⟨e⟩ := source_component_equiv_seventeen ρ h hm
  have ht := source_component_eq_top ρ h hm hd
  let eL : generalizedFitting G ≃* G := MulEquiv.ofBijective
    (generalizedFitting G).subtype ⟨Subtype.val_injective,
      fun g => ⟨⟨g, ht ▸ mem_top g⟩, rfl⟩⟩
  exact ⟨eL.symm.trans e⟩

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen

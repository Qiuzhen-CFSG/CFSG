module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGraphPlacement
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.GraphFusion

/-!
# Uniform graph-class transport in the marked binary unitary completion

Every element of the actual model graph-involution class in the marked
upper extension has a conjugator inside the original overlap. The matrix
proof constructs this conjugator with a trace-one scalar; its image under
the middle completion map therefore gives the required ambient conjugacy.
There is no additional placement premise.

Combining this with the proved marked graph/root exclusion gives F.4.36
for every graph-class involution in the original extended Sylow subgroup.
The distinct twisted outer class is retained. Source: Aschbacher--Smith,
F.4.35--36, printed p.292.
-/
@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.GraphPlacement
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open GraphCentralizer
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "B" => Extension.overlap 1 hn

/-- Model graph conjugacy inside the marked upper extension is already
conjugacy inside the literal common endpoint group. -/
theorem overlap_graph_class_placement (f : B)
    (hfU : f.val ∈ Extension.extendedUpper 1 hn)
    (hf : IsConj (Extension.sigma 1 hn) f.val) :
    ∃ v : B, v * graphInvolution * v⁻¹ = f := by
  obtain ⟨fM, hfM, hfe⟩ := hfU
  have hfclass : IsConj (UnitaryFourOuter.sigma F σ hσ) fM := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hf
    obtain ⟨gM, rfl⟩ := Extension.extensionProjection_surjective 1 hn g
    apply isConj_iff.mpr
    refine ⟨gM, ?_⟩
    apply Extension.extensionProjection_injective 1 hn
    simpa only [map_mul, map_inv, Extension.extensionProjection_sigma, hfe] using hg
  obtain ⟨v, hv, hvf⟩ := UnitaryFourGraphPlacement.upper_graph_conjugator F σ hσ
    (PointLocal.fieldConj_nontrivial 1 hn) hfM hfclass
  let w : B :=
    ⟨Extension.extensionProjection 1 hn (SemidirectProduct.inl v),
      ⟨SemidirectProduct.inl v, UnitaryFourSylow.upper_le_borel F σ hσ hv, rfl⟩⟩
  refine ⟨w, Subtype.ext ?_⟩
  change Extension.extensionProjection 1 hn (SemidirectProduct.inl v) *
    Extension.sigma 1 hn * (Extension.extensionProjection 1 hn (SemidirectProduct.inl v))⁻¹ = f.val
  simpa only [map_mul, map_inv, Extension.extensionProjection_sigma] using
    (congrArg (Extension.extensionProjection 1 hn) hvf).trans hfe

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
    (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

/-- The actual middle map lifts the entire upper model graph class to
the marked ambient graph class, without a global model embedding. -/
theorem model_graph_class_lifts (f : B)
    (hfU : f.val ∈ Extension.extendedUpper 1 hn)
    (hf : IsConj (Extension.sigma 1 hn) f.val) :
    IsConj (i (c.middle graphInvolution)) (i (c.middle f)) := by
  obtain ⟨v, hv⟩ := overlap_graph_class_placement f hfU hf
  exact (i.comp c.middle).map_isConj (isConj_iff.mpr ⟨v, hv⟩)

/-- F.4.36 for every actual model graph-class involution in the marked
extended Sylow, under the original root-centralizer bound. -/
theorem source_graph_involution_not_conjugate_root
    (hi : Function.Injective i)
    (z : Extension.point 1 hn)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (f : B) (hfU : f.val ∈ Extension.extendedUpper 1 hn)
    (hf : IsConj (Extension.sigma 1 hn) f.val) :
    ¬ IsConj (i (c.middle f)) (i (c.left z)) :=
  GraphFusion.source_graph_class_not_conjugate_root c i hi z hc
    (model_graph_class_lifts c i f hfU hf)

/-- All original upper graph-class elements have the same ambient class
through the supplied completion, including when the ambient group has
additional involution fusion of other kinds. -/
theorem source_graph_class_fusion (f g : B)
    (hfU : f.val ∈ Extension.extendedUpper 1 hn)
    (hgU : g.val ∈ Extension.extendedUpper 1 hn)
    (hf : IsConj (Extension.sigma 1 hn) f.val)
    (hg : IsConj (Extension.sigma 1 hn) g.val) :
    IsConj (i (c.middle f)) (i (c.middle g)) :=
  (model_graph_class_lifts c i f hfU hf).symm.trans
    (model_graph_class_lifts c i g hgU hg)

end CFSG.Quasithin.ChapterF.UnitaryTwo.GraphPlacement

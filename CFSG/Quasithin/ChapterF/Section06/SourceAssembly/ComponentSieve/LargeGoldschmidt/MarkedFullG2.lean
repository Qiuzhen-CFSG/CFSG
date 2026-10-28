module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.G2
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedResidual
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SylowExponent
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentModels
public import Theory.Mathieu.M12.GoldschmidtFullG2Obstruction

/-!
# The literal full binary G₂ marking in the source group

Restricting the full marked pair to its actual derived overlap gives an
injective wreathed group of order 32 in the original two-residual. Both
local inclusion squares are used in the checked a²=a³ residual argument.
The same full marking excludes an ambient M₁₂: its first vertex centralizes
the transported whole Sylow center, contradicting the concrete local
residual-order obstruction. No abstract Sylow distinction is asserted.

Source: Aschbacher–Smith F.1.12(I)(3), F.6.18(11), printed pp.263,310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open Atlas.G2 Atlas.G2.BinaryParabolicPair
open Atlas.G2.BinaryCore Atlas.G2.LieParabolicSetup
open Atlas.G2.LieAutomorphismExtensions Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
variable {G : Type*} [Group G] {G₁ G₂ : Subgroup G}

theorem full_g2_marked_inner_sylow_embedding
    (hM : GreenBook.ExceptionalModels.G2.IsFullAmalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    ∃ f : derivedSylow →* G, Function.Injective f ∧
      f.range ≤ G₁ ⊓ G₂ ∧ f.range ≤ pResidual 2 G := by
  obtain ⟨m⟩ := hM
  let e := m.symm
  let dL : BinaryLeft →* firstParabolic :=
    (BinaryDerived.subtype.comp BinaryLeft.subtype).codRestrict firstParabolic (fun x => by
      change (x.val.val : Model (ZMod 2)) ∈ firstParabolic
      rw [← parabolic₁_binary]
      exact x.property)
  let dR : BinaryRight →* secondParabolic :=
    (BinaryDerived.subtype.comp BinaryRight.subtype).codRestrict secondParabolic
      (fun x => x.property)
  let dB : binaryOverlap →* commonSylow :=
    (BinaryDerived.subtype.comp binaryOverlap.subtype).codRestrict _ (fun x => by
      change (x.val.val : Model (ZMod 2)) ∈ unipotent
      exact binaryOverlap_eq.le x.property)
  let fS : commonSylow →* G := (G₁ ⊓ G₂).subtype.comp e.middle.toMonoidHom
  let fL : firstParabolic →* G := G₁.subtype.comp e.left.toMonoidHom
  let fR : secondParabolic →* G := G₂.subtype.comp e.right.toMonoidHom
  let l := fL.comp dL
  let r := fR.comp dR
  have hl (x : binaryOverlap) : l (binaryAmalgam.left x) = fS (dB x) :=
    congrArg Subtype.val (e.left_commutes (dB x))
  have hr (x : binaryOverlap) : r (binaryAmalgam.right x) = fS (dB x) :=
    congrArg Subtype.val (e.right_commutes (dB x))
  let j : derivedSylow ≃* binaryOverlap :=
    MulEquiv.subgroupCongr Atlas.G2.ExceptionalLocalQuotients.overlap_eq_derivedSylow.symm
  let f := fS.comp (dB.comp j.toMonoidHom)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x y h
    have hb : dB (j x) = dB (j y) := e.middle.injective (Subtype.ext h)
    have he : (j x).val.val = (j y).val.val :=
      congrArg (fun b : commonSylow => (b : Model (ZMod 2))) hb
    exact j.injective (Subtype.ext (Subtype.ext he))
  · rintro x ⟨s,rfl⟩
    exact (e.middle (dB (j s))).property
  · rintro x ⟨s,rfl⟩
    change fS (dB (j s)) ∈ pResidual 2 G
    rw [← hl]
    exact binary_amalgam_middle_le_twoResidual l r (fun x => (hl x).trans (hr x).symm) (j s)
end CFSG.Quasithin.ChapterF.SourceAssembly

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open Atlas.G2 Atlas.G2.BinaryParabolicPair
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

theorem not_mathieu_of_full_g2_amalgam
    (h : IsGoldschmidtTriple G₁ G₂)
    (hM : GreenBook.ExceptionalModels.G2.IsFullAmalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right))
    (eG : G ≃* Sporadic.Mathieu.M12) : False := by
  obtain ⟨T,hT⟩ := h.intersection_sylow
  obtain ⟨m⟩ := hM
  let P := T.mapSurjective (f := eG.toMonoidHom) eG.surjective
  let eTP : T ≃* P := (T : Subgroup G).equivMapOfInjective eG.toMonoidHom eG.injective
  let j : commonSylow ≃* P :=
    (m.middle.symm.trans (MulEquiv.subgroupCongr hT)).trans eTP
  let f : firstParabolic →* Sporadic.Mathieu.M12 :=
    eG.toMonoidHom.comp (G₁.subtype.comp m.left.symm.toMonoidHom)
  have hf : Function.Injective f := eG.injective.comp
    (G₁.subtype_injective.comp m.left.symm.injective)
  have hj (s : commonSylow) : f (concreteAmalgam.left s) = (j s : Sporadic.Mathieu.M12) :=
    congrArg (fun g : G₁ => eG (g : G)) (m.symm.left_commutes s)
  apply Sporadic.Mathieu.M12FullG2Obstruction.not_injective_first_parabolic f hf P
  rintro _ ⟨g,rfl⟩
  apply mem_centralizer_iff.mpr
  rintro _ ⟨x,hx,rfl⟩
  change (x : Sporadic.Mathieu.M12) * f g = f g * (x : Sporadic.Mathieu.M12)
  let y := j.symm x
  have hy : y ∈ center commonSylow := by
    apply mem_center_iff.mpr
    intro z
    apply j.injective
    simpa only [y,map_mul,MulEquiv.apply_symm_apply] using mem_center_iff.mp hx (j z)
  have hc := (commutator_eq_bot_iff_le_centralizer.mp
    GreenBook.ExceptionalModels.G2.full_numbering) g.property
  have he : concreteAmalgam.left y * g = g * concreteAmalgam.left y :=
    Subtype.ext (mem_centralizer_iff.mp hc _ ⟨y,hy,rfl⟩)
  have hh := congrArg f he
  simpa only [map_mul,hj,y,MulEquiv.apply_symm_apply] using hh
end CFSG.Quasithin.ChapterF.SourceAssembly

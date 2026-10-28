module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Bounds
public import BenderSuzuki.External.Huppert.XI.SubgroupSolvable


/-!
# The literal solvable Suzuki subgroup used by the restrictions

The injective map J → L followed by the source model L ≃ Sz(q) identifies
J with its actual image. Its supplied solvability gives standard containment
in a Borel or one of the three torus normalizers. The given Sylow subgroup
U transports to an elementary Sylow subgroup of that same image with the
same order. These conclusions retain the same map throughout.

Source: GLS4, Chapter 4, Lemma 3.8, as applied in Chapter 2, Lemmas
14.7–14.9; refs/KGroup/GLS4/Chapter4.tex and Chapter2.tex.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

public theorem Context.centralizer_model_standard_containment (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (T : SuzukiNonsplitTorusPair m) :
    SuzukiStandardContainment T (d.model.toMonoidHom.comp f).range := by
  let e := MonoidHom.ofInjective (f := d.model.toMonoidHom.comp f) (d.model.injective.comp hf)
  let := g.centralizer_solvable
  let : Group.IsSolvable (d.model.toMonoidHom.comp f).range :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact suzukiStandardContainment_of_isSolvable (by have := d.parameter_pos; omega) T _

public theorem Context.centralizer_model_elementary_sylow (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) :
    ∃ V : Sylow 2 (d.model.toMonoidHom.comp f).range,
      IsElementaryAbelian 2 V ∧ Nat.card V = Nat.card g.U := by
  let J := centralizer (residualGenerated M z t : Set G)
  let e := MonoidHom.ofInjective (f := d.model.toMonoidHom.comp f) (d.model.injective.comp hf)
  obtain ⟨V, hV⟩ := g.U_sylow_centralizer
  let eU : V ≃* g.U := ((V : Subgroup J).equivMapOfInjective J.subtype
    J.subtype_injective).trans (MulEquiv.subgroupCongr hV)
  let := g.U_elementary
  let : IsElementaryAbelian 2 V :=
    IsElementaryAbelian.of_surjective eU.symm.toMonoidHom eU.symm.surjective
  let W := V.mapSurjective e.surjective
  let eW := (V : Subgroup J).equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨W, ?_, ?_⟩
  · exact IsElementaryAbelian.of_surjective eW.toMonoidHom eW.surjective
  · exact (Nat.card_congr eW.toEquiv).symm.trans (Nat.card_congr eU.toEquiv)

end BenderSuzuki.ZD.SuzukiExclusion

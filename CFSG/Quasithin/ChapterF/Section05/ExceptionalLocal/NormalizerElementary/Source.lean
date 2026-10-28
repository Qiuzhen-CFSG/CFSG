module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary.PointSource
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary.SourceFusion
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionFacts

/-!
# Original-source elementary normalizer conclusions

The completed source fusion record discharges the earlier-source premise
in the literal elementary family, intersection, transvection, joint
centralizer, root-transitivity and point-quotient theorems. These are direct
consumer applications with the marked short involution fixed by the original
completion, with no additional local-model or fusion premise.

Source: Aschbacher–Smith F.5.4–5, printed pp.301–302.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

theorem source_normalizer_elementary_list (y : G) (hy : y∈Source.sylowImage c i)
    (hyt : y∉Tcentralizer c i (sourceMarkedShort c i)) (B : Subgroup G) :
    (B≤Source.sylowImage c i ∧ IsElementaryAbelian 2 B ∧ Nat.card B=16) ↔
      B=A c i false ∨ B=A c i true ∨
      B=(A c i true).map (MulAut.conj y).toMonoidHom ∨ B=Q c i true :=
  normalizer_elementary_list c i z h (sourceMarkedShort c i) (source_fusionFacts c i z h) y hy hyt B

theorem source_normalizer_plane_intersection (y : G) (hy : y∈Source.sylowImage c i)
    (hyt : y∉Tcentralizer c i (sourceMarkedShort c i)) :
    A c i true ⊓ (A c i true).map (MulAut.conj y).toMonoidHom =
      zpowers (rootElement c i z) ⊔ zpowers (sourceMarkedShort c i) :=
  normalizer_plane_A_intersection c i z h (sourceMarkedShort c i)
    (source_fusionFacts c i z h) y hy hyt

theorem source_normalizer_joint_centralizer :
    centralizer ({rootElement c i z,sourceMarkedShort c i} : Set G)=
      Tcentralizer c i (sourceMarkedShort c i) := by
  rw [←normalizer_root_short_centralizer c i z h (sourceMarkedShort c i) (source_fusionFacts c i z h)]
  ext x
  simp only [mem_centralizer_iff,mem_inf,Set.mem_insert_iff,Set.mem_singleton_iff,
    forall_eq_or_imp,forall_eq]

theorem source_normalizer_transvection (b : Bool) :
    ∃ g∈normalizer (A c i b : Set G),
      ((centralizer ({g} : Set G)).subgroupOf (A c i b)).index=2 :=
  normalizer_A_transvection c i z h (sourceMarkedShort c i) (source_fusionFacts c i z h) b

theorem source_normalizer_point_quotient :
    Nonempty (normalizerQuotient c i false ≃* Equiv.Perm (Fin 5)) :=
  normalizer_point_quotient_of_source c i z h (sourceMarkedShort c i) (source_fusionFacts c i z h)

theorem source_normalizer_root_transitive (b : Bool) :
    ∀ x∈A c i b, IsConj (rootElement c i z) x →
      ∃ n∈normalizer (A c i b : Set G), MulAut.conj n (rootElement c i z)=x :=
  normalizer_root_transitive c i z h (sourceMarkedShort c i) (source_fusionFacts c i z h) b

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal

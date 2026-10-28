module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.BinaryRankTwo
public import Theory.Mathieu.M11.OrdinaryLocal

/-!
# The initial ordinary M₁₁ row

The original two-core quotient marking is a finite perfect central two-cover.
The concrete semidihedral Sylow calculation removes that kernel. All M₁₁
Sylow fixers are inner, so the source singleton centralizer overgroup places
C_L(Z(S_L)) inside M_L; maximality and properness give equality. This proves
the full M₁₁ constructor of the initial ordinary catalogue.

The original component, Sylow and local intersection are retained. The
remaining sporadic rows and initial catalogue exhaustiveness stay with the
ordinary catalogue assembly. The later Thompson-normalizer residual clause
of 15.1.22 is a separate obligation.
Source: Aschbacher--Smith 15.1.20(3d), printed pp.1096--1097, and I.1.3.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The source quotient marking itself lifts to an actual M₁₁ equivalence;
no trivial-center premise is imposed on the original ordinary component. -/
theorem PreExclusionSource.mathieuEleven_equiv_of_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M11) :
    Nonempty (d.L ≃* Sporadic.Mathieu.M11) := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let f := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  exact ⟨MulEquiv.ofBijective (f.toMonoidHom.comp (QuotientGroup.mk' (center d.L)))
    ⟨Sporadic.Mathieu.OrdinaryLocal.central_two_cover_injective (s.ordinary hL).center_two f,
      f.surjective.comp (QuotientGroup.mk'_surjective _)⟩⟩

/-- The maximal Sylow-center centralizer is exactly the original M_L. -/
theorem PreExclusionSource.mathieuEleven_centralizer_eq
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Sporadic.Mathieu.M11) :
    d.ML = d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) := by
  apply s.centralizer_eq_of_sylow_fixers (h := h) hG hM hu hL e
  · intro _ a _ _
    exact Sporadic.Mathieu.automorphism_inner_of_equiv_m11 (MulEquiv.refl _) a
  · exact Sporadic.Mathieu.OrdinaryLocal.centralizer_isCoatom e

/-- The complete initial M₁₁ constructor, with the literal two-core quotient
and the Sylow-center centralizer clause. -/
theorem PreExclusionSource.ordinary20_of_mathieuEleven_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M11) :
    d.Ordinary20Alternatives := by
  obtain ⟨f⟩ := s.mathieuEleven_equiv_of_quotient (h := h) hL e
  exact .sporadic .m11 (by intro he; cases he) (by intro he; cases he) ⟨e⟩
    (s.mathieuEleven_centralizer_eq (h := h) hG hM hu hL f)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.HexadComplement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.CoreInvolutions
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadOuterComplement

/-!
# The compatible outer extension in the original Mathieu overlap

The original marked Mathieu arguments supply perfectness of C_H(X), its
involutory normalizer splitting, and the exact native hexad defining the
point-plane overlap. The new source theorem extends the canonical perfect
order-1080 subgroup across an involution preserving that same hexad section.
The resulting actual subgroup has order 2160, contains X, and is disjoint
from Q. Its original Aut(M22) projection has exactly X as kernel and image
of order 720. Both native and original quotient markings are retained.

No extra hypotheses or LocalData-dependent fusion are used. The invariant
core complement and Todd splitting remain with the recognition owner.
Source: Aschbacher--Segev, Invent. Math. 105 (1991), (4.8), printed p.599,
DOI 10.1007/BF01232280; the original Aschbacher--Smith 8.2.12--14 application.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))

include D h hmany hV hq hnon a E hE

include z hz hne hquot

/-- The actual point-plane overlap contains the extended hexad subgroup,
with its specified native outer involution and its original cubic marking. -/
theorem sourceOrbit_m24_full_cubic_hexad_outer :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)),
      ∃ (B : Finset (Fin 22)) (hB : B ∈ m22Blocks),
        (normalizer (D.sourceOrbit : Set G)).subgroupOf (centralizer ({(z : G)} : Set G)) =
          (Recognition.JankoFour.LocalGeometry.LocalSubgroups.designStabilizer B).comap
            (Recognition.JankoFour.LocalGeometry.CubicLift.projection cubic) ∧
        ∃ (A : Subgroup (fullCubicCentralizer cubic X)) (v : fullCubicNormalizer cubic X)
            (t : m22DesignAut),
          Nat.card A=1080 ∧ Group.IsPerfect A ∧ fullCubicScalar cubic X ≤ A ∧
          A.map (fullCubicSimpleProjection ht cubic X)=hexadSectionImage hB ∧
          orderOf t=2 ∧ t.val ∉ M22 ∧ t • B=B ∧
          t • Classical.choose (exists_m22Hexad_complementary_point hB) =
            Classical.choose (exists_m22Hexad_complementary_point hB) ∧
          Recognition.JankoFour.LocalGeometry.CubicLift.projection cubic v.val=m22DesignAutToAut t ∧
          orderOf v=2 ∧ v.val ∉ fullCubicCentralizer cubic X ∧
          v.val ∈ normalizer
            (A.map (fullCubicCentralizer cubic X).subtype : Set (centralizer ({(z : G)} : Set G))) ∧
          let J := A.map (fullCubicCentralizer cubic X).subtype ⊔ zpowers v.val
          Nat.card J=2160 ∧ Disjoint (center (centralizer ({(z : G)} : Set G))) J ∧
          Disjoint (Recognition.JankoFour.core (z : G)) J ∧ J ≤ fullCubicNormalizer cubic X ∧
          cubicSylowImage cubic X ≤ J ∧
          J ≤ (normalizer (D.sourceOrbit : Set G)).subgroupOf (centralizer ({(z : G)} : Set G)) := by
  intro ht cubic X
  obtain ⟨B,hB,hpre,_⟩ := D.sourceOrbit_m24_full_cubic_hexad_complement
    h hmany hV hq hnon a E hE z hz hne hquot cubic X
  let := (D.sourceOrbit_m24_full_cubic_perfect h hmany hV hq hnon a E hE z hz hne hquot cubic X).2.1
  obtain ⟨s,hs,hso,_⟩ := D.sourceOrbit_m24_full_cubic_split
    h hmany hV hq hnon a E hE z hz hne hquot cubic X
  exact ⟨B,hB,hpre,fullCubic_hexad_outer_complement ht cubic X s
    (hs ▸ pow_orderOf_eq_one s) hso hB (normalizer (D.sourceOrbit : Set G)) hpre⟩

/-- The same original subgroup has trivial intersection with Q and retains
exactly X as the kernel of its Aut(M22) projection, whose image has order 720. -/
theorem sourceOrbit_m24_full_cubic_hexad_outer_quotient :
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)),
      ∃ J : Subgroup (centralizer ({(z : G)} : Set G)),
        Nat.card J=2160 ∧ Disjoint (Recognition.JankoFour.core (z : G)) J ∧
        J ≤ fullCubicNormalizer cubic X ∧ cubicSylowImage cubic X ≤ J ∧
        J ≤ (normalizer (D.sourceOrbit : Set G)).subgroupOf (centralizer ({(z : G)} : Set G)) ∧
        ((Recognition.JankoFour.LocalGeometry.CubicLift.projection cubic).comp J.subtype).ker =
          (cubicSylowImage cubic X).subgroupOf J ∧
        Nat.card (J.map (Recognition.JankoFour.LocalGeometry.CubicLift.projection cubic))=720 := by
  intro cubic X
  have ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨B,hB,hpre,A,v,t,_,_,_,_,_,_,_,_,_,_,_,_,hJc,_,hJQ,hJN,hXJ,hJM⟩ :=
    D.sourceOrbit_m24_full_cubic_hexad_outer h hmany hV hq hnon a E hE z hz hne hquot cubic X
  exact ⟨_,hJc,hJQ,hJN,hXJ,hJM,fullCubic_marker_free_quotient ht cubic X _ hJc hJQ hXJ⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

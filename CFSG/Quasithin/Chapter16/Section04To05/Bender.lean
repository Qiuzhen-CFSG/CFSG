module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Contracts
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Orbit
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Centralizer
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Onan
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.EndpointReduction
public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.TwoStructure

/-!
# The Bender branch of Proposition 16.5.1

From the source Bender quotient and the standard Δ₀ setup, construct the
cyclic actor, its faithful normalizer action, and the conjugator moving Ω₁(T_C).
All GLS96 Definition 14.1 hypotheses are verified. The moving conjugator and
the odd Sylow-fixed orbit exclude the first three O'Nan alternatives, leaving
|Ω₁(T_C)| = 2, |V| = 8 and the nonabelian group of order 21.

The endpoint reduction forces the fixed-field order to be four and excludes
the unitary case by preservation of the actual embedded Φ(T_L). Hence
L ≃ PSL₂(4) and N_G(L) = L C_G(L). Faithful projection of R into L gives
T_C = Ω₁(T_C) of order two. The proved cyclic-centralizer clause of 16.4.4
then constructs C_G(z) ≃ PSL₂(4) × C₂, with z central in the supplied Sylow.
This gives `CFSG.Quasithin.IsJanko1Type G`.

The final theorem retains only the permitted earlier cover, 16.4.2(4),
16.4.6, 16.4.8, 16.4.10 and GLS96 C.14.2 inputs. The source assembly owner
supplies these earlier results. Global identification with the concrete J₁
model belongs to the separate I.4.9 recognition theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed pp.1194–1195; GLS96, C.14.1–14.2.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.Bender
variable {G : Type*} [Group G] [Finite G]

/-- The exceptional action supplies the local J₁ recognition witness. The
component, normalizer and centralizer conclusions are proved by the endpoint
reduction; the cyclic-centralizer clause is the proved source 16.4.4(2). -/
theorem Geometry.isJanko1Type_of_onan_alternatives
    {T : Sylow 2 G} {z g : G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n) (h : IntersectionSetup T z L g R)
    (hE : HasEvenTypeCentralizers G)
    (hconj : R = (commutingSylow T L).conjBy g)
    (hcover : center L ≠ ⊥ →
      Nonempty ((L ⧸ center L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (halt : let := d.elementary
      Representation.GoldschmidtONan.Alternatives
        (normalizerRepresentation (benderSpace T L))
        (inducedActor (benderSpace T L) d.actor)) : IsJanko1Type G := by
  have hfaith : Disjoint R (centralizer (L : Set G)) :=
    disjoint_iff.mpr h.normalizer_structure.2.2.2
  obtain ⟨hUC, hV, hA, _⟩ := d.exceptional_cardinalities h.toStandardSetup hfaith halt
  obtain ⟨⟨e⟩, hnorm⟩ := d.linear_endpoint_of_source_cover h.toStandardSetup hE
    hfaith hUC hV hA hcover
  exact isJanko1Type_of_linear_endpoint h e hfaith hconj hUC
    h.toStandardSetup.centralizer_z_le hnorm
    (h.toStandardSetup.cyclic_commutingSylow_centralizer hE)

/-- The local conclusion of Proposition 16.5.1, from the source Bender
quotient and the standard Δ₀ setup. All cyclic-actor, moving-conjugator,
Goldschmidt–O'Nan, unitary-exclusion and centralizer obligations are discharged.
The explicit inputs are precisely the earlier cover, 16.4.2(4), 16.4.6,
16.4.8, 16.4.10 results and GLS96 C.14.2 on actual normalizer representations.
The parent supplies these earlier theorems; global J₁ recognition is separate. -/
theorem isJanko1Type_of_bender_source_quotient
    {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (h : IntersectionSetup T z L g R)
    (hdelta : (centralizer (L : Set G)).conjBy g ∈ deltaZero L)
    (hb : ClassificationModels.IsBenderModel (L ⧸ pCore 2 L))
    (hcover : center L ≠ ⊥ →
      CoverAndSylowElimination.SuzukiCoverInput T L ∧ Nat.card (center L) ≤ 4)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (h1646 : GeometryConstruction.WeakClosure.SmallLinear.FiveOuterPGLExclusion T z L)
    (h1648 : ∀ n : ℕ, 2 ≤ n →
      ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n) →
      ∀ u ∈ R, orderOf u = 2 →
        involutionTwoResidual L u ≤ L.conjBy g ∨
          (n ≠ 3 ∧ (pResidual 3 (involutionTwoResidual L u)).map
            (involutionTwoResidual L u).subtype ≤ L.conjBy g))
    (honan : ∀ (V : Subgroup G) [IsElementaryAbelian 2 V]
      (Y : Subgroup (ActionImage V)),
      Representation.GoldschmidtONan.Input (normalizerRepresentation V) Y →
        Representation.GoldschmidtONan.Alternatives (normalizerRepresentation V) Y) :
    IsJanko1Type G := by
  obtain ⟨n, ⟨d⟩⟩ := GeometryConstruction.exists_geometry_of_source_quotient
    hG h hdelta hb hcover hR htransport h1646 h1648
  let := d.elementary
  apply d.isJanko1Type_of_onan_alternatives h hG.evenType
    (h.eq_conjugate_commutingSylow hR htransport)
    (fun hc => (hcover hc).1.quotient_model)
  exact honan (benderSpace T L) (inducedActor (benderSpace T L) d.actor)
    (d.onanInput h.toStandardSetup)

end CFSG.Quasithin.Chapter16.Intersections.Bender

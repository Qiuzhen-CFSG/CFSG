module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion

/-!
# The original Mathieu witness and AS91 Todd fusion calculations

The same original `sourceOrbit_m24_isTypeJ4` witness supplies the central
marker. Its unchanged earlier `LocalData` selects the Todd representative
and gives the two orbits, ambient nonfusion and the actual C_M(t)/E quotient.
The exact conditional (6.2)(3), including its standing marker-class premise,
gives pure second-class intersections of order at most four. The constructed
coordinate triangle supplies a pair plane whose literal normalizer quotient
has two-rank at most four. Projected involutions fix 128 elements of the
original radical, and larger radical subgroups have no escaping normalizer
inside the second centralizer. The first fixed-coset argument gives each such
proper overgroup a unique fixed coset of the original relative normalizer.

The second fixed-coset argument now supplies the full centralizer
C_G(t)=C_M(t) and uniqueness of the conjugate radical containing t.
The incidence theorem now supplies the exact intersection premise on this
same LocalData. Four explicit Todd lifts cover the involutions outside E;
their original quotient images and orders are retained. Together with z and t,
they give six representatives in C_G(z) joined with M, with conjugators in
that join. The four lifts now fuse into the original plane core Q. The two
core orbits give two-class fusion in the join with actual conjugators. Full
involution centralizers and fusion control establish ambient generation by
the source strong-embedding argument. The final application discharges the
intersection premise using the incidence theorem on this same LocalData.

Source: Aschbacher–Segev (1991), (6.3)–(6.5), p.602; Aschbacher–Smith 8.2.12–14,
printed pp.722–723, for the original Mathieu recognition consumer.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The two Todd orbits, centralizer quotient and conditional radical-intersection
bound for the literal original Mathieu witness and all its original arguments. -/
theorem sourceOrbit_m24_todd_fusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
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
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    (hi : SourceFusion.MarkerIntersection data) :
    SourceFusion.second data ∈ data.P.E ∧ orderOf (SourceFusion.second data) = 2 ∧
    ¬ IsConj (z : G) (SourceFusion.second data) ∧
    (∀ u ∈ data.P.E, u ≠ 1 →
      (∃ m ∈ data.P.M, MulAut.conj m (z : G) = u) ∨
      ∃ m ∈ data.P.M, MulAut.conj m (SourceFusion.second data) = u) ∧
    Nonempty ((SourceFusion.secondCentralizer data ⧸
      data.P.E.subgroupOf (SourceFusion.secondCentralizer data)) ≃* MulAut M22) ∧
    primeRank 2 (SourceFusion.secondCentralizer data ⧸
      data.P.E.subgroupOf (SourceFusion.secondCentralizer data)) ≤ 5 ∧
    (∀ g : G, g ∈ Recognition.JankoFour.centralizer (SourceFusion.second data) →
      g ∉ data.P.M →
      Nat.card (data.P.E ⊓ data.P.E.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 4 ∧
      ∀ u ∈ data.P.E ⊓ data.P.E.map (MulAut.conj g).toMonoidHom, u ≠ 1 →
        ∃ m ∈ data.P.M, MulAut.conj m (SourceFusion.second data) = u) :=
  SourceFusion.todd_fusion_consequences data hi

/-- The constructed pair plane, its original normalizer quotient and radical
centralizers, and the larger-subgroup normalizer barrier for the same Mathieu
witness. No plane-existence, rank, or centralizer premise is added. -/
theorem sourceOrbit_m24_pair_plane_normalizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
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
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    (hi : SourceFusion.MarkerIntersection data) :
    SourceFusion.secondPlane data ≤ data.P.E ∧
    SourceFusion.second data ∈ SourceFusion.secondPlane data ∧
    Nat.card (SourceFusion.secondPlane data) = 4 ∧
    (∀ u ∈ SourceFusion.secondPlane data, u ≠ 1 →
      ∃ m ∈ data.P.M, MulAut.conj m (SourceFusion.second data) = u) ∧
    data.P.E ≤ SourceFusion.pairNormalizer data (SourceFusion.secondPlane data) ∧
    primeRank 2 (SourceFusion.pairNormalizer data (SourceFusion.secondPlane data) ⧸
      data.P.E.subgroupOf (SourceFusion.pairNormalizer data (SourceFusion.secondPlane data))) ≤ 4 ∧
    (∀ m : SourceFusion.pairNormalizer data (SourceFusion.secondPlane data),
      orderOf (SourceFusion.pairNormalizerProjection data (SourceFusion.secondPlane data) m) = 2 →
      Nat.card (data.P.E ⊓ Recognition.JankoFour.centralizer (m : G) : Subgroup G) = 128) ∧
    (∀ V : Subgroup G, SourceFusion.secondPlane data < V → V ≤ data.P.E →
      normalizer (V : Set G) ⊓ Recognition.JankoFour.centralizer (SourceFusion.second data) ≤
        SourceFusion.secondCentralizer data) :=
  SourceFusion.secondPlane_normalizer_facts data hi

/-- The first actual fixed-coset argument on the original Mathieu witness,
conditional only on its unchanged LocalData and exact earlier intersection premise. -/
theorem sourceOrbit_m24_pair_plane_fixed_cosets
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
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
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    (hi : SourceFusion.MarkerIntersection data) :
    ∀ V : Subgroup G, SourceFusion.secondPlane data < V → V ≤ data.P.E →
      ∃! q : SourceFusion.pairAmbientNormalizer data ⧸
          data.P.M.subgroupOf (SourceFusion.pairAmbientNormalizer data),
        ∀ v : V.subgroupOf (SourceFusion.pairAmbientNormalizer data),
          (v : SourceFusion.pairAmbientNormalizer data) • q = q :=
  fun V hUV hVE => SourceFusion.pairPlane_overgroup_unique_fixed_coset data hi V hUV hVE

/-- AS91 (6.3)(3) on the literal original Mathieu recognition witness:
full ambient centralizer containment and uniqueness of the conjugate radical.
Only the same LocalData and exact earlier (6.2)(3) are supplied. -/
theorem sourceOrbit_m24_full_second_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
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
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    (hi : SourceFusion.MarkerIntersection data) :
    Recognition.JankoFour.centralizer (SourceFusion.second data) ≤ data.P.M ∧
    Recognition.JankoFour.centralizer (SourceFusion.second data) =
      SourceFusion.secondCentralizer data ∧
    (∀ g : G, SourceFusion.second data ∈ data.P.E.map (MulAut.conj g).toMonoidHom →
      data.P.E.map (MulAut.conj g).toMonoidHom = data.P.E) :=
  SourceFusion.second_centralizer_consequences data hi

/-- The same Mathieu witness supplies the exact earlier intersection theorem.
Its second centralizer is therefore unconditional on that theorem, and all
involutions in the original centralizer-point join have six explicit
representatives with conjugators in the join. The four outside-radical
representatives retain the original Todd projection and are actual involutions.
Their remaining fusion into the plane core is not assumed. -/
theorem sourceOrbit_m24_involution_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
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
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    :
    (Recognition.JankoFour.centralizer (SourceFusion.second data) ≤ data.P.M ∧
      Recognition.JankoFour.centralizer (SourceFusion.second data) =
        SourceFusion.secondCentralizer data ∧
      ∀ g : G, SourceFusion.second data ∈ data.P.E.map (MulAut.conj g).toMonoidHom →
        data.P.E.map (MulAut.conj g).toMonoidHom = data.P.E) ∧
    (∀ b e : Bool, SourceFusion.pointLift data b e ∈ data.P.M ∧
      orderOf (SourceFusion.pointLift data b e) = 2 ∧
      SourceFusion.pointLift data b e ∉ data.P.E ∧
      data.P.projection ⟨SourceFusion.pointLift data b e,SourceFusion.pointLift_mem data b e⟩ =
        if b then M24InvolutionCentralizers.involution2A else M24InvolutionCentralizers.involution2B) ∧
    (∀ u : G, u ∈ Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M → orderOf u = 2 →
      (∃ k ∈ Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M,
        MulAut.conj k (z : G) = u) ∨
      (∃ k ∈ Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M,
        MulAut.conj k (SourceFusion.second data) = u) ∨
      ∃ b e : Bool, ∃ k ∈ Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M,
        MulAut.conj k (SourceFusion.pointLift data b e) = u) :=
  ⟨SourceFusion.second_centralizer_consequences data data.source_six_two_three_map,
    (fun b e => ⟨SourceFusion.pointLift_mem data b e,SourceFusion.pointLift_order data b e,
      SourceFusion.pointLift_not_mem_radical data b e,SourceFusion.pointLift_projection data b e⟩),
    SourceFusion.join_involution_representatives data⟩

/-- Complete AS91 (6.3)–(6.5)(2) consequences for the literal original
Mathieu witness. The same LocalData supplies the earlier intersection theorem;
all fusion conjugators remain in the original centralizer-point join. -/
theorem sourceOrbit_m24_fusion_generation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
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
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    :
    (¬ IsConj (z : G) (SourceFusion.second data) ∧
      ∀ u : G, orderOf u = 2 →
        IsConj (z : G) u ∨ IsConj (SourceFusion.second data) u) ∧
    (Recognition.JankoFour.centralizer (SourceFusion.second data) ≤ data.P.M ∧
      Recognition.JankoFour.centralizer (SourceFusion.second data) =
        SourceFusion.secondCentralizer data ∧
      ∀ g : G, SourceFusion.second data ∈ data.P.E.map (MulAut.conj g).toMonoidHom →
        data.P.E.map (MulAut.conj g).toMonoidHom = data.P.E) ∧
    (∀ u : G, u ∈ Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M → orderOf u = 2 →
      (∃ k ∈ Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M,
        MulAut.conj k (z : G) = u) ∨
      ∃ k ∈ Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M,
        MulAut.conj k (SourceFusion.second data) = u) ∧
    (∀ u : G, u ∈ Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M → orderOf u = 2 →
      Recognition.JankoFour.centralizer u ≤ Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M) ∧
    (∀ x y : G, x ∈ Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M →
      y ∈ Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M →
      orderOf x = 2 → IsConj x y →
      ∃ k ∈ Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M, MulAut.conj k x = y) ∧
    Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M = ⊤ :=
  ⟨SourceFusion.involution_classes data,
    SourceFusion.second_centralizer_consequences data data.source_six_two_three_map,
    SourceFusion.join_involution_fusion data,
    SourceFusion.join_centralizer_le data data.source_six_two_three_map,
    SourceFusion.join_controls_involution_fusion data data.source_six_two_three_map,
    SourceFusion.generate data data.source_six_two_three_map⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

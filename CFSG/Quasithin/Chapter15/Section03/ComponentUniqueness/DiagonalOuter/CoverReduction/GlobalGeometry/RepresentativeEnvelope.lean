module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.NormalizerEligibility
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.OddCoreUpgrade
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Components

/-!
# The component containing L in the representative centralizer

The full normalizer equality makes C_{C_G(v)}(V₁) normalize L. The actual
center identity puts L in that centralizer; its quasisimplicity and trivial
odd core make it a local 2-component. Applying the precise earlier I.3.1(3)
input constructs an ordinary, relatively normal component containing L.

The fixed-line adapter transports source 15.3.6(3) to C_G(v). Local-family
membership comes from the original outside overgroup, and SQTK follows from
v being an involution. Thus 1.2.4 applies, and its uniqueness attaches the
actual A.3.12 quotient embedding to the component constructed by balance.
`RepresentativeIdentification` resolves that embedding, including the M₂₃
multiplier case, using the marked cover.
No outside-family hypothesis is imposed on C_G(v).

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, I.3.1(3) on
printed pp.414--415, 1.2.4 on p.505, 15.3.6(3) on p.1122, and p.1136.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
open Chapter1 Chapter1.Section02
universe u
variable {G : Type u} [Group G]

/-- The rank-two conclusion of I.3.1(3), with its actual containing component.
This is an earlier theorem input; the SQTK and local 2-component hypotheses
must be proved before it can be applied. -/
def EarlierRankTwoBalance (κ : GroupClass.{u}) : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsSQTK κ H →
    ∀ (P : Subgroup H), IsPGroup 2 P →
    ∀ (B : Subgroup (centralizer (P : Set H))), IsTwoComponent B →
      primeRank 3 B = 2 → ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
        B.map (centralizer (P : Set H)).subtype ≤ K

private theorem sqtk_quotient_twoCore [Finite G] {κ : GroupClass.{u}}
    (h : IsSQTK κ G) : IsSQTK κ (G ⧸ pCore 2 G) := by
  refine ⟨?_, h.isKGroup.quotient _⟩
  intro p hp ho
  let _ : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (h.stronglyQuasithin p hp ho)

/-- Balance makes the containing subgroup ordinary, while 1.2.4 attaches
its actual A.3.12 quotient embedding. The Sylow input is the earlier
15.3.6(3) for the fixed-line centralizer, not outside-family membership. -/
theorem representative_component_envelope [Finite G] {κ : GroupClass.{u}}
    (earlier : EarlierEmbeddings κ) (balance : EarlierRankTwoBalance κ)
    (hG : IsSimpleQTKE κ G)
    (I L V S : Subgroup G) [IsKleinFour V] [IsQuasisimple L]
    (hI : I = normalizer (V : Set G))
    (hIL : I ≤ normalizer (L : Set G))
    (hZ : (center L).map L.subtype = V)
    (hoL : pPrimeCore 2 L = ⊥) (hrank : primeRank 3 L = 2)
    (hlocal : L ∈ Chapter1.L G S)
    (v : G) (hv : v ∈ V) (hv2 : orderOf v = 2)
    (P : Sylow 2 (centralizer ({v} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({v} : Set G)).subtype = S) :
    let H := centralizer ({v} : Set G)
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧ L ≤ K.map H.subtype ∧
      A312Embedding ((L.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
        (K.map (QuotientGroup.mk' (pCore 2 H))) := by
  let H := centralizer ({v} : Set G)
  have hH := hG.involution_centralizer_sqtk hv2
  have hVH : V ≤ H := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm
        (⟨w, hw⟩ : V) ⟨v, hv⟩))
  have hLC : L ≤ centralizer (V : Set G) := by
    intro l hl w hw
    obtain ⟨z, hz, he⟩ := mem_map.mp (hZ.symm ▸ hw)
    have hc := congrArg Subtype.val (mem_center_iff.mp hz ⟨l, hl⟩)
    change (z : G) = w at he
    change l * (z : G) = (z : G) * l at hc
    rw [he] at hc
    exact hc.symm
  have hLH : L ≤ H := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hLC hl v hv).symm
  let A := L.subgroupOf H
  let Q := V.subgroupOf H
  let C := centralizer (Q : Set H)
  have hAC : A ≤ C := by
    intro a ha w hw
    exact Subtype.ext (hLC ha w hw)
  have hCI : C ≤ I.subgroupOf H := by
    intro a ha
    rw [hI]
    apply Subgroup.centralizer_le_normalizer
    intro w hw
    exact congrArg Subtype.val (ha ⟨w, hVH hw⟩ hw)
  have hCA : C ≤ normalizer (A : Set H) := by
    intro a ha
    apply mem_normalizer_iff.mpr
    intro l
    exact mem_normalizer_iff.mp (hIL (hCI ha)) l
  let B := A.subgroupOf C
  let e : B ≃* L := (subgroupOfEquivOfLe hAC).trans (subgroupOfEquivOfLe hLH)
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e.symm
  let : B.Normal := normal_subgroupOf_of_le_normalizer hCA
  have hcomp : IsComponent C B := ⟨(inferInstance : B.Normal).isSubnormal, inferInstance⟩
  have hoB : pPrimeCore 2 B = ⊥ := by
    apply ((pPrimeCore 2 B).map_eq_bot_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [pPrimeCore_map_iso, hoL]
  have htwo : IsTwoComponent B := by
    refine ⟨component_isCComponent hcomp, ?_⟩
    exact IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hoB).trans (QuotientGroup.quotientBot (G := B))).symm
  have hQ : IsPGroup 2 Q :=
    (IsPGroup.of_card (n := 2) (show Nat.card V = 2 ^ 2 by
      rw [IsKleinFour.card_four]; decide)).comap_subtype
  obtain ⟨K, hK, hn, hBK⟩ := balance H hH Q hQ B htwo
    ((primeRank_congr 3 e).trans hrank)
  have hAK : A ≤ K := by
    change (A.subgroupOf C).map C.subtype ≤ K at hBK
    rwa [map_subgroupOf_eq_of_le hAC] at hBK
  have hSH : S ≤ H := hP ▸ map_subtype_le _
  have hAP : A ∈ Chapter1.L H (P : Subgroup H) := by
    have he : S.subgroupOf H = (P : Subgroup H) := by
      rw [← hP, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
    rw [← he]
    exact (mem_LIn_iff_subgroupOf hSH hLH).mp ⟨hLH, hlocal⟩
  obtain ⟨K₁, hK₁, hAK₁, huniq, hemb, _⟩ :=
    lemma_1_2_4_of_A_3_12_A_3_8 earlier.a312 earlier.a38
      (sqtk_quotient_twoCore hH) P hAP
  have he : K = K₁ := huniq K (component_isCComponent hK) hAK
  refine ⟨K, hK, hn, ?_, he.symm ▸ hemb⟩
  simpa only [A, map_subgroupOf_eq_of_le hLH] using map_mono (f := H.subtype) hAK

/-- The source fixed-subgroup Sylow conclusion 15.3.6(3) applies to the
centralizer of the chosen generator because its cyclic group is that line. -/
theorem representative_sylow_of_fixed_line
    (V W ZS S : Subgroup G) (hWV : W ≤ V)
    (hZS : ZS = fixedPlane V S) (v : G) (hgen : zpowers v = ZS ⊓ W)
    (hS : IsSylowIn 2 S (centralizer (fixedPlane W S : Set G))) :
    IsSylowIn 2 S (centralizer ({v} : Set G)) := by
  have he : fixedPlane W S = ZS ⊓ W := by
    rw [hZS]
    ext x
    exact ⟨fun h => ⟨⟨hWV h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  have hc : centralizer (fixedPlane W S : Set G) = centralizer ({v} : Set G) := by
    rw [he, ← hgen, zpowers_eq_closure, centralizer_closure]
  exact hc ▸ hS

/-- Supply the local-family and odd-core hypotheses from the original eligible
outside overgroup. No outside-family assertion is made about C_G(v). -/
theorem representative_envelope_of_outside [Finite G] {κ : GroupClass.{u}}
    (earlier : EarlierEmbeddings κ) (balance : EarlierRankTwoBalance κ)
    (hG : IsSimpleQTKE κ G)
    {Yplus M I L V S : Subgroup G} [IsKleinFour V]
    (houtside : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥)
    (hI : I = normalizer (V : Set G))
    (hIL : I ≤ normalizer (L : Set G))
    (hZ : (center L).map L.subtype = V) (hrank : primeRank 3 L = 2)
    (v : G) (hv : v ∈ V) (hv2 : orderOf v = 2)
    (hS : IsSylowIn 2 S (centralizer ({v} : Set G))) :
    let H := centralizer ({v} : Set G)
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧ L ≤ K.map H.subtype ∧
      A312Embedding ((L.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
        (K.map (QuotientGroup.mk' (pCore 2 H))) := by
  let e := subgroupOfEquivOfLe hLI
  let : IsQuasisimple (L.subgroupOf I) := hL.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e
  have ho : pPrimeCore 2 L = ⊥ := by
    rw [← pPrimeCore_map_iso 2 e, component_oddCore_eq_bot hL hodd, Subgroup.map_bot]
  obtain ⟨P, hP⟩ := hS
  exact representative_component_envelope earlier balance hG I L V S hI hIL hZ ho hrank
    (mem_L_of_cComponent houtside.1.1 (hSylow I houtside) hLI
      (component_isCComponent hL)) v hv hv2 P hP

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry

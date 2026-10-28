module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.LinearCore
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.Original
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.WeakAction
/-!
# The no-TI odd linear source bound above characteristic three

The actual image of V in H/J has order two: the large odd linear core
calculation bounds it by two, and the original outside-core hypothesis makes
it nontrivial. Its original dihedral pair therefore supplies the weak cubic
bound on every Sylow overgroup normalizing V, with the actual action retained.

The prime-three row is intentionally separate. Its graph-extension maximal
subgroup has a Sylow-normal elementary four-group in its two-core, so the
printed cyclicity shortcut on p.219 does not apply there.
Source: Aschbacher--Smith E.2.7--13, printed pp.219--225.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.OddDegreeThree
variable {H : Type*} [Group H] [Finite H]

/-- The original dihedral witness, without TI, for primes above three. -/
theorem source_original_of_three_lt
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hp3:3<p)
    (hm:ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p)
    (V:Subgroup H) [IsElementaryAbelian 2 V] (hVT:V≤T)
    (hvn:(V.subgroupOf (T:Subgroup H)).Normal)
    (hVM:V≤(ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout:¬V≤ChapterB.minimalParabolicCore T hP) :
    Nonempty (Solvable.Witness T (ChapterB.minimalParabolicMax T hP) V) := by
  let J:=ChapterB.minimalParabolicCore T hP
  let M:=ChapterB.minimalParabolicMax T hP
  let q:=QuotientGroup.mk' J
  let S:=T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W:=V.map q
  let D:=K.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  let : Fact p.Prime := ⟨hp⟩
  have hi:=Structure.source_normal_simple_image T hP hs K hK hgen
  have hmin:ChapterB.IsMinimalParabolicOver S ⊤ := (Structure.source_star_minimal_core_free T hP).1
  have hcore:ChapterB.minimalParabolicCore S hmin=⊥ := (Structure.source_star_minimal_core_free T hP).2
  have hO:pCore 2 (H⧸J)=⊥ := bot_unique ((ChapterB.minimalParabolicTwoCore_le_core S hmin).trans hcore.le)
  have hmax:ChapterB.minimalParabolicMax S hmin=M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  let : D.Normal := hi.2.2.1
  let : IsSimpleGroup D := hi.1
  have hc:Nat.card W≤2 := Structure.OddDegreeThree.linear_image_card_le_two_of_three_lt
    M V hVM q S hmin D hi.2.2.2 hO hp ho hp3 hm hmax.symm
  have hne:W≠⊥ := by
    intro hh
    have hle := (map_eq_bot_iff V).mp hh
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using hle)
  have htwo:Nat.card W=2 := by
    have := (one_lt_card_iff_ne_bot W).mpr hne
    omega
  exact Involution.source_star_order_two T hP V hVT hvn hVM htwo


/-- E.2.13 for the actual odd PSL₃ row above characteristic three. -/
theorem source_cubicRatio_le_two_of_three_lt
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : 3 < p)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p)
    (V U : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) ≤ 2 := by
  obtain ⟨w⟩ := source_original_of_three_lt T hP hs K hK hgen hp ho hp3 hm
    V hVT hvn hVM hout
  exact BenderPlacement.original_witness_cubicRatio_le_two hP hVT hvn hVM hout hfit
    (BenderPlacement.OriginalWitness.of_dihedral (n := 1) w) hTU hU

end CFSG.Quasithin.ChapterE.Witnesses.OddDegreeThree

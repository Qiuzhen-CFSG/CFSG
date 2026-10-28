module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ThirdSpaceAction
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalNormality
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.GroupTheory.SylowNormalizedResidual
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The original A₅ Borel in the normal-pair construction

The marked point centralizer maps onto the four-letter stabilizer in A₅,
so it has index five in L. It contains the actual Sylow intersection T ∩ L.
Rank-one maximality therefore identifies it with N_L(T ∩ L). The residual
and Sylow supplement then give B_L T = L₁ T.

The final theorem applies these identities to the literal F.1.1 pair (I,L,T):
its common Borel is L₁T and its parabolics are H and LT. The supplied I-Borel
and generation identities are the outputs of the original symmetric-three
pair construction; no marked-amalgam classification is assumed or asserted.

Source: Aschbacher–Smith, 13.5.17, printed p.922, and Hypothesis F.1.1,
printed p.259. All conclusions retain the original source Context.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open Section06.CentralizerReduction Section06.TerminalContradiction.Ratio
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The original A₅ quotient is the rank-one model PSL₂(4). -/
theorem quotient_rankOneModel : ChapterF.Source.IsRankOneModel (L ⧸ pCore 2 L) := by
  apply ChapterF.Source.IsRankOneModel.linear 2 (by decide)
  have hF : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    decide
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  exact ⟨GaloisField 2 2,inferInstance,inferInstance,hF,⟨d.quotient.trans e.symm⟩⟩

/-- The original Sylow intersection, with its literal ambient inclusion. -/
theorem local_sylow : ∃ S : Sylow 2 L,
    (S : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
  let M := L ⊔ (T : Subgroup G)
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer d.normalizes_L)
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)).exists_subgroupOf_eq_of_normal
    (L.subgroupOf M)
  let e := subgroupOfEquivOfLe (show L ≤ M from le_sup_left)
  let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨S,?_⟩
  change ((P : Subgroup (L.subgroupOf M)).map e.toMonoidHom).map L.subtype = _
  rw [hP]
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨hz,z.property⟩
  · rintro ⟨hxT,hxL⟩
    exact ⟨⟨x,hxL⟩,⟨⟨⟨x,show x∈M from (le_sup_left : L ≤ M) hxL⟩,hxL⟩,hxT,rfl⟩,rfl⟩

/-- The chosen central line has its original orbit of length five. -/
theorem point_centralizer_relIndex :
    (L ⊓ centralizer (V₁ : Set G)).relIndex L = 5 := by
  obtain ⟨s,hz,_⟩ := d.third_coordinates
  have he : (L ⊓ centralizer (V₁ : Set G)).subgroupOf L =
      AlternatingFiveBorel.B.comap s.action := by
    ext l
    change ((l:G) ∈ L ∧ (l:G) ∈ centralizer (V₁ : Set G)) ↔
      s.action l ∈ AlternatingFiveBorel.B
    constructor
    · intro hl
      exact (ThirdSpace.centralizerAction s hz ⟨l,hl⟩).property
    · intro hl
      refine ⟨l.property,?_⟩
      have hf := s.equivariant l z
      rw [(AlternatingFiveFlag.fixes_z_iff _).mpr hl] at hf
      have hz' : zpowers (s.map (Multiplicative.ofAdd z)) = V₁ := by
        simpa only [MonoidHom.map_zpowers] using hz
      have hfix : V₁ ≤ centralizer ({(l:G)} : Set G) := by
        rw [←hz']
        apply zpowers_le.mpr
        exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hf).symm
      exact fun x hx => mem_centralizer_singleton_iff.mp (hfix hx)
  change ((L ⊓ centralizer (V₁ : Set G)).subgroupOf L).index = 5
  rw [he,index_comap_of_surjective _ s.onto]
  have hc : Nat.card AlternatingFiveBorel.B = 12 := by
    rw [←Nat.card_congr AlternatingFiveBorel.marking.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hi := AlternatingFiveBorel.B.card_mul_index
  rw [hc,nat_card_alternatingGroup] at hi
  norm_num [Nat.factorial] at hi
  omega

/-- The local F.1.1 Borel is the original point centralizer inside L. -/
theorem borel_eq_point_centralizer :
    ChapterF.Source.borel L (T : Subgroup G) = L ⊓ centralizer (V₁ : Set G) := by
  obtain ⟨S,hS⟩ := d.local_sylow
  have hB := ChapterF.Source.rankOneBorelFacts_of_sylow L (T : Subgroup G) S hS
    (ChapterF.Source.rankOneSylowFacts_of_rankOneQuotient d.quotient_rankOneModel S)
  have hTC : (T : Subgroup G) ≤ centralizer (V₁ : Set G) :=
    d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two _ d.flag.one_card)
  have hCL : L ⊓ centralizer (V₁ : Set G) < L := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro he
    have hi := d.point_centralizer_relIndex
    rw [he,relIndex_self] at hi
    contradiction
  have hCB := hB.unique_maximal _ (le_inf inf_le_right (inf_le_left.trans hTC)) hCL
  have hm := relIndex_mul_relIndex (L ⊓ centralizer (V₁ : Set G))
    (ChapterF.Source.borel L (T : Subgroup G)) L hCB hB.proper.le
  rw [d.point_centralizer_relIndex] at hm
  have hd : (L ⊓ centralizer (V₁ : Set G)).relIndex
      (ChapterF.Source.borel L (T : Subgroup G)) ∣ 5 := ⟨_,hm.symm⟩
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
  · exact le_antisymm (relIndex_eq_one.mp h) hCB
  · rw [h] at hm
    have hBL : (ChapterF.Source.borel L (T : Subgroup G)).relIndex L = 1 := by omega
    exact (hB.proper.not_ge (relIndex_eq_one.mp hBL)).elim

/-- The common Sylow supplement converts the point centralizer to its residual. -/
theorem borel_sup_sylow_eq_residual_sup_sylow :
    ChapterF.Source.borel L (T : Subgroup G) ⊔ (T : Subgroup G) =
      residualCentralizer L V₁ ⊔ (T : Subgroup G) := by
  rw [d.borel_eq_point_centralizer]
  apply le_antisymm
  · apply sup_le ?_ le_sup_right
    exact le_embedded_pResidual_sup_sylow_of_normalizes T _
      (le_normalizer_inf d.normalizes_L
        (d.flag.one_invariant.trans (normalizer_le_normalizer_centralizer V₁)))
  · exact sup_le_sup ThirdSpace.residual_le_centralizer le_rfl

/-- The exact common Borel and the two original parabolics for 13.5.17's
F.1.1 application. The symmetric-three pair owner supplies `hI` and `hH`. -/
theorem source_pair_borel_parabolics {I H : Subgroup G}
    (hI : ChapterF.Source.borel I (T : Subgroup G) = (T : Subgroup G) ⊓ I)
    (hH : H = residualCentralizer L V₁ ⊔ I ⊔ (T : Subgroup G)) :
    ChapterF.Source.commonBorel ![I,L] (T : Subgroup G) =
        residualCentralizer L V₁ ⊔ (T : Subgroup G) ∧
      ChapterF.Source.parabolic ![I,L] (T : Subgroup G) 0 = H ∧
      ChapterF.Source.parabolic ![I,L] (T : Subgroup G) 1 = L ⊔ (T : Subgroup G) := by
  constructor
  · change (ChapterF.Source.borel I (T : Subgroup G) ⊔
      ChapterF.Source.borel L (T : Subgroup G)) ⊔ (T : Subgroup G) = _
    rw [hI,←d.borel_sup_sylow_eq_residual_sup_sylow]
    apply le_antisymm
    · exact sup_le (sup_le (inf_le_left.trans le_sup_right) le_sup_left) le_sup_right
    · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  constructor
  · change I ⊔ (T : Subgroup G) ⊔ ChapterF.Source.borel L (T : Subgroup G) = H
    calc
      _ = I ⊔ (ChapterF.Source.borel L (T : Subgroup G) ⊔ (T : Subgroup G)) := by ac_rfl
      _ = I ⊔ (residualCentralizer L V₁ ⊔ (T : Subgroup G)) := by
        rw [d.borel_sup_sylow_eq_residual_sup_sylow]
      _ = residualCentralizer L V₁ ⊔ I ⊔ (T : Subgroup G) := by ac_rfl
      _ = H := hH.symm
  · change (L ⊔ (T : Subgroup G)) ⊔ ChapterF.Source.borel I (T : Subgroup G) = _
    rw [hI]
    exact sup_eq_left.mpr (inf_le_left.trans le_sup_right)
end CFSG.Quasithin.Chapter13.Section05.A5Source.Context

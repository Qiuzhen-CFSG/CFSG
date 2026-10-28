module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticMiddleCoreProduct

/-!
# Excluding the original order-ten quintic quotient

In D10 every two-subgroup has order at most two.  The actual escaping
conjugate span therefore fills the image of the entire middle core.
Lifting with the full kernel gives a seed product whose intersection
commutator lies in the central line.  This contradicts the actual plane
commutator.  The original quotient is consequently Sz(2), without a
positive Suzuki parameter, a supplied profile, or an absolute core bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The full original quintic quotient is Sz(2); the dihedral alternative
is excluded by the actual critical middle-core commutator. -/
theorem source_quintic_suzuki_zero_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* DihedralGroup 5) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  classical
  have hno : ¬ Nonempty ((H ⧸ pCore 2 H) ≃* DihedralGroup 5) := by
    rintro ⟨eD⟩
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let V := localModule T M
    let Z := centralInvolutions T
    let U := conjugateSpanBy V H
    let Q := X.pCoreIn 2
    let QH := H.pCoreIn 2
    obtain ⟨g,hg,hDQ,hDne,hVI,hTI,hprod,hcommI,hfull⟩ :=
      source_quintic_middle_core_product hG T hempty hM hu hmany hcard e H hH hi
    let D := U.map (MulAut.conj g).toMonoidHom
    let I := U ⊓ D
    have hQT : Q ≤ (T : Subgroup G) :=
      (pCoreIn_le_sylow X (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right))).trans_eq
        (map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right))
    have hQH : Q ≤ H := hQT.trans hH.1.1.2
    let f : Q →* DihedralGroup 5 :=
      (eD.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))).comp (inclusion hQH)
    have hker : f.ker = QH.subgroupOf Q := by
      ext r
      change eD (QuotientGroup.mk (inclusion hQH r)) = 1 ↔ (r : G) ∈ QH
      rw [map_eq_one_iff _ eD.injective,QuotientGroup.eq_one_iff]
      change inclusion hQH r ∈ pCore 2 H ↔ (r : G) ∈ (pCore 2 H).map H.subtype
      constructor
      · intro hr; exact mem_map_of_mem H.subtype hr
      · rintro ⟨a,ha,he⟩
        exact (Subtype.ext he : a = inclusion hQH r) ▸ ha
    have hp : IsPGroup 2 Q := pCore_isPGroup.map X.subtype
    have hR : Nat.card f.range ≤ 2 := by
      obtain ⟨P,hP⟩ := (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
      have hPc : Nat.card P = 2 := by rw [P.card_eq_multiplicity,DihedralGroup.nat_card]; decide +kernel
      exact (card_le_of_le hP).trans_eq hPc
    have hDcard : 2 ≤ Nat.card ((D.subgroupOf Q).map f) := by
      have hpos := Nat.card_pos (α := (D.subgroupOf Q).map f)
      have hne : Nat.card ((D.subgroupOf Q).map f) ≠ 1 := by
        intro he
        have hh : D.subgroupOf Q ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp (card_eq_one.mp he)
        rw [hker] at hh
        apply hDne
        intro d hd
        exact hh (show (⟨d,hDQ hd⟩ : Q) ∈ D.subgroupOf Q from hd)
      omega
    have hmap : (D.subgroupOf Q).map f = (⊤ : Subgroup Q).map f := by
      apply eq_of_le_of_card_ge (map_mono le_top)
      rw [←MonoidHom.range_eq_map]
      exact hR.trans hDcard
    have htop : D.subgroupOf Q ⊔ f.ker = ⊤ :=
      top_unique (Subgroup.map_le_map_iff.mp hmap.ge)
    have hseed : Q = D ⊔ (QH ⊓ Q) := by
      rw [hker] at htop
      have hh := congrArg (Subgroup.map Q.subtype) htop
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show D ≤ Q from hDQ),
        subgroupOf_map_subtype,←MonoidHom.range_eq_map,range_subtype] at hh
      exact hh.symm
    have hZV : Z ≤ V := le_conjugateSpanBy _ _
    have hQcV : Q ≤ centralizer (V : Set G) := by
      have hh := (Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e).1
      exact hh.le.trans inf_le_right
    have hQZ : Q ≤ normalizer (Z : Set G) :=
      (hQcV.trans (centralizer_le hZV)).trans (Subgroup.centralizer_le_normalizer _)
    have hcomm : ⁅U,QH⁆ = Z :=
      (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2
    have hIQ : ⁅I,Q⁆ ≤ Z := by
      rw [hseed,commutator_comm]
      apply commutator_sup_le_of_relative_normal Q D (QH ⊓ Q) I Z hQZ hDQ inf_le_right
      · let : IsElementaryAbelian 2 U := (Section02.SolvableAmalgam.source_index_five_closure_structure
          hG T hempty hM hu hmany hcard e H hH.1 hi).1
        let : IsElementaryAbelian 2 D := IsElementaryAbelian.map _
        have hz : ⁅D,I⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
          ((le_centralizer (H := D)).trans (centralizer_le inf_le_right))
        exact hz.le.trans bot_le
      · rw [commutator_comm]
        exact (commutator_mono inf_le_left inf_le_left).trans hcomm.le
    have hVZ : V ≤ Z := hcommI.ge.trans hIQ
    have hc := card_le_of_le hVZ
    have hz := plane_centralInvolutions_card T M hM.1.2 hcard e
    change Nat.card V = 4 at hcard
    change Nat.card Z = 2 at hz
    omega
  exact ⟨hno,(Section02.SolvableAmalgam.source_index_five_models
    hG T hempty hM hu hmany hcard e H hH.1 hi).resolve_left hno⟩

end CFSG.Quasithin.Chapter14.Section06

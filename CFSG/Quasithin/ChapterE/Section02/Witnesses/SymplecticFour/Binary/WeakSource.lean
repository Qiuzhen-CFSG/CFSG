module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.Binary.Source
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.WeakAction
/-!
# The binary symplectic source bound without TI

The original binary witness splits into a dihedral pair or a marked Sp4(2)
pair. The dihedral pair gives the weak cubic estimate without TI; the marked
symplectic pair already gives a strict estimate. Thus the binary row in
E.2.13 needs no TI premise, as required in the outside-core qrc argument.

Source: Aschbacher--Smith E.2.13(3), printed pp.224--225, and 3.1.6,
printed pp.573--574.
-/
public section
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
variable {H : Type*} [Group H] [Finite H]
theorem source_cubicRatio_le_two (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (eK : K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2)))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) ≤ 2 := by
  rcases source_original T hP hs K hK hgen eK V hVT hn hVM hout with hb | ⟨w,ξ,S,hVS⟩
  · obtain ⟨w⟩ := hb
    exact BenderPlacement.original_witness_cubicRatio_le_two hP hVT hn hVM hout hfit w hTU hU
  · have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hn
    have hNV := minimalParabolic_normalizer_le T hP V
      (IsElementaryAbelian.isPGroup 2 V) hTV hout
    have hh := w.hypotheses hVT hTV hVM hNV
    have hp := w.proper_of_quotient_card_ne_one hNV (by
      rw [Nat.card_congr ξ.toEquiv,Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two]
      decide)
    let := DihedralCubic.centralizer_normal U V hU
    exact (DihedralCubic.ambient_cubic_actor_strict_symplectic_four_of_positive_exponent
      w.le hU hh (w.sylow_eq.le.trans (inf_le_left.trans hTU)) hp (w.fitting hTV hfit)
      1 (by decide) (by simp) ξ S hVS (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).2.2.2.2.2.le
end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary

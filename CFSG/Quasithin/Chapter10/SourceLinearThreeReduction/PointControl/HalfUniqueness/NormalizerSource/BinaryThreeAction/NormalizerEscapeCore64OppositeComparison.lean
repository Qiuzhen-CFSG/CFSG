module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCore64BaumannParabolic

/-!
# The actual Baumann parabolic versus the opposite source parabolic

The frozen full-core calculation supplies the literal Baumann parabolic
inside the original join.  The native wreath interval then identifies it
with one of the two original source parabolics.  The other source parabolic
is retained explicitly, together with the generated original join.

The comparison proved here is the part that is available without extending
the full-core action to `N_G(T₁)`: the intersection of that normalizer with
the original join lies in the actual Baumann parabolic and therefore
normalizes its literal two-residual.  The rank-twelve core containment from
the frozen theorem is carried along unchanged.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative

private theorem wreath_cover_pair_opposite {X : Type*} [Group X] [Finite X]
    (f : X →* Matrix.PSL3Two.WreathPair.Actor) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (S : Sylow 2 X) (A B H : Subgroup X)
    (hSA : (S : Subgroup X) ≤ A) (hSB : (S : Subgroup X) ≤ B)
    (hSH : (S : Subgroup X) ≤ H) (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hH : H ≠ ⊤)
    (hpA : ¬ IsPGroup 2 A) (hpB : ¬ IsPGroup 2 B) (hpH : ¬ IsPGroup 2 H)
    (hAB : A ≠ B) : H = A ∨ H = B := by
  let S' := S.mapSurjective hf
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Matrix.PSL3Two.WreathPair.Actor S'
    Matrix.PSL3Two.WreathPair.sylow
  let q := (MulAut.conj g).toMonoidHom.comp f
  have hq : Function.Surjective q := (MulAut.conj g).surjective.comp hf
  have hker : q.ker = f.ker := by
    ext x
    change (MulAut.conj g) (f x) = 1 ↔ f x = 1
    exact (MulAut.conj g).map_eq_one_iff
  have hqk : IsPGroup 2 q.ker := hker ▸ hk
  have hKS : q.ker ≤ (S : Subgroup X) := hqk.le_sylow_of_normal S
  have hS : (S : Subgroup X).map q = Matrix.PSL3Two.WreathPair.borel := by
    rw [show q = (MulAut.conj g).toMonoidHom.comp f from rfl,←map_map]
    exact (congrArg Sylow.toSubgroup hg).trans Matrix.PSL3Two.WreathPair.sylow_eq
  have pair (K : Subgroup X) (hSK : (S : Subgroup X) ≤ K)
      (hK : K ≠ ⊤) (hpK : ¬ IsPGroup 2 K) :
      K.map q = Matrix.PSL3Two.WreathPair.point ∨
        K.map q = Matrix.PSL3Two.WreathPair.line := by
    have hc : (K.map q).comap q = K := comap_map_eq_self (hKS.trans hSK)
    rcases Matrix.PSL3Two.WreathPair.overgroup_borel (K.map q)
      (hS ▸ map_mono hSK) with he | he | he | he
    · have ht : IsPGroup 2 (K.map q) := by
        rw [he,←Matrix.PSL3Two.WreathPair.sylow_eq]
        exact Matrix.PSL3Two.WreathPair.sylow.isPGroup'
      exact (hpK (hc ▸ ht.comap_of_ker_isPGroup q hqk)).elim
    · exact Or.inl he
    · exact Or.inr he
    · exact (hK (hc.symm.trans (by rw [he,comap_top]))).elim
  have inject (K M : Subgroup X) (hSK : (S : Subgroup X) ≤ K)
      (hSM : (S : Subgroup X) ≤ M) (he : K.map q = M.map q) : K = M := by
    rw [←comap_map_eq_self (hKS.trans hSK),←comap_map_eq_self (hKS.trans hSM),he]
  have ha := pair A hSA hA hpA
  have hb := pair B hSB hB hpB
  have hh := pair H hSH hH hpH
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hh with hh | hh
  all_goals first
    | exact (hAB (inject A B hSA hSB (ha.trans hb.symm))).elim
    | exact Or.inl (inject H A hSH hSA (hh.trans ha.symm))
    | exact Or.inr (inject H B hSH hSB (hh.trans hb.symm))

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 ChapterC.BinaryMS
namespace Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual Baumann parabolic is one of the two original parabolics; the
other one remains available for the source comparison.  The normalizer part
is deliberately restricted to its literal intersection with the original
join, where no extension of the full-core action is needed. -/
theorem normalizerEscape_fullCore64_baumann_opposite_comparison
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (hc : IsMulCommutative (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))))
    (hcard : Nat.card ((commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype) = 64) :
    let T₁ := (T : Subgroup G) ⊓ normalizer (L : Set G)
    let J := localJoin T L
    let H := J ⊓ normalizer (ChapterB.baumann T₁ : Set G)
    ∃ K : Subgroup G, Data D K ∧ K ≠ H ∧ H ⊔ K = J ∧
      (normalizer (T₁ : Set G) ⊓ J) ≤ normalizer (residual H : Set G) ∧
      ⁅J.pCoreIn 2,localOrbit T L⁆ ≤
        (normalizer (T₁ : Set G) ⊔ H).pCoreIn 2 := by
  let T₁ := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let J := localJoin T L
  let B := ChapterB.baumann T₁
  let H := J ⊓ normalizer (B : Set G)
  obtain ⟨hH,hU⟩ := normalizerEscape_fullCore64_baumann_parabolic D s hout hc hcard
  have hmodel : Selection.BinaryThreeNatural D := ⟨s.quotient,⟨s.natural⟩⟩
  have hzero : sourceMovedFixed D = ⊥ := moved_fixed_eq_bot s s.fixed_zero
  obtain ⟨A,K,hA,hK,hAK,hgen⟩ := exists_pair D hmodel hzero s.full_eq_local
    s.exchange_mem s.exchange_moves s.crossed
  let f := originalLift s s.fixed_zero
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hS : (S : Subgroup J).map J.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hHtwo : ¬ IsPGroup 2 H := by
    intro hp
    exact hH.sylow_maximal.ne (T.is_maximal' hp hH.sylow_le).symm
  have nonTwo (Q : Subgroup G) (hQ : Data D Q) : ¬ IsPGroup 2 Q := by
    intro hp
    exact hQ.sylow_maximal.ne (T.is_maximal' hp hQ.sylow_le).symm
  have proper (Q : Subgroup G) (hQ : Data D Q) : Q.subgroupOf J ≠ ⊤ :=
    hQ.maximal.ne_top
  have embed_ne {Q R : Subgroup G} (hQ : Q ≤ J) (hR : R ≤ J)
      (hne : Q ≠ R) : Q.subgroupOf J ≠ R.subgroupOf J := by
    intro he
    have hh := congrArg (map J.subtype) he
    rw [map_subgroupOf_eq_of_le hQ,map_subgroupOf_eq_of_le hR] at hh
    exact hne hh
  have not_two_subgroup (Q : Subgroup G) (hQ : Q ≤ J) (hp : ¬ IsPGroup 2 Q) :
      ¬ IsPGroup 2 (Q.subgroupOf J) := by
    intro hh
    have hm := hh.map J.subtype
    rw [map_subgroupOf_eq_of_le hQ] at hm
    exact hp hm
  have hpair := wreath_cover_pair_opposite f.hom f.surjective f.kernel_two S
    (A.subgroupOf J) (K.subgroupOf J) (H.subgroupOf J)
    (subgroupOf_mono J hA.sylow_le) (subgroupOf_mono J hK.sylow_le)
    (subgroupOf_mono J hH.sylow_le) (proper A hA) (proper K hK)
    (by
      intro he
      exact hH.maximal.ne_top he)
    (not_two_subgroup A hA.le_join (nonTwo A hA))
    (not_two_subgroup K hK.le_join (nonTwo K hK))
    (not_two_subgroup H hH.le_join hHtwo)
    (embed_ne hA.le_join hK.le_join hAK)
  have hNB : normalizer (T₁ : Set G) ≤ normalizer (B : Set G) :=
    normalizer_le_normalizer_baumann T₁
  have hNJ : normalizer (T₁ : Set G) ⊓ J ≤ H := by
    exact le_inf inf_le_right (inf_le_left.trans hNB)
  have hHN : H ≤ normalizer (residual H : Set G) := by
    have hn := (pResidual 2 H).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype,residual] using hn
  have hnorm : normalizer (T₁ : Set G) ⊓ J ≤ normalizer (residual H : Set G) :=
    hNJ.trans hHN
  have hopp : H = A ∨ H = K := by
    have hh : H.subgroupOf J = A.subgroupOf J ∨ H.subgroupOf J = K.subgroupOf J := hpair
    rcases hh with hh | hh
    · left
      have hh' := congrArg (map J.subtype) hh
      rw [map_subgroupOf_eq_of_le hH.le_join,
        map_subgroupOf_eq_of_le hA.le_join] at hh'
      exact hh'
    · right
      have hh' := congrArg (map J.subtype) hh
      rw [map_subgroupOf_eq_of_le hH.le_join,
        map_subgroupOf_eq_of_le hK.le_join] at hh'
      exact hh'
  rcases hopp with he | he
  · refine ⟨K,hK,?_,?_,hnorm,hU⟩
    intro hKH
    exact hAK (hKH.trans he).symm
    change H ⊔ K = J
    rw [he]
    simpa [J, sup_comm] using hgen
  · refine ⟨A,hA,?_,?_,hnorm,hU⟩
    intro hAH
    exact hAK (hAH.trans he)
    change H ⊔ A = J
    rw [he]
    simpa [J, sup_comm] using hgen

end Parabolics
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction

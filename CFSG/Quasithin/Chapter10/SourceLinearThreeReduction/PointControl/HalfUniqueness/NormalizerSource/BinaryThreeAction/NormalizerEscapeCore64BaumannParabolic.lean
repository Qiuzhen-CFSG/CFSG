module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCore64BaumannOvergroup
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeWreathParabolics

/-!
# The actual Baumann parabolic and the full rank12 core placement

The exhaustive Sylow interval in the literal wreath action identifies the
proper Baumann-normalizer overgroup with one of the two original source
parabolics. Its enlargement therefore has the full orbit movement in its
two-core, with all original parabolic data and the same T1 retained.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative

private theorem wreath_cover_pair {X : Type*} [Group X] [Finite X]
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
      K.map q = Matrix.PSL3Two.WreathPair.point ∨ K.map q = Matrix.PSL3Two.WreathPair.line := by
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
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- One of the two original parabolics is the actual Baumann-normalizer
intersection, and its actual normalizer enlargement absorbs the rank12 movement. -/
theorem normalizerEscape_fullCore64_baumann_parabolic
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (hc : IsMulCommutative (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))))
    (hcard : Nat.card ((commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype) = 64) :
    let T₁ := (T : Subgroup G) ⊓ normalizer (L : Set G)
    let H := localJoin T L ⊓ normalizer (ChapterB.baumann T₁ : Set G)
    Parabolics.Data D H ∧
      ⁅(localJoin T L).pCoreIn 2,localOrbit T L⁆ ≤
        (normalizer (T₁ : Set G) ⊔ H).pCoreIn 2 := by
  let T₁ := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let J := localJoin T L
  let H := J ⊓ normalizer (ChapterB.baumann T₁ : Set G)
  obtain ⟨hTH,hHJ,h3,hU⟩ := normalizerEscape_fullCore64_baumann_overgroup D s hout hc hcard
  have hmodel : Selection.BinaryThreeNatural D := ⟨s.quotient,⟨s.natural⟩⟩
  have hzero : sourceMovedFixed D = ⊥ := moved_fixed_eq_bot s s.fixed_zero
  obtain ⟨A,B,hA,hB,hAB,_⟩ := Parabolics.exists_pair D hmodel hzero s.full_eq_local
    s.exchange_mem s.exchange_moves s.crossed
  let f := originalLift s s.fixed_zero
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hS : (S : Subgroup J).map J.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hHtwo : ¬ IsPGroup 2 H := by
    intro hp
    obtain ⟨n,hn⟩ := (hp.to_le (show L ⊓ H ≤ H from inf_le_right)).exists_card_eq
    rw [hn] at h3
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h3)
  have nonTwo (K : Subgroup G) (hK : Parabolics.Data D K) : ¬ IsPGroup 2 K := by
    intro hp
    exact hK.sylow_maximal.ne (T.is_maximal' hp hK.sylow_le).symm
  have proper (K : Subgroup G) (hK : Parabolics.Data D K) : K.subgroupOf J ≠ ⊤ :=
    hK.maximal.ne_top
  have embed_ne {K M : Subgroup G} (hK : K ≤ J) (hM : M ≤ J)
      (hne : K ≠ M) : K.subgroupOf J ≠ M.subgroupOf J := by
    intro he
    have hh := congrArg (map J.subtype) he
    rw [map_subgroupOf_eq_of_le hK,map_subgroupOf_eq_of_le hM] at hh
    exact hne hh
  have not_two_subgroup (K : Subgroup G) (hK : K ≤ J) (hp : ¬ IsPGroup 2 K) :
      ¬ IsPGroup 2 (K.subgroupOf J) := by
    intro hh
    have hm := hh.map J.subtype
    rw [map_subgroupOf_eq_of_le hK] at hm
    exact hp hm
  have hpair := wreath_cover_pair f.hom f.surjective f.kernel_two S
    (A.subgroupOf J) (B.subgroupOf J) (H.subgroupOf J)
    (subgroupOf_mono J hA.sylow_le) (subgroupOf_mono J hB.sylow_le)
    (subgroupOf_mono J hTH) (proper A hA) (proper B hB)
    (by
      intro he
      have hh := congrArg (map J.subtype) he
      rw [map_subgroupOf_eq_of_le hHJ.le,←MonoidHom.range_eq_map,range_subtype] at hh
      exact hHJ.ne hh)
    (not_two_subgroup A hA.le_join (nonTwo A hA))
    (not_two_subgroup B hB.le_join (nonTwo B hB))
    (not_two_subgroup H hHJ.le hHtwo) (embed_ne hA.le_join hB.le_join hAB)
  refine ⟨?_,hU⟩
  rcases hpair with he | he
  · have hh := congrArg (map J.subtype) he
    rw [map_subgroupOf_eq_of_le hHJ.le,map_subgroupOf_eq_of_le hA.le_join] at hh
    exact hh.symm ▸ hA
  · have hh := congrArg (map J.subtype) he
    rw [map_subgroupOf_eq_of_le hHJ.le,map_subgroupOf_eq_of_le hB.le_join] at hh
    exact hh.symm ▸ hB

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction

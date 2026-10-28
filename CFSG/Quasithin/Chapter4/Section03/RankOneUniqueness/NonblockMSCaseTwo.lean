module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockLinearThreeAction
public import Theory.ThreeSubgroups

/-!
# A crossing exclusion for the doubled-natural MS branch

In C.1.34(2), the original full module is [Q,L]. Crossing preserves both
L and this full module, so Qᵗ fixes the image of L in K/O₂(K). When this
image is either actual SL₃ parabolic residual, its automorphism fixer is
trivial. Thus [Qᵗ,K] lies in O₂(K). The relative three-subgroups lemma and
perfectness of K lower it into [O₂(K),K]=Q, contradicting the source
crossing obstruction.

The proof does not need O₂(K)=Q or the Thompson-set description in C.1.36.
The two earlier inputs remain explicit: the common quotient/parabolic
marking and [Q,L]=W. Their construction in the nonbinary MS classification,
and final source assembly, remain with
qt-d-1222-rankone-uniqueness-nonblock. This is a conditional case exclusion,
not a construction of MSData.
Source: Aschbacher--Smith, original 4.3.10, printed pp.616--617;
C.1.34(2) and C.4.1(3), pp.136,151.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The doubled-natural branch's full commutator identity is incompatible
with the source crossing, once the literal L-image is a parabolic residual.
No equality Q=O₂(K), short-group hypothesis or Thompson-set classification
is needed. The module/quotient markings remain earlier source obligations. -/
theorem false_of_core_fullModule_and_parabolic
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : (c.K ⧸ pCore 2 c.K) ≃* SL(3,F))
    (he : c.componentQuotientL.map e.toMonoidHom = Matrix.PSL3.LinearThree.pointLocalSL F ∨
      c.componentQuotientL.map e.toMonoidHom = Matrix.PSL3.LinearThree.lineLocalSL F)
    (hfull : ⁅Q c,L⁆ = W c) : False := by
  let Q' := (Q c).map (MulAut.conj c.t⁻¹).toMonoidHom
  let f : c.K →* G := c.H.subtype.comp c.K.subtype
  have hfi : Function.Injective f := c.H.subtype_injective.comp c.K.subtype_injective
  have hQ : (ChapterC.blockU c.K).map f = Q c := by
    rw [core_eq_blockLayer, ←map_map]
  have hQ'H : Q' ≤ c.H := by
    have hs : (S c).map (MulAut.conj c.t⁻¹).toMonoidHom = S c :=
      mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (S c : Set G)).inv_mem c.crossing_normalizes)
    exact ((map_mono (f := (MulAut.conj c.t⁻¹).toMonoidHom)
      (core_le_sylow c)).trans_eq hs).trans inf_le_right
  have hlocal : ⁅Q',L⁆ ≤ Q c :=
    (crossing_core_fullModule c D hfull).le.trans (fullModule_lt_core c hf).le
  let : c.K.Normal := c.component_normal
  have hcore : ⁅Q',K c⁆ ≤ (K c).pCoreIn 2 := by
    apply commutator_le.mpr
    intro u hu k hk
    obtain ⟨k,hk,rfl⟩ := hk
    let z : c.K := ⟨k,hk⟩
    let a : MulAut c.K := MulAut.conjNormal (⟨u,hQ'H hu⟩ : c.H)
    have ha : (pCore 2 c.K).quotientAut a = 1 := by
      apply c.quotientAut_eq_one_of_parabolic_image hn hF e he
      rintro x ⟨w,hw,rfl⟩
      rw [quotientAut_apply_mk]
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hd : a w * w⁻¹ ∈ ChapterC.blockU c.K := by
        apply (mem_map_iff_mem hfi).mp
        rw [hQ]
        exact hlocal (commutator_mem_commutator hu hw)
      exact ChapterC.blockU_le_core (by simpa only [div_eq_mul_inv] using hd)
    have hz := DFunLike.congr_fun ha (QuotientGroup.mk' (pCore 2 c.K) z)
    rw [quotientAut_apply_mk] at hz
    have hzcore : a z * z⁻¹ ∈ pCore 2 c.K := by
      simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hz
    have hm : ⁅u,((k : c.H) : G)⁆ ∈ ((pCore 2 c.K).map c.K.subtype).map c.H.subtype :=
      ⟨_,⟨_,hzcore,rfl⟩,rfl⟩
    change ⁅u,((k : c.H) : G)⁆ ∈ (c.K.pCoreIn 2).map c.H.subtype at hm
    rwa [map_pCoreIn_of_injective 2 c.K c.H.subtype c.H.subtype_injective] at hm
  let : Group.IsPerfect c.K := c.component.perfect
  let : Group.IsPerfect (K c) := Group.IsPerfect.map c.H.subtype
  have hKnQ : K c ≤ normalizer (Q c : Set G) :=
    (map_subtype_le _).trans (core_normalized c)
  have hQ'nQ : Q' ≤ normalizer (Q c : Set G) := hQ'H.trans (core_normalized c)
  have hdouble : ⁅⁅Q',K c⁆,K c⁆ ≤ Q c := commutator_mono hcore le_rfl
  have hrot := commutator_commutator_le_of_rotate_of_le_normalizer hKnQ hKnQ hQ'nQ
    (by simpa only [commutator_comm (K c) Q'] using hdouble) hdouble
  rw [(K c).commutator_eq_self] at hrot
  exact crossing_core_commutator_not_le c hf hrot
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

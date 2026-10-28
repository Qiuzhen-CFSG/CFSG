module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCubicRadical
public import Theory.GroupTheory.PCoreCentralImage
public import Theory.GroupTheory.PResidual.PrimeToAction
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Splitting the full span in the remaining cubic branch

For the original normal two-perfect five-lift Y, the central pairing and
three-subgroups lemma put [O₂(Y),Y] in the full U_I-action kernel. Coprime
transfer then kills O₂(Y) itself. The original faithful quotient action
supplies the reverse containment, so the kernel is exactly O₂(Y).

Coprime action now splits U_I into its literal moved subgroup W=[U_I,Y]
and fixed subgroup C=C_{U_I}(Y). Original generation gives U_I=VW;
the pairing radical meets V in V₁, so V meets W trivially and C has
order eight. The order-four pairing quotient further gives R=WV₁.
The source application is in LargePrimeCubicSplittingSource.

These are necessary restrictions in the surviving branch, not its exclusion.
In particular C has not been identified with the critical pair's common
eight-group. Source: Aschbacher–Smith, 14.5.21(1), 14.7.6, printed pp.1019
and 1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Representation
open Chapter12.Section08 CriticalFusion.Source
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

/-- In a central pairing, radical movement makes the full two-core of a
normal two-perfect odd lift act trivially on the original module. -/
theorem local_radical_lift_action_kernel
    {I U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction I U Z)
    (Y : Subgroup I) (hYp : IsPPerfect 2 Y)
    (hY5 : IsPGroup 5 (Y ⧸ pCore 2 Y))
    (hk : ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y)
    (hz : Z ≤ centralizer (Y.map I.subtype : Set G))
    (hq : ⁅I.pCoreIn 2,U⁆ ≤ Z)
    (hm : ⁅Y.map I.subtype,U⁆ ≤ U ⊓ centralizer (I.pCoreIn 2 : Set G)) :
    ((U.normalizerMonoidHom.comp (inclusion a.normalizes)).comp Y.subtype).ker =
      pCore 2 Y := by
  let j := I.subtype.comp Y.subtype
  let f := (U.normalizerMonoidHom.comp (inclusion a.normalizes)).comp Y.subtype
  have hcore : (pCore 2 Y).map j ≤ I.pCoreIn 2 := by
    rintro x ⟨y,hy,rfl⟩
    have hyk := hk.ge hy
    have hyI : (y : I) ∈ pCore 2 I := (QuotientGroup.eq_one_iff _).mp hyk
    exact mem_map_of_mem I.subtype hyI
  have hrot : ⁅⁅I.pCoreIn 2,Y.map I.subtype⁆,U⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · exact commutator_eq_bot_iff_le_centralizer.mpr (hm.trans inf_le_right)
    · rw [commutator_comm U (I.pCoreIn 2)]
      exact commutator_eq_bot_iff_le_centralizer.mpr (hq.trans hz)
  have hc : ⁅pCore 2 Y,(⊤ : Subgroup Y)⁆ ≤ f.ker := by
    have hc' : (⁅pCore 2 Y,(⊤ : Subgroup Y)⁆).map j ≤ centralizer (U : Set G) := by
      rw [map_commutator,←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype]
      exact (commutator_mono hcore le_rfl).trans
        (commutator_eq_bot_iff_le_centralizer.mp hrot)
    intro y hy
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change j y * (v : G) * (j y)⁻¹ = (v : G)
    rw [←hc' (mem_map_of_mem j hy) v v.property,mul_inv_cancel_right]
  have hi : Nat.Coprime 2 (pCore 2 Y).index := by
    rw [index_eq_card]
    obtain ⟨n,hn⟩ := hY5.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 5).pow_right n
  apply le_antisymm
  · intro y hy
    apply hk.le
    change QuotientGroup.mk' (pCore 2 I) (y : I) = 1
    apply a.faithful
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) v.toMul
    have hv : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) w) = v :=
      congrArg Additive.ofMul hw
    rw [←hv,a.conjugation,map_one]
    have he := congrArg (fun b : MulAut U => b w) hy
    change (⟨((y : I) : G) * (w : G) * ((y : I) : G)⁻¹,_⟩ : U) = w at he
    rw [he]
    rfl
  · exact pCore_le_of_commutator_le_of_coprime_index hYp hi f.ker hc

/-- The literal full-module action of the five-lift has coprime image;
its fixed and moved subgroups therefore split the original span. -/
theorem local_radical_lift_splitting
    {I U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction I U Z)
    (Y : Subgroup I) (hYp : IsPPerfect 2 Y)
    (hY5 : IsPGroup 5 (Y ⧸ pCore 2 Y))
    (hk : ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y)
    (hz : Z ≤ centralizer (Y.map I.subtype : Set G))
    (hq : ⁅I.pCoreIn 2,U⁆ ≤ Z)
    (hm : ⁅Y.map I.subtype,U⁆ ≤ U ⊓ centralizer (I.pCoreIn 2 : Set G)) :
    ⁅U,Y.map I.subtype⁆ ⊔ (U ⊓ centralizer (Y.map I.subtype : Set G)) = U ∧
      ⁅U,Y.map I.subtype⁆ ⊓ (U ⊓ centralizer (Y.map I.subtype : Set G)) = ⊥ := by
  let B := Y.map I.subtype
  have hBI : B ≤ I := map_subtype_le _
  have hBN : B ≤ normalizer (U : Set G) := hBI.trans a.normalizes
  let f := U.normalizerMonoidHom.comp (inclusion hBN)
  let e : Y ≃* B := Y.equivMapOfInjective I.subtype I.subtype_injective
  have he : (f.comp e.toMonoidHom).ker = pCore 2 Y :=
    local_radical_lift_action_kernel a Y hYp hY5 hk hz hq hm
  have hf : IsPGroup 5 f.range := by
    have hr : (f.comp e.toMonoidHom).range = f.range :=
      by
        ext b
        constructor
        · rintro ⟨y,rfl⟩
          exact ⟨e y,rfl⟩
        · rintro ⟨y,rfl⟩
          obtain ⟨y,rfl⟩ := e.surjective y
          exact ⟨y,rfl⟩
    rw [←hr]
    have hq : IsPGroup 5 (Y ⧸ (f.comp e.toMonoidHom).ker) :=
      hY5.of_equiv (QuotientGroup.quotientMulEquivOfEq he.symm)
    exact hq.of_equiv (QuotientGroup.quotientKerEquivRange (f.comp e.toMonoidHom))
  exact commutator_centralizer_decomposition_of_coprime_image U B hBN
    (IsPGroup.coprime_card_of_ne 5 2 (by decide) f.range U hf
      (IsElementaryAbelian.isPGroup 2 U))

/-- The original generation identity holds modulo the literal displacement,
without replacing it by the larger pairing radical. -/
theorem local_span_eq_seed_sup_moved
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (Y : Subgroup I) [Y.Normal]
    (hgen : I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G))) :
    V ⊔ ⁅F.UH I,Y.map I.subtype⁆ = F.UH I := by
  let B := Y.map I.subtype
  let W := ⁅F.UH I,B⁆
  have hIU : I ≤ normalizer (F.UH I : Set G) := le_normalizer_conjugateSpanBy V I
  have hIB : I ≤ normalizer (B : Set G) := by
    have hh := Y.le_normalizer_map I.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hIW : I ≤ normalizer (W : Set G) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hIU hx),
      mem_normalizer_iff_map_conj_eq.mp (hIB hx)]
  have hVU : V ≤ F.UH I := le_conjugateSpanBy V I
  have hWU : W ≤ F.UH I :=
    le_normalizer_iff_commutator_le_left.mp ((map_subtype_le Y).trans hIU)
  have hBV : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
    sup_le ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
      (by simpa only [F.last] using F.invariant 3)
  have hN : I ≤ normalizer ((V ⊔ W : Subgroup G) : Set G) := by
    rw [hgen]
    refine sup_le ?_ ((le_inf hBV ((le_sup_right.trans hgen.ge).trans hIW)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono (sup_le hVU hWU) le_rfl).trans le_sup_right
  exact le_antisymm (sup_le hVU hWU) (conjugateSpanBy_le le_sup_left hN)

/-- In the restricted cubic branch the fixed summand has exactly eight
points. It is kept separate from the common eight-group of the critical pair. -/
theorem local_radical_fixed_eight
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (Y : Subgroup I) [Y.Normal]
    [IsElementaryAbelian 2 (F.UH I)]
    (hgen : I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)))
    (hz : F.Vi 1 ≤ centralizer (Y.map I.subtype : Set G))
    (hm : ⁅Y.map I.subtype,F.UH I⁆ ≤ F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G))
    (hinter : V ⊓ (F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G)) = F.Vi 1)
    (hsplit : ⁅F.UH I,Y.map I.subtype⁆ ⊔
      (F.UH I ⊓ centralizer (Y.map I.subtype : Set G)) = F.UH I)
    (hdis : ⁅F.UH I,Y.map I.subtype⁆ ⊓
      (F.UH I ⊓ centralizer (Y.map I.subtype : Set G)) = ⊥) :
    V ⊓ ⁅F.UH I,Y.map I.subtype⁆ = ⊥ ∧
      Nat.card (F.UH I ⊓ centralizer (Y.map I.subtype : Set G) : Subgroup G) = 8 := by
  let U := F.UH I
  let W := ⁅U,Y.map I.subtype⁆
  let C := U ⊓ centralizer (Y.map I.subtype : Set G)
  have hWU : W ≤ U := by
    change ⁅F.UH I,Y.map I.subtype⁆ ≤ F.UH I
    rw [commutator_comm]
    exact hm.trans inf_le_left
  have hVU : V ≤ U := le_conjugateSpanBy V I
  have hVW : V ⊓ W = ⊥ := by
    apply bot_unique
    apply le_trans _ hdis.le
    refine le_inf inf_le_right (le_inf (inf_le_left.trans hVU) ?_)
    apply le_trans _ hz
    rw [←hinter]
    exact le_inf inf_le_left (inf_le_right.trans (by rwa [commutator_comm] at hm))
  have hUC : U ≤ centralizer (U : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hVWN : W ≤ normalizer (V : Set G) :=
    (hWU.trans (hUC.trans (centralizer_le hVU))).trans (Subgroup.centralizer_le_normalizer _)
  have hCWN : C ≤ normalizer (W : Set G) :=
    ((show C ≤ U from inf_le_left).trans (hUC.trans (centralizer_le hWU))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hv : Nat.card V = 8 := by
    simpa only [F.last,show (2 : ℕ)^3 = 8 from rfl] using F.card 3 (by decide)
  have h1 := card_sup_eq_mul_of_normalizes_of_disjoint V W hVWN (disjoint_iff.mpr hVW)
  have h2 := card_sup_eq_mul_of_normalizes_of_disjoint W C hCWN (disjoint_iff.mpr hdis)
  rw [local_span_eq_seed_sup_moved h I Y hgen,hv] at h1
  rw [hsplit] at h2
  have hpos : 0 < Nat.card W := Nat.card_pos
  refine ⟨hVW,?_⟩
  apply Nat.eq_of_mul_eq_mul_left hpos
  simpa only [mul_comm 8 (Nat.card W)] using h2.symm.trans h1

/-- The full pairing radical is exactly the moved summand times the original
central point; neither this summand nor the original five-action is discarded. -/
theorem local_radical_eq_moved_sup_point
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (Y : Subgroup I) [Y.Normal]
    [IsElementaryAbelian 2 (F.UH I)]
    (hgen : I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)))
    (hz : F.Vi 1 ≤ centralizer (Y.map I.subtype : Set G))
    (hm : ⁅Y.map I.subtype,F.UH I⁆ ≤ F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G))
    (hinter : V ⊓ (F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G)) = F.Vi 1)
    (hdis : ⁅F.UH I,Y.map I.subtype⁆ ⊓
      (F.UH I ⊓ centralizer (Y.map I.subtype : Set G)) = ⊥)
    (hi : (F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G)).relIndex (F.UH I) = 4) :
    ⁅F.UH I,Y.map I.subtype⁆ ⊔ F.Vi 1 =
      F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G) := by
  let U := F.UH I
  let W := ⁅U,Y.map I.subtype⁆
  let R := U ⊓ centralizer (I.pCoreIn 2 : Set G)
  have hWR : W ≤ R := by rwa [commutator_comm] at hm
  have hWU : W ≤ U := hWR.trans inf_le_left
  have hZR : F.Vi 1 ≤ R := hinter.ge.trans inf_le_right
  have hZU : F.Vi 1 ≤ U := hZR.trans inf_le_left
  have hUC : U ≤ centralizer (U : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hWZ : W ⊓ F.Vi 1 = ⊥ := bot_unique
    ((inf_le_inf_left W (le_inf hZU hz)).trans hdis.le)
  have hVW : V ⊓ W = ⊥ := by
    apply bot_unique
    rw [←hWZ]
    exact le_inf inf_le_right ((le_inf inf_le_left (inf_le_right.trans hWR)).trans hinter.le)
  have hv : Nat.card V = 8 := by
    simpa only [F.last,show (2 : ℕ)^3 = 8 from rfl] using F.card 3 (by decide)
  have hzcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hcardU := card_sup_eq_mul_of_normalizes_of_disjoint V W
    ((hWU.trans (hUC.trans (centralizer_le (le_conjugateSpanBy V I)))).trans
      (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr hVW)
  rw [local_span_eq_seed_sup_moved h I Y hgen,hv] at hcardU
  have hcardR := relIndex_mul_relIndex (⊥ : Subgroup G) R U bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hi] at hcardR
  have hcardWZ := card_sup_eq_mul_of_normalizes_of_disjoint W (F.Vi 1)
    ((hZU.trans (hUC.trans (centralizer_le hWU))).trans (Subgroup.centralizer_le_normalizer _))
      (disjoint_iff.mpr hWZ)
  rw [hzcard] at hcardWZ
  apply eq_of_le_of_card_ge (sup_le hWR hZR)
  rw [hcardWZ]
  have hc : Nat.card R * 4 = 8 * Nat.card W := hcardR.trans hcardU
  omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

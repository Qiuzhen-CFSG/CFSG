module

public import CFSG.Quasithin.ChapterE.Section05.CoreCenter
public import CFSG.Quasithin.ChapterE.Section05.GenerationFromCenter.Component

/-!
# The E.5.1 center calculation after a normal Sylow intersection

Keep the original E-member K and its original rank-bounded actor. Replace P
by S=P∩N, where N is normal in the ambient group and the actor belongs to the
prescribed Thompson family of S. The core O₂(K) still normalizes S, and its
intersection with N is normal in K. Thus the elementary span inside that
intersection is normal in K, and the original two-layer argument applies.
No E-membership of K∩N, component-orbit transitivity after restriction, or
inheritance of the numerical generation parameter is asserted.

Source application: Aschbacher--Smith 6.1.4, printed p.665, using E.5.1.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE
open ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- The smaller-Sylow elementary core span is normal in the original member. -/
theorem shifted_higherThompsonCore_normal (P N A K : Subgroup G) [N.Normal]
    {j k : ℕ} (hK : IsEMemberAt j P A K) :
    ((higherThompsonCore (P ⊓ N) K k).subgroupOf K).Normal := by
  apply (normal_subgroupOf_iff (higherThompsonCore_le _ K k)).mpr
  intro w x hw hx
  have hmap : (higherThompsonCore (P ⊓ N) K k).map
      (MulAut.conj x).toMonoidHom ≤ higherThompsonCore (P ⊓ N) K k := by
    rw [map_le_iff_le_comap]
    apply sSup_le
    intro B hB
    rw [← map_le_iff_le_comap]
    have hBc : B.map (MulAut.conj x).toMonoidHom ≤ (pCore 2 K).map K.subtype := by
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨q, hq, rfl⟩ := hB.2 hb
      exact ⟨(⟨x,hx⟩ : K) * q * (⟨x,hx⟩ : K)⁻¹,
        (inferInstance : (pCore 2 K).Normal).conj_mem q hq ⟨x,hx⟩, rfl⟩
    have hBn : B.map (MulAut.conj x).toMonoidHom ≤ N := by
      rintro _ ⟨b,hb,rfl⟩
      exact (inferInstance : N.Normal).conj_mem b (hB.1.1 hb).2 x
    let _ : IsElementaryAbelian 2 B := hB.1.2.1
    apply le_sSup
    refine ⟨⟨le_inf (hBc.trans hK.1.core_le) hBn,
      IsElementaryAbelian.map _,hB.1.2.2.1,?_⟩,hBc⟩
    rw [card_map_of_injective (MulAut.conj x).injective]
    exact hB.1.2.2.2
  exact hmap (mem_map_of_mem _ hw)

private theorem shifted_maxJ_core_le (S A K : Subgroup G) (i j : ℕ)
    (hA : A ∈ thompsonFamily S i) (hij : i+j < twoRank S)
    (hr : Nat.log 2 ((A ⊓ (pCore 2 K).map K.subtype).relIndex A) ≤ j) :
    elementaryAbelianMaxJ (S ⊓ (pCore 2 K).map K.subtype) ≤
      higherThompsonCore S K (i+j) := by
  let Q := S ⊓ (pCore 2 K).map K.subtype
  let B := A ⊓ (pCore 2 K).map K.subtype
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (show B ≤ A from inf_le_left)
  obtain ⟨b,hb⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
  have hrank := ((mem_thompsonFamily_iff_rank S A i).mp hA).2.2
  have hdiff := log_card_sub_log_card_eq_log_relIndex A B inf_le_left
  change Nat.log 2 (B.relIndex A) ≤ j at hr
  rw [← hdiff,hb,Nat.log_pow Nat.one_lt_two] at hr
  have hcard : 2 ^ (twoRank S-(i+j)) ≤ Nat.card B := by
    rw [hb]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply sSup_le
  intro C hC
  let _ : IsElementaryAbelian 2 C := hC.2.1
  have hBQ : B ≤ Q := le_inf (inf_le_left.trans hA.1) inf_le_right
  have hcardC := hcard.trans (hC.2.2 B hBQ inferInstance)
  intro x hx
  obtain ⟨F,hFC,heF,hcardF,hxF⟩ :=
    IsElementaryAbelian.exists_two_power_subgroup_mem C (by omega) hcardC x hx
  exact (le_sSup (show F ∈ {F : Subgroup G |
      F ∈ thompsonFamily S (i+j) ∧ F ≤ (pCore 2 K).map K.subtype} from
    ⟨⟨hFC.trans (hC.1.trans inf_le_left),heF,hij.le,hcardF⟩,
      hFC.trans (hC.1.trans inf_le_right)⟩)) hxF

private theorem shifted_center_inf_core_le (S A K : Subgroup G) (i j : ℕ)
    (hA : A ∈ thompsonFamily S i) (hij : i+j < twoRank S)
    (hr : Nat.log 2 ((A ⊓ (pCore 2 K).map K.subtype).relIndex A) ≤ j) :
    higherThompsonCenter S (i+j) ⊓ (pCore 2 K).map K.subtype ≤
      higherThompsonCore S K (i+j) := by
  let Q := S ⊓ (pCore 2 K).map K.subtype
  let W := higherThompsonCore S K (i+j)
  have hJ := shifted_maxJ_core_le S A K i j hA hij hr
  have hle := omegaOneAmbient_mono (inf_le_inf_left Q (centralizer_le hJ))
  rw [omegaCentralizer_thompson] at hle
  have homega : omegaOneAmbient (Q ⊓ centralizer (W : Set G)) ≤ W :=
    hle.trans (fun x hx => hJ ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)
  intro d hd
  apply homega
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl d
  · exact ⟨⟨higherThompsonCenter_le S (i+j) hd.1,hd.2⟩,
      (centralizer_le (higherThompsonCore_le_thompsonJ S K (i+j)))
        (higherThompsonCenter_centralizes S (i+j) hd.1)⟩
  · exact ((mem_omegaOneCenterAmbient_iff _ _).mp hd.1).2.1

private theorem shifted_center_le_member (P N A K : Subgroup G) (i j : ℕ)
    (hA : A ∈ thompsonFamily (P ⊓ N) i) (hij : i+j < twoRank (P ⊓ N))
    (hK : IsEMemberAt j P A K) : higherThompsonCenter (P ⊓ N) (i+j) ≤ K := by
  have hD : higherThompsonCenter (P ⊓ N) (i+j) ≤ tau P A := by
    intro d hd
    apply mem_centralizerModulo_iff.mpr
    refine ⟨(higherThompsonCenter_le _ _ hd).1,fun a ha => ?_⟩
    have hc := mem_centralizer_iff.mp
      (higherThompsonCenter_le_centralizer _ A i j hA hij hd) a ha
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
    exact (pCore 2 G).one_mem
  exact hD.trans (hK.1.2.2.2.1.trans inf_le_right)

private theorem shifted_center_commutator (P N A K : Subgroup G) [N.Normal] (i j : ℕ)
    (hA : A ∈ thompsonFamily (P ⊓ N) i) (hij : i+j < twoRank (P ⊓ N))
    (hK : IsEMemberAt j P A K) :
    ⁅higherThompsonCenter (P ⊓ N) (i+j),(pCore 2 K).map K.subtype⁆ ≤
      higherThompsonCore (P ⊓ N) K (i+j) := by
  apply le_trans _ (shifted_center_inf_core_le _ A K i j hA hij hK.core_rank_le)
  apply le_inf
  · apply le_normalizer_iff_commutator_le_left.mp
    apply hK.1.core_le.trans
    apply le_trans _ (normalizer_le_normalizer_higherThompsonCenter (P ⊓ N) (i+j))
    exact (le_inf P.le_normalizer
      (by rw [normalizer_eq_top]; exact le_top)).trans inf_normalizer_le_normalizer_inf
  · apply le_normalizer_iff_commutator_le_right.mp
    apply (shifted_center_le_member P N A K i j hA hij hK).trans
    exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le (pCore 2 K))).mp (by
      rw [subgroupOf,comap_map_eq_self_of_injective K.subtype_injective]
      infer_instance)

private theorem two_subgroup_le_core {R U : Subgroup G} [R.Normal]
    (hR : IsTwoClosed R) (hU : IsPGroup 2 U) (hUR : U ≤ R) : U ≤ pCore 2 G := by
  obtain ⟨S,hS⟩ := hR
  let _ : (S : Subgroup R).Characteristic := S.characteristic_of_normal hS
  have hsn : ((S : Subgroup R).map R.subtype).Normal := inferInstance
  have hle : U.subgroupOf R ≤ (S : Subgroup R) := by
    let _ := hS
    obtain ⟨T,hT⟩ := (hU.comap_of_injective R.subtype R.subtype_injective).exists_le_sylow
    have hST : S=T := by
      apply Sylow.ext
      exact (S.is_maximal' T.isPGroup' (S.isPGroup'.le_sylow_of_normal T)).symm
    simpa only [hST,subgroupOf] using hT
  calc
    U = (U.subgroupOf R).map R.subtype := (map_subgroupOf_eq_of_le hUR).symm
    _ ≤ (S : Subgroup R).map R.subtype := map_mono hle
    _ ≤ pCore 2 G := le_sSup ⟨hsn,S.isPGroup'.map R.subtype⟩

/-- E.5.1 for the center defined by a normal intersection with P. The local
member, core, radical, and rank bound remain those of the original K. -/
theorem shifted_higherThompsonCenter_le_omegaCenter_of_radical
    (P N A K : Subgroup G) [N.Normal] (i j : ℕ)
    (hA : A ∈ thompsonFamily (P ⊓ N) i) (hK : IsEMemberAt j P A K)
    (R : Subgroup K) [R.Normal] (hR : IsTwoClosed R)
    (hquot : pCore 2 (K ⧸ R) = ⊥)
    (hcent : pResidual 2 K ⊓ centralizer (pCore 2 K : Set K) ≤ R) :
    higherThompsonCenter (P ⊓ N) (i+j) ≤
      omegaOneCenterAmbient (higherThompsonCore (P ⊓ N) K (i+j)) := by
  by_cases hdeg : twoRank (P ⊓ N) ≤ i+j
  · rw [higherThompsonCenter_eq_bot_of_rank_le _ _ hdeg]
    exact bot_le
  have hij : i+j < twoRank (P ⊓ N) := Nat.lt_of_not_ge hdeg
  let D := higherThompsonCenter (P ⊓ N) (i+j)
  let W := higherThompsonCore (P ⊓ N) K (i+j)
  have hDK : D ≤ K := shifted_center_le_member P N A K i j hA hij hK
  have hWK : W ≤ K := higherThompsonCore_le _ K (i+j)
  let d := D.subgroupOf K
  let w := W.subgroupOf K
  let _ : w.Normal := shifted_higherThompsonCore_normal P N A K hK
  have hwQ : w ≤ pCore 2 K := by
    intro x hx
    obtain ⟨q,hq,he⟩ := higherThompsonCore_le_core _ K (i+j) hx
    exact (show q=x from Subtype.ext he) ▸ hq
  have hdw : d ≤ centralizer (w : Set K) := by
    intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    apply Subtype.ext
    exact mem_centralizer_iff.mp
      ((centralizer_le (higherThompsonCore_le_thompsonJ _ K (i+j)))
        (higherThompsonCenter_centralizes _ (i+j) hx)) y hy
  have hcomm : ⁅d,pCore 2 K⁆ ≤ w := by
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hDK,map_subgroupOf_eq_of_le hWK]
    exact shifted_center_commutator P N A K i j hA hij hK
  have hdR : d ≤ R :=
    (le_inf hdw (le_commutatorPreimage le_top hcomm)).trans
      (two_layer_le_radical (pCore 2 K) w R (pCore_isPGroup.to_le hwQ) hquot hcent)
  let _ : IsElementaryAbelian 2 D := omegaOneCenterAmbient_elementaryAbelian _
  have hdQ : d ≤ pCore 2 K := two_subgroup_le_core hR
    ((IsElementaryAbelian.isPGroup 2 D).comap_subtype) hdR
  have hDQ : D ≤ (pCore 2 K).map K.subtype := fun x hx =>
    ⟨⟨x,hDK hx⟩,hdQ hx,rfl⟩
  intro x hx
  refine (mem_omegaOneCenterAmbient_iff W x).mpr ⟨?_,?_,?_⟩
  · exact shifted_center_inf_core_le _ A K i j hA hij hK.core_rank_le ⟨hx,hDQ hx⟩
  · exact ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.1
  · exact mem_centralizer_iff.mp
      ((centralizer_le (higherThompsonCore_le_thompsonJ _ K (i+j)))
        (higherThompsonCenter_centralizes _ (i+j) hx))

/-- Both original E-member branches supply their own radical; only the
original E.5.1 centralizer alternative is required. -/
theorem shifted_higherThompsonCenter_le_omegaCenter
    (P N A K : Subgroup G) [N.Normal] (i j : ℕ)
    (hA : A ∈ thompsonFamily (P ⊓ N) i) (hK : IsEMemberAt j P A K)
    (hcent : WeakClosureCentralizerBound P A K) :
    higherThompsonCenter (P ⊓ N) (i+j) ≤
      omegaOneCenterAmbient (higherThompsonCore (P ⊓ N) K (i+j)) := by
  rcases hcent with ⟨ho,hc⟩ | ⟨he,hc⟩
  · exact shifted_higherThompsonCenter_le_omegaCenter_of_radical P N A K i j hA hK
      (weakClosureOddRadical K) ho.weakClosureOddRadical_twoClosed
      ho.pCore_quotient_weakClosureOddRadical hc
  · apply shifted_higherThompsonCenter_le_omegaCenter_of_radical P N A K i j hA hK
      (solvableRadical K) he.1 _ hc
    let H := K ⧸ solvableRadical K
    let _ : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
    have hle : pCore 2 H ≤ solvableRadical H := le_solvableRadical _ inferInstance inferInstance
    exact bot_unique (hle.trans_eq solvableRadical_quotient_solvableRadical)

end CFSG.Quasithin.ChapterE

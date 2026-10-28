module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalComponent
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalQuotientSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.ChapterC.Section02
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.NormalizedSupConsequences
/-!
# The original core is radical in the exceptional component join

Let C=C_T(K) have order two, J=K_D C, T₀=C_T(C), and T₁=T₀∩J.
The marked A₅ image gives [L:C_L(C)]=6. Since L is normal in M,
[M:C_M(C)] is even; the source bound [T:T₀]≤2 therefore makes T₀
Sylow in C_M(C). Subnormal restriction makes the literal T₁ Sylow in M∩J.

The A₅ block core formula gives O₂(KT₁)=Q, where Q=O₂(LT).
Earlier maximal-local uniqueness gives N_G(Q)≤M, so the same T₁ is
Sylow in N_J(Q). The Sylow-overgroup core theorem then gives
O₂(N_J(Q))=Q. C.2.1(2) puts O₂(J) inside Q. Its already proved trivial
intersection with V forces it to centralize K, and hence O₂(J)=C.

The final consumer constructs the core split and C_T(L)=1 from the original
source setup. It retains the genuine earlier maximality hypothesis and the
containing component already supplied by SourceExceptionalComponent.
Source: Aschbacher--Smith 13.5.15(7), printed pp.920--921, from the
definition of T₁ through the conclusion D=O₂(K_D D).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalRadical
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

private theorem sylow_in_of_even_index (T : Sylow 2 G) (A U : Subgroup G)
    (hUT : U ≤ T) (hUA : U ≤ A) (hi : U.relIndex (T : Subgroup G) ≤ 2)
    (he : 2 ∣ A.index) : Chapter1.IsSylowIn 2 U A := by
  have hmulT := relIndex_mul_index hUT
  have hmulA := relIndex_mul_index hUA
  have htwo : 2 ∣ U.index := he.trans (index_dvd_of_le hUA)
  have hi2 : U.relIndex (T : Subgroup G) = 2 := by
    rw [←hmulT] at htwo
    have hh := (Nat.prime_two.dvd_mul.mp htwo).resolve_right T.not_dvd_index
    have hpos : 0 < U.relIndex (T : Subgroup G) := Nat.pos_of_ne_zero index_ne_zero_of_finite
    exact Nat.le_antisymm hi (Nat.le_of_dvd hpos hh)
  have hodd : ¬ 2 ∣ (U.subgroupOf A).index := by
    intro hh
    have hfour : 2 * 2 ∣ U.index := by
      rw [←hmulA]
      exact Nat.mul_dvd_mul hh he
    rw [←hmulT,hi2] at hfour
    exact T.not_dvd_index ((Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hfour)
  exact ⟨(T.isPGroup'.to_le hUT).comap_subtype.toSylow hodd,
    map_subgroupOf_eq_of_le hUA⟩

include d in
/-- Earlier maximal-local uniqueness controls the actual original core normalizer. -/
theorem original_core_normalizer_le
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L) :
    normalizer (D.LT.pCoreIn 2 : Set G) ≤ M := by
  rw [d.local_normalizer]
  apply hmax.normal_subgroup_normalizer_le d.normalizes_L (pCoreIn_le 2 D.LT)
  · intro he
    exact d.chosen.ne_bot (bot_unique (d.chosen.le_core.trans he.le))
  · exact D.LT.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D.LT (pCore 2 D.LT))

include d in
/-- The literal centralizer in L has the source index six. -/
theorem exceptional_local_centralizer_index
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2 = D.V)
    (hsplit : D.LT.pCoreIn 2 = D.V ⊔ ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)))
    (hCL : (D.T : Subgroup G) ⊓ centralizer (D.L : Set G) = ⊥)
    (hcard : Nat.card ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) = 2) :
    let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
    (D.L ⊓ centralizer (C : Set G)).relIndex D.L = 6 := by
  let K := NormalBranch.K D g.val
  let C := (D.T : Subgroup G) ⊓ centralizer (K : Set G)
  let X := D.L ⊓ centralizer (C : Set G)
  let f := SourceSixBlock.actor d
  have he : X = K ⊔ D.L.pCoreIn 2 :=
    SourceExceptionalNormalizer.exceptional_local_centralizer d h e g hK a hi hS hsplit hCL hcard
  have hX : X.subgroupOf D.L = K.subgroupOf D.L ⊔ pCore 2 D.L := by
    rw [he,subgroupOf_sup hK (pCoreIn_le 2 D.L)]
    congr 1
    exact comap_map_eq_self_of_injective D.L.subtype_injective _
  have hker : f.ker ≤ X.subgroupOf D.L := by
    rw [SourceSixBlock.actor_ker d e,hX]
    exact le_sup_right
  have hmap : (X.subgroupOf D.L).map f = (K.subgroupOf D.L).map f := by
    rw [hX,Subgroup.map_sup,←SourceSixBlock.actor_ker d e,Subgroup.map_ker_self,sup_bot_eq]
  have hcardK : Nat.card ((K.subgroupOf D.L).map f) = 60 := by
    rw [←card_map_of_injective (f := (alternatingGroup (Fin 6)).subtype)
      (alternatingGroup (Fin 6)).subtype_injective,map_map]
    change Nat.card ((K.subgroupOf D.L).map (localMap d)) = 60
    rw [hi,card_map_of_injective (MulAut.conj a.val).injective,FivePair.five_card]
  have hindex : ((K.subgroupOf D.L).map f).index = 6 := by
    have hh := ((K.subgroupOf D.L).map f).card_mul_index
    rw [hcardK,nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  change (X.subgroupOf D.L).index = 6
  rw [←(X.subgroupOf D.L).index_map_eq (SourceSixBlock.actor_surjective d) hker,hmap,hindex]

include d in
/-- The source centralizer in T has full Sylow order in C_M(C). -/
theorem exceptional_sylow_in_maximal_centralizer
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2 = D.V)
    (hsplit : D.LT.pCoreIn 2 = D.V ⊔ ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)))
    (hCL : (D.T : Subgroup G) ⊓ centralizer (D.L : Set G) = ⊥)
    (hcard : Nat.card ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) = 2) :
    let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
    Chapter1.IsSylowIn 2 ((D.T : Subgroup G) ⊓ centralizer (C : Set G))
      (M ⊓ centralizer (C : Set G)) := by
  let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
  let A := M ⊓ centralizer (C : Set G)
  let U := (D.T : Subgroup G) ⊓ centralizer (C : Set G)
  have hTM : (D.T : Subgroup G) ≤ M := d.local_normalizer.symm ▸ d.normalizes_L
  have hLM : D.L ≤ M := d.local_normalizer.symm ▸ D.L.le_normalizer
  have hUA : U ≤ A := inf_le_inf_right _ hTM
  have hrel : A.relIndex D.L = 6 := by
    have hh := exceptional_local_centralizer_index d h e g hK a hi hS hsplit hCL hcard
    change (D.L ⊓ centralizer (C : Set G)).relIndex D.L = 6 at hh
    have he : A ⊓ D.L = D.L ⊓ centralizer (C : Set G) := by
      change (M ⊓ centralizer (C : Set G)) ⊓ D.L = _
      rw [inf_right_comm,inf_of_le_right hLM]
    rw [←inf_relIndex_right,he]
    exact hh
  have hrelM : 2 ∣ A.relIndex M := by
    have hnorm : A ≤ normalizer (D.L : Set G) :=
      inf_le_left.trans (by rw [d.local_normalizer])
    have hd : A.relIndex (D.L ⊔ A) ∣ A.relIndex M :=
      dvd_of_mul_right_eq _ (relIndex_mul_relIndex A (D.L ⊔ A) M le_sup_right
        (sup_le hLM inf_le_left))
    rw [relIndex_sup_of_normalizes D.L A hnorm,hrel] at hd
    exact (by decide : 2 ∣ 6).trans hd
  have hidx := SourceExceptionalIndex.exceptional_sylow_centralizer_index
    d h e hseed hn hU g hK hp a hi hcard
  have hs : Chapter1.IsSylowIn 2 (U.subgroupOf M) (A.subgroupOf M) := by
    apply sylow_in_of_even_index (D.T.subtype hTM) (A.subgroupOf M) (U.subgroupOf M)
      (subgroupOf_mono _ inf_le_left) (subgroupOf_mono _ hUA)
    · simpa only [Sylow.coe_subtype,relIndex_subgroupOf hTM] using hidx
    · exact hrelM
  have hm := Chapter1.Section02.IndexTwo.isSylowIn_map hs M.subtype
  rwa [map_subgroupOf_eq_of_le (inf_le_left.trans hTM),map_subgroupOf_eq_of_le inf_le_left] at hm


private theorem sylow_component_intersection
    {C KD S : Subgroup G} (hc : Nat.card C = 2)
    (hKD : KD ≤ centralizer (C : Set G))
    (hcomp : (KD.subgroupOf (centralizer (C : Set G))).IsCComponent)
    (hSM : S ≤ M)
    (hS : Chapter1.IsSylowIn 2 S (M ⊓ centralizer (C : Set G))) :
    Chapter1.IsSylowIn 2 (S ⊓ (KD ⊔ C)) (M ⊓ (KD ⊔ C)) := by
  let H := centralizer (C : Set G)
  let J := KD ⊔ C
  let A := M ⊓ H
  let : IsCyclic C := isCyclic_of_prime_card (p := 2) hc
  have hJH : J ≤ H := sup_le hKD C.le_centralizer
  have hj := SourceExceptionalQuotientSylow.component_central_join_subnormal hc hKD hcomp
  have hn : ((M ⊓ J).subgroupOf A).IsSubnormal := by
    have hh := hj.comap (inclusion (show A ≤ H from inf_le_right))
    have he : (J.subgroupOf H).comap (inclusion (show A ≤ H from inf_le_right)) =
        (M ⊓ J).subgroupOf A := by
      ext x
      exact ⟨fun hx => ⟨x.property.1,hx⟩,fun hx => hx.2⟩
    rwa [he] at hh
  have hs := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hS
    (show M ⊓ J ≤ A from inf_le_inf_left _ hJH) hn
  simpa only [←inf_assoc,inf_eq_left.mpr hSM] using hs

variable (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L)
    (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2 = D.V)
    (hsplit : D.LT.pCoreIn 2 = D.V ⊔ ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)))
    (hCL : (D.T : Subgroup G) ⊓ centralizer (D.L : Set G) = ⊥)
    (hcard : Nat.card ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) = 2)
    (KD : Subgroup G) (hKKD : NormalBranch.K D g.val ≤ KD)
    (hKD : KD ≤ centralizer (((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G))
    (hcomp : (KD.subgroupOf (centralizer (((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G))).IsCComponent)

local notation "K₀" => NormalBranch.K D g.val
local notation "C₀" => ((D.T : Subgroup G) ⊓ centralizer (K₀ : Set G))
local notation "J₀" => (KD ⊔ C₀ : Subgroup G)
local notation "T₀" => ((D.T : Subgroup G) ⊓ centralizer (C₀ : Set G))
local notation "T₁" => (T₀ ⊓ J₀ : Subgroup G)

include d h e hseed hn hU g hK hp a hi hS hsplit hCL hcard KD hKD hcomp in
/-- The literal source T₁ is Sylow in M∩K_D C. -/
theorem exceptional_intersection_sylow :
    Chapter1.IsSylowIn 2 T₁ (M ⊓ J₀) := by
  have hTM : (D.T : Subgroup G) ≤ M := d.local_normalizer.symm ▸ d.normalizes_L
  exact sylow_component_intersection hcard hKD hcomp (inf_le_left.trans hTM)
    (exceptional_sylow_in_maximal_centralizer d h e hseed hn hU g hK hp a hi hS hsplit hCL hcard)

include d h e hseed hn hU g hK hL hp a hi hS hsplit hCL hcard KD hKKD hKD hcomp in
/-- The original A₅ block and the literal T₁ have precisely the original core Q. -/
theorem exceptional_pair_join_core :
    (K₀ ⊔ T₁).pCoreIn 2 = D.LT.pCoreIn 2 := by
  let A := K₀ ⊔ T₁
  have hTM : (D.T : Subgroup G) ≤ M := d.local_normalizer.symm ▸ d.normalizes_L
  have hLM : D.L ≤ M := d.local_normalizer.symm ▸ D.L.le_normalizer
  have hAJ : A ≤ M ⊓ J₀ := sup_le (le_inf (hK.trans hLM) (hKKD.trans le_sup_left))
    (le_inf ((inf_le_left.trans inf_le_left).trans hTM) inf_le_right)
  have hTA : Chapter1.IsSylowIn 2 T₁ A :=
    (exceptional_intersection_sylow d h e hseed hn hU g hK hp a hi hS hsplit hCL hcard KD hKD hcomp).restrict
      le_sup_right hAJ
  obtain ⟨P,hP⟩ := hTA
  have hcoreT : A.pCoreIn 2 ≤ (D.T : Subgroup G) :=
    (pCoreIn_le_sylow A P).trans (hP.le.trans (inf_le_left.trans inf_le_left))
  have hT0K := SourceExceptionalNormalizer.exceptional_sylow_centralizer_normalizes_pair
    d h e g hK hp a hi hS hsplit hCL hcard
  have hAK : A ≤ normalizer (K₀ : Set G) :=
    sup_le (K₀).le_normalizer (inf_le_left.trans hT0K)
  have hB := SourceFiveBlock.alternatingBlock d e g hK hp a hi hS
  have hc := SourceFiveSpan.module_commutator d hK a hi h hL hseed
  have hb := SourceCoreSplit.pair_block_layer g hS hc
  have he := hB.normalizer_twoCore_eq_module_sup_centralizer le_sup_left hAK
  rw [hb] at he
  apply le_antisymm
  · rw [he,hsplit]
    exact sup_le le_sup_left ((inf_le_inf hcoreT le_rfl).trans le_sup_right)
  · let : IsCyclic (C₀ : Subgroup G) := isCyclic_of_prime_card (p := 2) hcard
    have hQA : D.LT.pCoreIn 2 ≤ A := by
      rw [hsplit]
      exact sup_le ((hS ▸ pCoreIn_le 2 K₀).trans le_sup_left)
        ((le_inf (le_inf inf_le_left (C₀).le_centralizer) le_sup_right).trans le_sup_right)
    have hALT : A ≤ D.LT := sup_le (hK.trans le_sup_left)
      ((inf_le_left.trans inf_le_left).trans le_sup_right)
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 D.LT) hQA
      (hALT.trans (D.LT.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image D.LT (pCore 2 D.LT))))


include d h e hseed hn hU g hK hL hp a hi hS hsplit hCL hcard KD hKKD hKD hcomp in
/-- The literal T₁ is Sylow in the normalizer of the original core inside K_D C,
and that core is radical there. -/
theorem exceptional_core_radical
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L) :
    Chapter1.IsSylowIn 2 T₁ (J₀ ⊓ normalizer (D.LT.pCoreIn 2 : Set G)) ∧
      (J₀ ⊓ normalizer (D.LT.pCoreIn 2 : Set G)).pCoreIn 2 = D.LT.pCoreIn 2 := by
  let Q := D.LT.pCoreIn 2
  let N := J₀ ⊓ normalizer (Q : Set G)
  let A := K₀ ⊔ T₁
  have hQN : D.LT ≤ normalizer (Q : Set G) :=
    D.LT.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D.LT (pCore 2 D.LT))
  have hT1N : T₁ ≤ N := le_inf inf_le_right
    ((inf_le_left.trans inf_le_left).trans (le_sup_right.trans hQN))
  have hNM : N ≤ M ⊓ J₀ := le_inf
    (inf_le_right.trans (original_core_normalizer_le d hmax)) inf_le_left
  have hTS := (exceptional_intersection_sylow d h e hseed hn hU g hK hp a hi hS
    hsplit hCL hcard KD hKD hcomp).restrict hT1N hNM
  refine ⟨hTS,?_⟩
  obtain ⟨P,hP⟩ := hTS
  have hAN : A ≤ N := sup_le
    (le_inf (hKKD.trans le_sup_left) (hK.trans (le_sup_left.trans hQN))) hT1N
  have hAc : A.pCoreIn 2 = Q := exceptional_pair_join_core d h e hseed hn hU g hK hL hp a hi hS
    hsplit hCL hcard KD hKKD hKD hcomp
  have hh := pCoreIn_normalizer_eq_of_sylow_le P hAN (hP.le.trans le_sup_right)
  rw [hAc,inf_eq_left.mpr (show N ≤ normalizer (Q : Set G) from inf_le_right)] at hh
  exact hh

include d h e hseed hn hU g hK hL hp a hi hS hsplit hCL hcard KD hKKD hKD hcomp in
/-- C.2.1(2) puts the whole two-core of K_D C in the actual radical Q. -/
theorem exceptional_twoCore_le_original
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L) :
    (J₀).pCoreIn 2 ≤ D.LT.pCoreIn 2 := by
  let J := J₀
  let Q := D.LT.pCoreIn 2
  have hQJ : Q ≤ J := by
    change D.LT.pCoreIn 2 ≤ J
    rw [hsplit]
    exact sup_le ((hS ▸ pCoreIn_le 2 K₀).trans (hKKD.trans le_sup_left)) le_sup_right
  have hrad := (exceptional_core_radical d h e hseed hn hU g hK hL hp a hi hS
    hsplit hCL hcard KD hKKD hKD hcomp hmax).2
  have hmap : (normalizer (Q.subgroupOf J : Set J)).map J.subtype =
      J ⊓ normalizer (Q : Set G) := by
    rw [←subgroupOf_normalizer_eq hQJ,subgroupOf_map_subtype,inf_comm]
  have hrad' : (normalizer (Q.subgroupOf J : Set J)).pCoreIn 2 = Q.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ J.subtype J.subtype_injective,hmap,
      map_subgroupOf_eq_of_le hQJ]
    exact hrad
  have hh := ChapterC.twoCore_le_radical (Q.subgroupOf J)
    (isPGroup_pCoreIn 2 D.LT).comap_subtype hrad'
  have hm := map_mono (f := J.subtype) hh
  rwa [map_subgroupOf_eq_of_le hQJ] at hm

include d h e hseed hn hU g hK hL hp a hi hS hsplit hCL hcard KD hKKD hKD hcomp in
/-- The source's trivial V-intersection and radicality identify the exact
ambient core O₂(K_D C)=C, with no extra Sylow or normalizer premise. -/
theorem exceptional_twoCore_eq_centralizer
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hdis : D.V ⊓ (J₀).pCoreIn 2 = ⊥) : (J₀).pCoreIn 2 = C₀ := by
  let J := J₀
  let Q := D.LT.pCoreIn 2
  let P := J.pCoreIn 2
  have hPQ : P ≤ Q := exceptional_twoCore_le_original d h e hseed hn hU g hK hL hp a hi hS
    hsplit hCL hcard KD hKKD hKD hcomp hmax
  have hKQ : K₀ ≤ normalizer (Q : Set G) := (hK.trans le_sup_left).trans
    (D.LT.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D.LT (pCore 2 D.LT)))
  have hQK : Q ≤ normalizer (K₀ : Set G) := SourcePairResidual.twoCore_normalizes_pair h g
  have hcomm : ⁅K₀,Q⁆ ≤ D.V := by
    rw [←hS]
    exact le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 D.LT).to_le (le_normalizer_iff_commutator_le_right.mp hKQ))
      (le_normalizer_iff_commutator_le_left.mp hQK) (normalizer_commutator_ge_left _ _)
  have hKP : K₀ ≤ normalizer (P : Set G) := (hKKD.trans le_sup_left).trans
    (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hz : ⁅K₀,P⁆ = ⊥ := bot_unique ((le_inf
    ((commutator_mono le_rfl hPQ).trans hcomm)
    (le_normalizer_iff_commutator_le_right.mp hKP)).trans hdis.le)
  apply le_antisymm
  · exact le_inf (hPQ.trans (h.sylow_centralizer.symm.le.trans inf_le_left))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
  · let : IsCyclic (C₀ : Subgroup G) := isCyclic_of_prime_card (p := 2) hcard
    have hJC : J ≤ centralizer (C₀ : Set G) := sup_le hKD (C₀).le_centralizer
    exact le_pCoreIn_of_normalizes (D.T.isPGroup'.to_le inf_le_left) le_sup_right
      (hJC.trans (centralizer_le_normalizer (C₀ : Set G)))


include d h e hseed hn hU g hK hL hp a hi hS hcard KD hKKD hKD hcomp in
/-- The actual selected original pair supplies all core and Sylow conclusions
in the radical paragraph of 13.5.15, retaining only the earlier 12.2 maximality
and the already constructed containing component with its core intersection. -/
theorem exceptional_radical_and_core
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hdis : D.V ⊓ (J₀).pCoreIn 2 = ⊥) :
    Chapter1.IsSylowIn 2 T₁ (M ⊓ J₀) ∧
      Chapter1.IsSylowIn 2 T₁ (J₀ ⊓ normalizer (D.LT.pCoreIn 2 : Set G)) ∧
      (J₀ ⊓ normalizer (D.LT.pCoreIn 2 : Set G)).pCoreIn 2 = D.LT.pCoreIn 2 ∧
      (J₀).pCoreIn 2 = C₀ := by
  have hB := SourceFiveBlock.alternatingBlock d e g hK hp a hi hS
  have hc := SourceFiveSpan.module_commutator d hK a hi h hL hseed
  have hsplit := SourceCoreSplit.core_eq_module_sup_centralizer h g hK hB hS hc
  have hCL := SourcePairCentralizer.sylow_local_centralizer_eq_bot_of_generated_core d h e hseed hn hU
  obtain ⟨hTN,hrad⟩ := exceptional_core_radical d h e hseed hn hU g hK hL hp a hi hS
    hsplit hCL hcard KD hKKD hKD hcomp hmax
  exact ⟨exceptional_intersection_sylow d h e hseed hn hU g hK hp a hi hS
    hsplit hCL hcard KD hKD hcomp,hTN,hrad,
    exceptional_twoCore_eq_centralizer d h e hseed hn hU g hK hL hp a hi hS
      hsplit hCL hcard KD hKKD hKD hcomp hmax hdis⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalRadical
end

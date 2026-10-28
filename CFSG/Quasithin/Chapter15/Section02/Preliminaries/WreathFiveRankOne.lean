module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveNonquasisimple
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import GorensteinWalter.PSL2Cardinality

/-!
# The binary rank-one case in the original marked-five wreath argument

The original local A₅ component is local at the full Sylow subgroup of W.
If its containing component L₁ has a binary SL₂ two-core quotient, the
rank-one Sylow-overgroup theorem forces K=L₁. Comparing their literal
quotient orders bounds the field degree by two. This excludes the rank-one
case with degree divisible by four in the printed C.2.7/A.3.15 comparison.

The source consumer keeps the same chosen K, Y, S, W, R and L₁, and all the
original global hypotheses. The classification producing that comparison
and the linear-three case remain separate.
Source: Aschbacher--Smith, original15.2.4, printed p.1107.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The full-Sylow local A₅ fixes the field degree of a binary rank-one
containing component to be at most two. -/
public theorem source_local_component_rankOne_degree_le_two
    {H K S W L₁ : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hKW : K ≤ W) (hSyl : Chapter1.IsSylowIn 2 S W)
    (hcore : pCore 2 W ≠ ⊥)
    (hL₁ : L₁ ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L₁)
    (hq : IsQuasisimple (L₁ ⧸ pCore 2 L₁))
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (e : (L₁ ⧸ pCore 2 L₁) ≃* SL(2,F.Carrier)) : F.degree ≤ 2 := by
  obtain ⟨P,hP⟩ := hSyl
  have hSW : S ≤ W := hP ▸ map_subtype_le _
  have hP' : (P : Subgroup W) = S.subgroupOf W := by
    rw [←hP]
    exact (comap_map_eq_self_of_injective W.subtype_injective _).symm
  have hWH : W ∈ Chapter1.H G :=
    fun hb => hcore ((map_eq_bot_iff_of_injective _ W.subtype_injective).mp hb)
  have hcoreS : W.pCoreIn 2 ≤ S := hP ▸ pCoreIn_le_sylow W P
  have hcoreKS : W.pCoreIn 2 ≤ (K ⊔ S).pCoreIn 2 :=
    (le_inf (hcoreS.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 (sup_le hKW hSW))
  have hlocal : K ∈ Chapter1.L G S :=
    ⟨hK.2.subgroupOf_of_le le_sup_left (sup_le hK.1 hSH),
      Chapter1.IsSylowIn.restrict ⟨P,hP⟩ le_sup_right (sup_le hKW hSW),
      fun hb => hWH (bot_unique (hb ▸ hcoreKS))⟩
  have hlocal' : K.subgroupOf W ∈ Chapter1.L W (P : Subgroup W) := by
    rw [hP']
    exact (Chapter1.mem_LIn_iff_subgroupOf hSW hKW).mp ⟨hKW,hlocal⟩
  let a := subgroupOfEquivOfLe hL₁.1
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let : IsQuasisimple (L₁ ⧸ pCore 2 L₁) := hq
  let : IsQuasisimple ((L₁.subgroupOf W) ⧸ pCore 2 (L₁.subgroupOf W)) :=
    IsQuasisimple.of_mulEquiv b.symm
  let f := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L₁)).comp a.toMonoidHom)
  have hf : Function.Surjective f := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp a.surjective)
  have heq := ChapterA.Section03.SourceEmbeddings.eq_of_rankOne_cover P hlocal'.1
    hL₁.2 (comap_mono hKL) f hf
  have heq' : K = L₁ := by
    have hh := congrArg (map W.subtype) heq
    simpa only [map_subgroupOf_eq_of_le hKW,map_subgroupOf_eq_of_le hL₁.1] using hh
  subst L₁
  have hc : Nat.card SL(2,F.Carrier) = 60 := by
    rw [←Nat.card_congr e.toEquiv,Nat.card_congr heK.some.toEquiv,
      nat_card_alternatingGroup]
    norm_num
  have hd : 2 ^ F.degree ∣ 60 := by
    rw [←hc,GorensteinWalter.sl2_card_formula,F.card_eq]
    exact dvd_mul_right _ _
  by_contra hn
  have hh : 8 ∣ 60 := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ F.degree)).trans hd
  norm_num at hh

open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- The original failed-parabolic configuration excludes the binary rank-one
row of the printed comparison, whose positive field degree is divisible by four. -/
public theorem source_HStar_wreath_five_failed_quotient_no_large_rankOne
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hcases : SourceCases.Dihedral (imageRepresentation M V hV.normalized) ∨
      SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let R := (Y ⊔ S).pCoreIn 2
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (pCore 2 W ≠ ⊥ →
        (¬ ∀ i, generalizedFitting (((ChapterF.Source.parabolic L S i).subgroupOf W).map q) =
          pCore 2 (((ChapterF.Source.parabolic L S i).subgroupOf W).map q)) →
        Chapter1.IsSylowIn 2 S W ∧ V ≤ W.pCoreIn 2 ∧
        generalizedFitting W = pCore 2 W ∧
        Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple W R (W ⊓ M) ∧
        ∃ L₁ : Subgroup G, L₁ ∈ Chapter1.cComponentsIn W ∧ K ≤ L₁ ∧ ¬ L₁ ≤ M ∧
          W ≤ normalizer (L₁ : Set G) ∧ W = L₁ ⊔ (W ⊓ M) ∧
          generalizedFitting L₁ = pCore 2 L₁ ∧
          ¬ Chapter1.IsSylowIn 2 R (L₁ ⊔ R) ∧ Y ≤ L₁ ∧
          IsQuasisimple (L₁ ⧸ pCore 2 L₁) ∧
          ∀ F : ChapterB.QuasisimpleSource.BinaryField,
            4 ∣ F.degree → ¬ Nonempty ((L₁ ⧸ pCore 2 L₁) ≃* SL(2,F.Carrier))) := by
  obtain ⟨K,hK,heK,hout,hi,hJS,hconf⟩ :=
    source_HStar_wreath_five_failed_quotient_quasisimple_component
      hG T hempty hM hJ hu hmany hV hcases hH he
  refine ⟨K,hK,heK,hout,hi,hJS,?_⟩
  intro hcore hfailed
  obtain ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hnot,hYL,hq⟩ :=
    hconf hcore hfailed
  refine ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hnot,hYL,hq,?_⟩
  intro F hd hF
  have hle := source_local_component_rankOne_degree_le_two hK
    (inf_le_left.trans hH.1.1.2) heK
    (le_sup_right.trans le_sup_left) hSyl hcore hL₁ hKL hq F hF.some
  have hge := Nat.le_of_dvd F.degree_pos hd
  omega

end CFSG.Quasithin.Chapter15.Section02

module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryAction
public import Theory.GroupTheory.ElementarySylowQuinticAction
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms

/-!
# The original quintic pair inside the actual ordinary quotient

The genuine five-group on the original moving support descends through the
perfect central cover. Two-group outer automorphisms make this actor inner,
so its nontrivial elementary displacement is an actual subgroup of the
specified quotient, normalized by the original full Sylow. Its order is at
least sixteen. The actual inner five-group and full movement are retained.
No whole marked residual is assumed to be a five-group.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem raw_quintic_normal_elementary_pair
    (T : Sylow 2 G) {M V Z1 L Y : Subgroup G} [IsElementaryAbelian 2 V]
    [Group.IsPerfect L] (hTM : (T : Subgroup G) ≤ M)
    (hn : M ≤ normalizer (V : Set G)) (hVM : V ≤ M) (hZ : Z1 ≤ V)
    (hLG : L ≤ centralizer (Z1 : Set G)) (hcenter : center L = pCore 2 L)
    (hSyl : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hY : IsPGroup 5 Y)
    (hYR : Y ≤ (pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype)
    (hnL : let C := M ⊓ centralizer (Z1 : Set G); let R := (pResidual 2 C).map C.subtype
      R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G))
    (hWY : let C := M ⊓ centralizer (Z1 : Set G); let R := (pResidual 2 C).map C.subtype
      ⁅⁅V,R⁆,Y⁆ = ⁅V,R⁆)
    (hmove : let C := M ⊓ centralizer (Z1 : Set G); let R := (pResidual 2 C).map C.subtype
      ⁅L,⁅V,R⁆⁆ ≠ ⊥)
    {X : Type*} [Group X] (e : (L ⧸ pCore 2 L) ≃* X)
    (hz : center X = ⊥) (ho : IsPGroup 2 (MulAut.Outer X)) :
    ∃ (P : Sylow 2 X) (E D : Subgroup X), IsElementaryAbelian 2 E ∧
      E ≤ (P : Subgroup X) ∧ (P : Subgroup X) ≤ normalizer (E : Set X) ∧
      IsPGroup 5 D ∧ ⁅E,D⁆ = E ∧ E ≠ ⊥ ∧ 16 ≤ Nat.card E := by
  let : Finite X := Finite.of_equiv (L ⧸ pCore 2 L) e.toEquiv
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',
      ←hcenter]
  let c : PerfectCentralCovering.Cover L X := ⟨q,hq,inferInstance,hker.le⟩
  let C := M ⊓ centralizer (Z1 : Set G)
  let R := (pResidual 2 C).map C.subtype
  let W := ⁅V,R⁆
  let N := normalizer (L : Set G)
  let f := (c.autMap hker).comp L.normalizerMonoidHom
  have hRC : R ≤ C := map_subtype_le _
  have hRN : R ≤ N := le_sup_left.trans hnL
  have hYN : Y ≤ N := hYR.trans hRN
  have hWN : W ≤ N := le_sup_right.trans hnL
  have hRV : R ≤ normalizer (V : Set G) := (hRC.trans inf_le_left).trans hn
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp hRV
  have hVC : V ≤ C := le_inf hVM
    (V.le_centralizer.trans (centralizer_le hZ))
  have hWC : W ≤ C := hWV.trans hVC
  have hCW : C ≤ normalizer (W : Set G) := by
    have hnV : (V.subgroupOf C).Normal :=
      normal_subgroupOf_of_le_normalizer (inf_le_left.trans hn)
    have hR : R.subgroupOf C = pResidual 2 C := by
      apply map_injective C.subtype_injective
      rw [map_subgroupOf_eq_of_le hRC]
    have he : W.subgroupOf C = ⁅V.subgroupOf C,pResidual 2 C⁆ := by
      change ⁅V,R⁆.subgroupOf C = _
      rw [SubgroupTransport.subgroupOf_commutator V R hVC hRC,hR]
    have hn : (W.subgroupOf C).Normal := he ▸ inferInstance
    exact (normal_subgroupOf_iff_le_normalizer hWC).mp hn
  let A := (W.subgroupOf N).map f
  let B := (Y.subgroupOf N).map f
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  let : IsElementaryAbelian 2 (W.subgroupOf N) := IsElementaryAbelian.subgroupOf hWN
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  have hB : IsPGroup 5 B :=
    (hY.of_equiv (subgroupOfEquivOfLe hYN).symm).map f
  obtain ⟨P,hP⟩ := hSyl
  let Q := P.mapSurjective (f := q) hq
  have hPC : ((P : Subgroup L).map L.subtype) ≤ C := by
    rw [hP]
    exact le_inf ((inf_le_left.trans inf_le_left).trans hTM)
      (inf_le_right.trans hLG)
  have hPA : (Q : Subgroup X).map (MulAut.conj : X →* MulAut X) ≤
      normalizer (A : Set (MulAut X)) := by
    rintro _ ⟨x,⟨l,hl,rfl⟩,rfl⟩
    let xn : N := ⟨l,L.le_normalizer l.property⟩
    have hxW : xn ∈ normalizer (W.subgroupOf N : Set N) := by
      rw [←subgroupOf_normalizer_eq hWN]
      exact hCW (hPC (mem_map_of_mem L.subtype hl))
    have hfx : f xn = MulAut.conj (q l) := by
      ext z
      obtain ⟨w,rfl⟩ := hq z
      change c.autMap hker (L.normalizerMonoidHom xn) (q w) = _
      rw [c.autMap_apply hker]
      change q (l*w*l⁻¹) = _
      simp only [map_mul,map_inv,MulAut.conj_apply]
    rw [←hfx]
    exact (W.subgroupOf N).le_normalizer_map f (mem_map_of_mem f hxW)
  have hAB : ⁅A,B⁆ = A := by
    dsimp only [A,B]
    rw [←map_commutator,←SubgroupTransport.subgroupOf_commutator W Y hWN hYN,hWY]
  have hAne : A ≠ ⊥ := by
    intro he
    have hcW : W ≤ centralizer (L : Set G) := by
      intro w hw l hl
      have hh : f ⟨w,hWN hw⟩ = 1 := mem_bot.mp (he ▸ mem_map_of_mem f hw)
      have hh' : L.normalizerMonoidHom ⟨w,hWN hw⟩ = 1 :=
        (c.autMap_injective hker) (hh.trans (map_one (c.autMap hker)).symm)
      have ha := congrArg Subtype.val (DFunLike.congr_fun hh' (⟨l,hl⟩ : L))
      change w*l*w⁻¹=l at ha
      exact (mul_inv_eq_iff_eq_mul.mp ha).symm
    exact hmove (by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hcW)
  obtain ⟨E,D,hE,hEP,hPE,hD,hED,hEn,hcE⟩ :=
    exists_normal_elementary_pair_of_quintic_movement hz ho Q A B hB hPA hAB hAne
  exact ⟨Q,E,D,hE,hEP,hPE,hD,hED,hEn,hcE⟩

/-- The original full quintic source produces the actual large elementary
quintic pair in the specified ordinary quotient, with the full Sylow retained. -/
theorem PreparedChosenModule.decomposable_five_raw_ordinary_quintic_pair
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let S := (T : Subgroup G) ⊓ G1
      ∀ {L : Subgroup G}, L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
        center L = pCore 2 L → Chapter1.IsSylowIn 2 (S ⊓ L) L →
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ∀ {X : Type*} [Group X], (L ⧸ pCore 2 L) ≃* X →
          center X = ⊥ → IsPGroup 2 (MulAut.Outer X) →
          ∃ (P : Sylow 2 X) (E D : Subgroup X), IsElementaryAbelian 2 E ∧
            E ≤ (P : Subgroup X) ∧ (P : Subgroup X) ≤ normalizer (E : Set X) ∧
            IsPGroup 5 D ∧ ⁅E,D⁆ = E ∧ E ≠ ⊥ ∧ 16 ≤ Nat.card E := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R S L hLG hLc hcenter hSyl hnL hmove X _ e hz ho
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  obtain ⟨Y,hY,hperfect,hYA,_,_,_,_,hBY,_⟩ :=
    s.exists_permuting_quintic_actor hM.1.2 h.normalized h.le_selected c d π hp hs hJi hfive
  have hYC : Y ≤ C := hYA.trans (map_subtype_le _)
  have hYR : Y ≤ R := by
    have hh := embedded_pResidual_mono 2 hYC
    rw [(pResidual_eq_top_iff 2 Y).mpr hperfect,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hWB := (s.full_residual_geometry hM.1.2 h.normalized c d π hp hs hJi).2.1
  have hWY : ⁅⁅localModule T M,R⁆,Y⁆ = ⁅localModule T M,R⁆ := by
    rw [hWB]
    exact hBY
  let : IsQuasisimple (L.subgroupOf G1) := hLc.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
  exact raw_quintic_normal_elementary_pair T hM.1.2 h.normalized h.le_selected
    (inf_le_left.trans (plane_le _)) hLG hcenter hSyl hY hYR hnL hWY hmove e hz ho

end CFSG.Quasithin.Chapter15.Section01

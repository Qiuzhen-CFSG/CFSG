module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.OmegaFieldBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborTorus
public import Theory.GroupTheory.CoprimeFixedLayer

/-!
# Equality of the alpha omega order and the beta field order

The actual beta torus normalizes the entire alpha quotient omega preimage.
Its nonidentity elements fix exactly Z_alpha intersect Z(W). This subgroup
contains all omega displacements and centralizes the omega preimage. The
coprime decomposition and the three-subgroup lemma therefore show that the
torus acts freely on nonidentity elements of the faithful omega image.
Orbit counting gives |K_beta| < |Omega|. Since |K_beta| = q_beta - 1, this
reverses the already proved omega bound and gives equality.

This uses the constructed stronger displacement containment to shorten the
opposite-omega argument in DGS, Groups and Graphs (1985), 9.4, printed p.143.
All normalizers are in the original completion; the torus is not assumed to
lie in L_alpha. AlphaRecognition applies the result to both source branches.
-/

@[expose] public noncomputable section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G]

private theorem normalize_omega_preimage
    (H R K : Subgroup G)
    (hKH : K ≤ normalizer (H : Set G)) (hKR : K ≤ normalizer (R : Set G)) :
    let q := QuotientGroup.mk' (pCore 2 H)
    K ≤ normalizer ((((omegaCenterIn ((R.subgroupOf H).map q)).comap q).map
      H.subtype : Subgroup G) : Set G) := by
  dsimp only
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := omegaCenterIn ((R.subgroupOf H).map q)
  let Y := (A.comap q).map H.subtype
  have hconj (k : G) (hk : k ∈ K) : ∀ y ∈ Y, k*y*k⁻¹ ∈ Y := by
    let e : H ≃* H := H.normalizerMonoidHom ⟨k,hKH hk⟩
    let f := QuotientGroup.congr (pCore 2 H) (pCore 2 H) e (pCore_map_iso 2 e)
    have heR : (R.subgroupOf H).map e.toMonoidHom = R.subgroupOf H := by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (mem_normalizer_iff.mp (hKR hk) x).mp hx
      · intro x hx
        refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
        exact (mem_normalizer_iff.mp (hKR (K.inv_mem hk)) x).mp hx
    have hq : f.toMonoidHom.comp q = q.comp e.toMonoidHom := by
      ext x
      exact QuotientGroup.congr_mk' _ _ e (pCore_map_iso 2 e) x
    have hfR : ((R.subgroupOf H).map q).map f.toMonoidHom =
        (R.subgroupOf H).map q := by
      rw [map_map,hq,←map_map,heR]
    have hfA : A.map f.toMonoidHom = A := by
      dsimp only [A]
      rw [NilesRankOneKernel.omegaCenterIn_map_injective f.toMonoidHom f.injective,hfR]
    rintro y ⟨x,hx,rfl⟩
    refine ⟨e x,?_,rfl⟩
    change q (e x) ∈ A
    rw [←show f (q x) = q (e x) from QuotientGroup.congr_mk' _ _ e (pCore_map_iso 2 e) x]
    exact hfA ▸ mem_map_of_mem f.toMonoidHom hx
  intro k hk
  apply mem_normalizer_iff.mpr
  intro y
  constructor
  · exact hconj k hk y
  · intro hy
    have hh := hconj k⁻¹ (K.inv_mem hk) _ hy
    simpa only [inv_inv,inv_mul_cancel_left,mul_inv_cancel_right,mul_assoc,inv_mul_cancel,mul_one] using hh

private theorem torus_card_lt_image
    {D : Type*} [Group D] (q : G →* D) (Y K : Subgroup G)
    [Finite K] [Finite (Y.map q)]
    (hn : K ≤ normalizer (Y : Set G))
    (hne : ∃ y ∈ Y, q y ≠ 1)
    (hfree : ∀ k ∈ K, k ≠ 1 → ∀ y ∈ Y, Commute (q k) (q y) → q y = 1) :
    Nat.card K < Nat.card (Y.map q) := by
  classical
  obtain ⟨y,hy,hy1⟩ := hne
  let f : K → Y.map q := fun k => ⟨q ((k:G)*y*(k:G)⁻¹),
    mem_map_of_mem q ((mem_normalizer_iff.mp (hn k.property) y).mp hy)⟩
  have hf1 (k : K) : f k ≠ 1 := by
    intro he
    have hh := congrArg (fun z : Y.map q => q (k:G)⁻¹*(z:D)*q (k:G)) he
    apply hy1
    simpa only [f,map_mul,map_inv,OneMemClass.coe_one,mul_one,mul_assoc,
      inv_mul_cancel_left,mul_inv_cancel_left,mul_inv_cancel,inv_mul_cancel] using hh
  have hfi : Function.Injective f := by
    intro j k he
    by_contra hjk
    have hkne : (k:G)⁻¹*(j:G) ≠ 1 := by
      intro hh
      apply hjk
      exact Subtype.ext ((inv_mul_eq_one.mp hh).symm)
    have hcomm : Commute (q ((k:G)⁻¹*(j:G))) (q y) := by
      have hh := congrArg (fun z : Y.map q => q (k:G)⁻¹*(z:D)*q (j:G)) he
      change q ((k:G)⁻¹*(j:G)) * q y = q y * q ((k:G)⁻¹*(j:G))
      simpa only [f,map_mul,map_inv,mul_assoc,inv_mul_cancel_left,
        mul_inv_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh
    exact hy1 (hfree _ (K.mul_mem (K.inv_mem k.property) j.property) hkne y hy hcomm)
  let F : Option K → Y.map q := fun x => match x with
    | none => 1
    | some k => f k
  have hF : Function.Injective F := by
    intro x y he
    cases x with
    | none => cases y with
      | none => rfl
      | some k => exact (hf1 k he.symm).elim
    | some j => cases y with
      | none => exact (hf1 j he).elim
      | some k => exact congrArg some (hfi he)
  have hh := Nat.card_le_card_of_injective F hF
  have hcard : Nat.card (Option K) = Nat.card K + 1 := by
    let := Fintype.ofFinite K
    simp only [Nat.card_eq_fintype_card,Fintype.card_option]
  rw [hcard] at hh
  omega


private theorem torus_card_lt_centralizer_index
    (V Y K Z₀ : Subgroup G) [Finite V] [Finite Y] [Finite K]
    [IsMulCommutative V] (hV : IsPGroup 2 V)
    (hYn : Y ≤ normalizer (V : Set G)) (hKn : K ≤ normalizer (V : Set G))
    (hKY : K ≤ normalizer (Y : Set G)) (hodd : Odd (Nat.card K))
    (hne : ¬ Y ≤ centralizer (V : Set G))
    (hdisp : ⁅V,Y⁆ ≤ Z₀) (hZY : Z₀ ≤ centralizer (Y : Set G))
    (hfixed : ∀ k ∈ K, k ≠ 1 → V ⊓ centralizer ({k} : Set G) = Z₀) :
    Nat.card K < (centralizer (V : Set G)).relIndex Y := by
  let N := normalizer (V : Set G)
  let q := V.normalizerMonoidHom
  let YN := Y.subgroupOf N
  let KN := K.subgroupOf N
  have hYN : Finite YN := Finite.of_equiv Y (subgroupOfEquivOfLe hYn).symm.toEquiv
  have hKN : Finite KN := Finite.of_equiv K (subgroupOfEquivOfLe hKn).symm.toEquiv
  let := hYN
  let := hKN
  have hker := V.normalizerMonoidHom_ker
  have hne' : ∃ y ∈ YN, q y ≠ 1 := by
    obtain ⟨y,hy,hc⟩ := SetLike.not_le_iff_exists.mp hne
    refine ⟨⟨y,hYn hy⟩,hy,?_⟩
    intro he
    have hh : (⟨y,hYn hy⟩ : N) ∈ q.ker := he
    rw [hker] at hh
    exact hc hh
  have hfree : ∀ k ∈ KN, k ≠ 1 → ∀ y ∈ YN, Commute (q k) (q y) → q y = 1 := by
    intro k hk hk1 y hy hcomm
    let D := zpowers (k:G)
    let X := zpowers (y:G)
    have hDK : D ≤ K := zpowers_le.mpr hk
    let : Finite D := Finite.of_injective (inclusion hDK) (inclusion_injective hDK)
    have hkn : (k:G) ≠ 1 := fun he => hk1 (Subtype.ext he)
    have hfix : V ⊓ centralizer (D : Set G) = Z₀ := by
      apply le_antisymm
      · rw [←hfixed k hk hkn]
        exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers (k:G))))
      · rw [←hfixed k hk hkn]
        rintro v ⟨hv,hvk⟩
        refine ⟨hv,?_⟩
        rintro _ ⟨m,rfl⟩
        exact (Commute.zpow_left (show Commute (k:G) v from (mem_centralizer_singleton_iff.mp hvk).symm) m).eq
    have hXY : X ≤ Y := zpowers_le.mpr hy
    have hC : ⁅X,D⁆ ≤ centralizer (V : Set G) := by
      have hC' : ⁅zpowers y,zpowers k⁆ ≤ q.ker := by
        apply (Subgroup.map_eq_bot_iff _).mp
        rw [map_commutator,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
        apply commutator_eq_bot_iff_le_centralizer.mpr
        rintro _ ⟨m,rfl⟩ _ ⟨n,rfl⟩
        exact (hcomm.zpow_zpow n m).eq
      have hm := map_mono hC' (f := N.subtype)
      rw [map_commutator,MonoidHom.map_zpowers,MonoidHom.map_zpowers,hker,
        map_subgroupOf_eq_of_le (centralizer_le_normalizer (V : Set G))] at hm
      exact hm
    obtain ⟨m,hm⟩ := hV.exists_card_eq
    have hc : Nat.Coprime (Nat.card D) (Nat.card V) := by
      rw [hm]
      exact (hodd.of_dvd_nat (card_dvd_of_le hDK)).coprime_two_left.symm.pow_right m
    have hVX := le_centralizer_of_coprime_fixed_layer V D X (hDK.trans hKn)
      (Group.isSolvable_of_comm fun x y => mul_comm x y) hc
      ((commutator_mono le_rfl hXY).trans (hdisp.trans (hfix.symm ▸ inf_le_right)))
      (hfix.symm ▸ hZY.trans (centralizer_le hXY)) hC
    have hyc := le_centralizer_iff.mp hVX (mem_zpowers (y:G))
    change y ∈ q.ker
    rw [hker]
    exact hyc
  have hn' : KN ≤ normalizer (YN : Set N) := fun _ hk => le_normalizer_comap N.subtype (hKY hk)
  have hh := torus_card_lt_image q YN KN hn' hne' hfree
  rw [Nat.card_congr (subgroupOfEquivOfLe hKn).toEquiv] at hh
  rw [Representation.BinaryConjugationSection.actor_image_card_eq_relIndex
    N (centralizer (V : Set G)) Y q hker hYn] at hh
  exact hh


open Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
universe u
variable {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The original alpha quotient omega-center has exactly the beta field order,
for every Sylow representative with the full source edge image. -/
theorem reduced_natural_residual_omega_eq_field (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (Mbin : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (M : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hres : NaturalResidualSection h beta e n) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    ∀ R : Sylow 2 H,
      (R : Subgroup H).map H.subtype =
        (stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2 →
      Nat.card (omegaCenterIn ((R : Subgroup H).map
        (QuotientGroup.mk' (pCore 2 H)))) = Nat.card F := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a
  let Hβ := graphLocalGroup Γ beta
  let E := (stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2
  let W := conjugateSpanBy (Q Γ a) (stabilizer Γ beta)
  let Z₀ := Z Γ a ⊓ (Subgroup.center W).map W.subtype
  let q := QuotientGroup.mk' (pCore 2 H)
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite Hβ := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (Z Γ a) := Finite.of_injective (inclusion (Z_le_stabilizer Γ a)) (inclusion_injective _)
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  obtain ⟨R,hR,hYW,hYZ,hZY,hquad,hindex,hbound,hselect⟩ :=
    reduced_natural_residual_omega_bound h hob hc hab hd hb hcomm Mbin M hn hF e hres
  let T : Sylow 2 (H ⧸ pCore 2 H) := R.mapSurjective (QuotientGroup.mk'_surjective _)
  let A := omegaCenterIn ((R : Subgroup H).map q)
  let Y := (A.comap q).map H.subtype
  change (R : Subgroup H).map H.subtype = E at hR
  have hER : E.subgroupOf H = (R : Subgroup H) := by
    rw [←hR]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hYH : Y ≤ H := map_subtype_le _
  let : Finite Y := Finite.of_injective (inclusion hYH) (inclusion_injective hYH)
  have hYq : (Y.subgroupOf H).map q = A := by
    change ((A.comap q).map H.subtype |>.comap H.subtype).map q = A
    rw [comap_map_eq_self_of_injective H.subtype_injective,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hYE : Y ≤ E := by
    rw [←hR]
    apply map_mono
    have hh := comap_mono (f := q) (map_subtype_le
      ((omega₁ (center ((R : Subgroup H).map q)) (p := 2)).map
        (center ((R : Subgroup H).map q)).subtype))
    have hk : q.ker ≤ (R : Subgroup H) := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal R
    exact hh.trans (comap_map_eq_self hk).le
  have hYP : Y ≤ stabilizer Γ a := hYH.trans (sylowGenerated_le _)
  have hYtwo : IsPGroup 2 Y := (isPGroup_pCoreIn 2 _).to_le hYE
  have hYC := Reduction.reduced_critical_inf_centralizer h hc Y hYtwo hYP
  have hqker : q.ker = (Q Γ a).subgroupOf H :=
    CommutingNontrivial.local_quotient_kernel Γ d a (MulEquiv.refl _)
  have hi : (Q Γ a).relIndex Y = Nat.card A := by
    rw [←Representation.BinaryConjugationSection.actor_image_card_eq_relIndex
      H (Q Γ a) Y q hqker hYH,hYq]
  have hiC : (centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex Y = Nat.card A := by
    calc
      _ = (Y ⊓ centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex Y :=
        (inf_relIndex_left _ _).symm
      _ = (Y ⊓ Q Γ a).relIndex Y := congrArg (fun U => U.relIndex Y) hYC
      _ = (Q Γ a).relIndex Y := inf_relIndex_left _ _
      _ = Nat.card A := hi
  have hTne : (T : Subgroup (H ⧸ pCore 2 H)) ≠ ⊥ := by
    intro he
    have hh := (M.rankOneSylowFacts T).proper
    change normalizer (↑(T : Subgroup (H ⧸ pCore 2 H)) : Set (H ⧸ pCore 2 H)) < ⊤ at hh
    rw [he,normalizer_eq_top] at hh
    exact (lt_irrefl _ hh)
  let : Nontrivial T := (nontrivial_iff_ne_bot _).mpr hTne
  have hAne : A ≠ ⊥ := by
    have hh := omega_center_ne_bot T.isPGroup'
    intro he
    apply hh
    apply (Subgroup.map_eq_bot_iff_of_injective _ (T : Subgroup (H ⧸ pCore 2 H)).subtype_injective).mp
    exact he
  have hYnc : ¬ Y ≤ centralizer (Z Γ a : Set (Reduction.G₀ L S₀)) := by
    intro hh
    have hcard : Nat.card A = 1 := by rw [←hiC,relIndex_eq_one.mpr hh]
    exact hAne (card_eq_one.mp hcard)
  obtain ⟨K,hK,hodd,hKcard,hKR,hKW⟩ :=
    reduced_linear_neighbor_torus h hab (hob a beta hab) hn hF e
  let : Finite K := Finite.of_injective (inclusion (hK.trans inf_le_left)) (inclusion_injective _)
  have hKn : K ≤ normalizer (Z Γ a : Set (Reduction.G₀ L S₀)) :=
    (hK.trans inf_le_right).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a)
  have hKH : K ≤ normalizer (H : Set (Reduction.G₀ L S₀)) :=
    (hK.trans inf_le_right).trans (sylowGenerated_normalized _)
  have hKE : K ≤ normalizer (E : Set (Reduction.G₀ L S₀)) := by
    apply le_trans (le_inf (hK.trans inf_le_right)
      ((hK.trans inf_le_left).trans (sylowGenerated_le _)))
    exact (stabilizer Γ a ⊓ stabilizer Γ beta).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hKY : K ≤ normalizer (Y : Set (Reduction.G₀ L S₀)) := by
    have hh := normalize_omega_preimage H E K hKH hKE
    rwa [hER] at hh
  have hfixed : ∀ k ∈ K, k ≠ 1 →
      Z Γ a ⊓ centralizer ({k} : Set (Reduction.G₀ L S₀)) = Z₀ := by
    intro k hk hk1
    let kβ : Hβ := ⟨k,(hK hk).1⟩
    have ho : Odd (orderOf kβ) := by
      have hh := hodd.of_dvd_nat (_root_.orderOf_dvd_natCard (⟨k,hk⟩ : K))
      simpa only [kβ,Subgroup.orderOf_mk] using hh
    exact reduced_natural_residual_neighbor_odd_fixed h hc hab hd hb hcomm
      (hob a beta hab) e hres kβ ho (fun he => hk1 (congrArg Subtype.val he))
  have hlt := torus_card_lt_centralizer_index (Z Γ a) Y K Z₀
    (IsElementaryAbelian.isPGroup 2 _) (hYP.trans
      (CommutingNontrivial.stabilizer_normalizes_Z Γ a)) hKn hKY hodd hYnc hYZ hZY hfixed
  rw [hKcard,hiC] at hlt
  change Nat.card A ≤ Nat.card F at hbound
  change Nat.card F - 1 < Nat.card A at hlt
  have heq : Nat.card A = Nat.card F := by omega
  dsimp only
  intro R' hR'
  have hh : (R' : Subgroup H) = (R : Subgroup H) := by
    apply map_injective H.subtype_injective
    exact hR'.trans hR.symm
  simpa only [hh] using heq

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

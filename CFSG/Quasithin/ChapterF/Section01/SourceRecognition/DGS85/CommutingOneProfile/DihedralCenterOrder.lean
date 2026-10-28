module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.DihedralPathActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CenterOrder

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathExistence

/-!
# Exact center order and exclusion for the A5/dihedral candidate

The dihedral path actor excludes an intersection layer of order two.
Center escape and the literal quotient index reduce |Z_beta| to two or
eight. In the latter case two disjoint beta centers span Z_alpha of order
64. They are complementary Sylow fixed spaces in its actual conjugation
representation. Natural SL2(4) recognition forces binary dimension
divisible by four, contradicting dimension six.

Thus |Z_beta| = 2, and the existing actual-core obstruction excludes D10.
A full A5 alpha marking implies that its intrinsic local actor is the
full stabilizer; no separate intrinsic marking or turn-existence input
is needed in the final exclusion. The full marking remains explicit here.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.6)--(11.7), printed pp.172--175.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem local_eq_full_of_a5 (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (a : Vertex (family P))
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃* alternatingGroup (Fin 5)) :
    d.localGroup a = stabilizer (family P) a := by
  let := finite_endpoints h
  let H := stabilizer (family P) a
  let L := (d.localGroup a).subgroupOf H
  have hn : H ≤ normalizer (d.localGroup a : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (d.conjugate t a).symm.trans (congrArg d.localGroup ht)
  let : L.Normal := normal_subgroupOf_of_le_normalizer hn
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : (L.map q).Normal := Normal.map inferInstance _ hq
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨T⟩ := Sylow.nonempty (p := 2) (G := H)
  have hTL : (T : Subgroup H) ≤ L := by
    intro x hx
    exact d.sylow_le a T (mem_map_of_mem H.subtype hx)
  have htop : L.map q = ⊤ := by
    apply (show (L.map q).Normal from inferInstance).eq_bot_or_eq_top.resolve_left
    intro he
    have heT : (T : Subgroup H).map q = ⊥ := bot_unique ((map_mono hTL).trans he.le)
    have hc : Nat.card (T.mapSurjective hq) = 4 := by
      rw [(T.mapSurjective hq).card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_fin]
      decide +kernel
    have h1 : Nat.card (T.mapSurjective hq) = 1 := by
      change Nat.card ((T : Subgroup H).map q) = 1
      simp only [heT,Subgroup.card_bot]
    omega
  have hker : q.ker ≤ L := hk ▸ (pCore_isPGroup.le_sylow_of_normal T).trans hTL
  have hL : L = ⊤ := by
    have hh := congrArg (comap q) htop
    rwa [comap_map_eq,sup_eq_left.mpr hker,comap_top] at hh
  apply le_antisymm (d.local_le a)
  intro x hx
  have hh : (⟨x,hx⟩ : H) ∈ L := hL ▸ mem_top _
  exact hh

variable {k : Type*} [Field k] [Finite k] [CharP k 2]

private theorem center_card_two_or_eight (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (ef : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃* alternatingGroup (Fin 5))
    (hk : Nat.card k = 4)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Nat.card (Z (family P) b) = 2 ∨ Nat.card (Z (family P) b) = 8 := by
  let := finite_endpoints h
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .dihedral ⟨eb⟩
  obtain ⟨t,hta,htb,hesc⟩ := source_linear_rankOne_center_escape h hB d hc hb hcomm
    hbc hac Ma Mb ea g hga hgb
  have hab := source_critical_one_adjacent hc hb
  have hab' : (graph (family P)).Adj a (t • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) t).map_adj_iff.mpr hab
    change (graph (family P)).Adj (t • a) (t • b) at hh
    rwa [show t • a = a from hta] at hh
  have hI := source_linear_dihedral_neighbor_intersection_eq_center h hB d hc hb hcomm
    hbc hac Ma ea eb g hga hgb
  have hZi : Z (family P) b ≤ neighborCoreIntersection (family P) b := hI.ge
  have hp : IsPGroup 2 (Z (family P) b) := (isPGroup_pCoreIn 2 _).to_le
    (hZi.trans (neighborCoreIntersection_le _ hab))
  have hZG : Z (family P) b ≤ stabilizer (family P) (t • b) :=
    (hZi.trans (neighborCoreIntersection_le _ hab)).trans ((source_Z_Q_U h a).2.trans
      ((ballKernel_one_le_edge _ hab').trans inf_le_right))
  let eL := (MulEquiv.subgroupCongr (d.conjugate t b)).trans
    ((d.localGroup b).equivMapOfInjective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).symm
  let eb' := (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans eb
  have hindex := source_dihedral_two_subgroup_index h d (t • b) eb' (Z (family P) b) hp hZG hesc
  have hlayer := (source_linear_rankOne_intersection_layer h hB d hc hb hbc hac
    Ma Mb ea t hta htb).2
  have hnot := source_dihedral_a5_layer_card_ne_two h hB hS d hc hb hbc hac Ma ea eb ef t hta htb
  rw [hI,hk] at hlayer
  rw [hI] at hnot
  let J := Z (family P) b ⊓ Q (family P) (t • b)
  let : Finite J := Finite.of_injective
    (inclusion (inf_le_right.trans (Q_le_stabilizer _ (t • b)))) (inclusion_injective _)
  have hindex' : J.relIndex (Z (family P) b) = 2 := by
    rw [inf_relIndex_left]
    exact hindex
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) J (Z (family P) b) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hindex'] at hcount
  obtain ⟨n,hn⟩ := (hp.to_le (show J ≤ Z (family P) b from inf_le_left)).exists_card_eq
  have hnle : n ≤ 2 := (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp
    (hn ▸ hlayer : 2^n ≤ 2^2)
  have hJ : Nat.card J = 1 ∨ Nat.card J = 4 := by
    have hnot' : Nat.card J ≠ 2 := hnot
    interval_cases n
    · exact Or.inl (by simpa using hn)
    · exact (hnot' (by simpa using hn)).elim
    · exact Or.inr (by simpa using hn)
  rcases hJ with hJ | hJ
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

private theorem center_pair_span_of_eight (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (_ef : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃* alternatingGroup (Fin 5))
    (hk : Nat.card k = 4)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (h8 : Nat.card (Z (family P) b) = 8) :
    Z (family P) b ⊔ Z (family P) (g • b) = Z (family P) a := by
  let := finite_endpoints h
  let : Finite (Z (family P) a) := Finite.of_injective
    (inclusion (Z_le_stabilizer _ a)) (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  have hZa := source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hab.symm
  have hZga : Z (family P) (g • b) ≤ Z (family P) a := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hZa
    rwa [←Z_translate,←Z_translate,show g • a = a from hga] at hh
  have hn : Z (family P) (g • b) ≤ normalizer (Z (family P) b : Set G) :=
    (hZga.trans (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      ((source_core_centralizes_center h a).trans (centralizer_le hZa)))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hd := source_linear_rankOne_beta_centers_disjoint h hB d hc hb hcomm hbc hac Ma (.dihedral ⟨eb⟩) ea g hga hgb
  have hcount := card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hd
  have hgcard : Nat.card (Z (family P) (g • b)) = Nat.card (Z (family P) b) := by
    rw [Z_translate,card_map_of_injective (MulAut.conj g).injective]
  rw [hgcard,h8] at hcount
  have hratio := (source_linear_dihedral_center_card_ratio h hB d hc hb hcomm hbc hac Ma ea eb).2
  rw [hk,h8] at hratio
  exact eq_of_le_of_card_ge (sup_le hZa hZga) (by omega)

private theorem center_fixed_edge (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥) :
    Z (family P) a ⊓ centralizer ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 : Set G) =
      Z (family P) b := by
  let := finite_endpoints h
  let := source_center_elementary h a
  have hab := source_critical_one_adjacent hc hb
  let E := stabilizer (family P) a ⊓ stabilizer (family P) b
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer (family P) a from inf_le_left)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hab.symm
  have he := sylow_image_eq_edge_core (stabilizer (family P) b)
    (stabilizer (family P) b ⊓ stabilizer (family P) a) inf_le_left
    (source_edge_core_sylow h hB hab.symm) T hT
  rw [inf_comm] at he
  have hZaE : Z (family P) a ≤ E.pCoreIn 2 :=
    pGroup_le_core_of_core_sylow E _
      (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
        ((source_Z_Q_U h a).2.trans (ballKernel_one_le_edge _ hab)))
      (IsElementaryAbelian.isPGroup 2 _) (source_edge_core_sylow h hB hab)
  apply le_antisymm
  · intro x hx
    have hm : x ∈ omegaCenterIn ((T : Subgroup (stabilizer (family P) b)).map
        (stabilizer (family P) b).subtype) := by
      rw [he]
      exact (mem_omegaCenterIn_iff _ _).mpr
        ⟨hZaE hx.1,hx.2,elemPow_eq_one_of_isElementaryAbelian x hx.1⟩
    exact (le_iSup (fun R : Sylow 2 (stabilizer (family P) b) => omegaCenterIn
      ((R : Subgroup (stabilizer (family P) b)).map (stabilizer (family P) b).subtype)) T) hm
  · apply le_inf (source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hab.symm)
    have hz := (source_commuting_one_center_identities h hB hS hc hb hcomm).1
    intro x hx
    rw [hz] at hx
    have hh := ((mem_omegaCenterIn_iff _ _).mp hx).2.1
    exact centralizer_le (he ▸ sylow_le_sylowGenerated (stabilizer (family P) b) T) hh


open Representation Representation.BinaryOffender

private theorem exists_center_action (h : LocallyRankOneTriple P B)
    (a : Vertex (family P)) {D : Type*} [Group D]
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃* D) :
    letI := source_center_elementary h a
    ∃ ρ : Representation (ZMod 2) D (Additive (Z (family P) a)),
      ∀ (l : stabilizer (family P) a) (z : Additive (Z (family P) a)),
        ((ρ (e (QuotientGroup.mk' (pCore 2 (stabilizer (family P) a)) l)) z).toMul : G) =
          (l : G) * z.toMul * (l : G)⁻¹ := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let H := stabilizer (family P) a
  let V := Z (family P) a
  have hn : H ≤ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ a)).mp (Z_normal _ a)
  let α := V.normalizerMonoidHom.comp (inclusion hn)
  have hker : pCore 2 H ≤ α.ker := by
    intro l hl
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    have hh := (source_core_centralizes_center h a) (mem_map_of_mem H.subtype hl)
    change (l : G) * (z : G) * (l : G)⁻¹ = z
    have he := hh z z.property
    change (z : G) * (l : G) = (l : G) * (z : G) at he
    rw [←he,mul_inv_cancel_right]
  let β := QuotientGroup.lift (pCore 2 H) α hker
  let γ := β.comp e.symm.toMonoidHom
  let : MulDistribMulAction D V := MulDistribMulAction.compHom _ γ
  refine ⟨Representation.ofElementaryAbelianAction,?_⟩
  intro l z
  change ((β (e.symm (e (QuotientGroup.mk' (pCore 2 H) l)))) z.toMul : G) = _
  rw [e.symm_apply_apply]
  rfl

private theorem fixedSpace_eq_ambient (V H A : Subgroup G)
    [IsElementaryAbelian 2 V] {D : Type*} [Group D]
    (q : H →* D) (ρ : Representation (ZMod 2) D (Additive V))
    (hact : ∀ (l : H) (z : Additive V), ((ρ (q l) z).toMul : G) =
      (l : G) * z.toMul * (l : G)⁻¹) (T : Subgroup H)
    (he : V ⊓ centralizer (T.map H.subtype : Set G) = A) :
    fixedSpace ρ (T.map q) = AddSubgroup.toZModSubmodule 2 (A.subgroupOf V).toAddSubgroup := by
  ext z
  change (∀ t : T.map q, ρ t.val z = z) ↔ (z.toMul : G) ∈ A
  rw [←he]
  constructor
  · intro hz
    refine ⟨z.toMul.property,?_⟩
    rintro x ⟨t,ht,rfl⟩
    have hh := congrArg (fun w : Additive V => (w.toMul : G))
      (hz ⟨q t,mem_map_of_mem q ht⟩)
    change ((ρ (q t) z).toMul : G) = z.toMul at hh
    rw [hact] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · rintro ⟨_,hz⟩ ⟨_,t,ht,rfl⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((ρ (q t) z).toMul : G) = z.toMul
    rw [hact,hz (t : G) (mem_map_of_mem H.subtype ht),mul_inv_cancel_right]

private theorem complementary_card_ne_sixtyFour
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) Representation.SL2FourNatural.SL V)
    (T R : Sylow 2 Representation.SL2FourNatural.SL)
    (hc : IsCompl (fixedSpace ρ T) (fixedSpace ρ R)) : Nat.card V ≠ 64 := by
  have hF : Nat.card Representation.SL2FourNatural.F = 2^2 := by
    rw [Nat.card_eq_fintype_card,Representation.SL2FourNatural.card_field]
    decide
  obtain ⟨m,E,_⟩ := Representation.SL2SylowFixedRecognition.natural_of_complementary_sylow_fixed
    ρ T R hc 2 (by decide) hF
  intro h64
  have hh := Nat.card_congr E.toEquiv
  rw [h64,Nat.card_fun,Nat.card_fun,Nat.card_fin,Nat.card_fin,hF,←pow_mul,←pow_mul] at hh
  have he : 6 = 2 * (2 * m) := Nat.pow_right_injective (by decide : 1 < 2) hh
  omega


/-- The dihedral beta center has order two when the alpha field has order
four and the full alpha quotient is genuinely A₅. -/
theorem source_linear_four_dihedral_center_card_two (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (ef : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃* alternatingGroup (Fin 5))
    (hk : Nat.card k = 4)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Nat.card (Z (family P) b) = 2 := by
  rcases center_card_two_or_eight h hB hS d hc hb hcomm hbc hac Ma ea eb ef hk g hga hgb with h2 | h8
  · exact h2
  exfalso
  let := finite_endpoints h
  let := source_center_elementary h a
  let H := stabilizer (family P) a
  let V := Z (family P) a
  let A := Z (family P) b
  let C := Z (family P) (g • b)
  let : Finite V := Finite.of_injective (inclusion (Z_le_stabilizer _ a)) (inclusion_injective _)
  let es := ef.trans Representation.SL2FourNatural.alternatingFiveEquiv.symm
  let q := es.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := es.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨ρ,hact⟩ := exists_center_action h a es
  have hab := source_critical_one_adjacent hc hb
  have hab' : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [show g • a = a from hga] at hh
  have hc' : IsCriticalPair (family P) a (g • b) := by
    simpa only [show g • a = a from hga] using CommutingNontrivial.criticalPair_translate (family P) hc g
  have hcomm' : ⁅Z (family P) a,Z (family P) (g • b)⁆ = ⊥ := by
    have hh := CommutingNontrivial.commuting_centers_translate (family P) a b g
    simpa only [show g • a = a from hga,hcomm,Subgroup.map_bot] using hh
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hab
  obtain ⟨R,hR⟩ := source_edge_vertex_sylow h hS hab'
  have hTeq := sylow_image_eq_edge_core H _ inf_le_left
    (source_edge_core_sylow h hB hab) T hT
  have hReq := sylow_image_eq_edge_core H _ inf_le_left
    (source_edge_core_sylow h hB hab') R hR
  have hfT := fixedSpace_eq_ambient V H A q ρ hact T
    (hTeq ▸ center_fixed_edge h hB hS hc hb hcomm)
  have hfR := fixedSpace_eq_ambient V H C q ρ hact R
    (hReq ▸ center_fixed_edge h hB hS hc' hb hcomm')
  have hAV : A ≤ V := source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hab.symm
  have hCV : C ≤ V := source_commuting_one_center_le_neighbor h hB hS hc' hb hcomm' hab'.symm
  have hd := source_linear_rankOne_beta_centers_disjoint h hB d hc hb hcomm hbc hac Ma (.dihedral ⟨eb⟩) ea g hga hgb
  have hs := center_pair_span_of_eight h hB hS d hc hb hcomm hbc hac Ma ea eb ef hk g hga hgb h8
  have hcompl : IsCompl (A.subgroupOf V) (C.subgroupOf V) := by
    constructor
    · apply disjoint_iff.mpr
      apply bot_unique
      intro x hx
      apply mem_bot.mpr
      apply Subtype.ext
      exact mem_bot.mp (hd.le_bot ⟨hx.1, hx.2⟩)
    · apply codisjoint_iff.mpr
      rw [←subgroupOf_sup hAV hCV,hs,subgroupOf_self]
  let φ : Subgroup V ≃o Submodule (ZMod 2) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)
  have hfixed : IsCompl (fixedSpace ρ (T.mapSurjective hq)) (fixedSpace ρ (R.mapSurjective hq)) := by
    change IsCompl (fixedSpace ρ ((T : Subgroup H).map q)) (fixedSpace ρ ((R : Subgroup H).map q))
    rw [hfT,hfR]
    exact φ.isCompl_iff.mp hcompl
  apply complementary_card_ne_sixtyFour ρ (T.mapSurjective hq) (R.mapSurjective hq) hfixed
  change Nat.card V = 64
  have hh := (source_linear_dihedral_center_card_ratio h hB d hc hb hcomm hbc hac Ma ea eb).2
  rw [hk,h8] at hh
  exact hh


/-- For a genuine full A₅ alpha quotient the dihedral beta-center order
is forced, with no intrinsic alpha marking or center-order premise. -/
theorem source_a5_dihedral_center_card_two (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (ef : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃* alternatingGroup (Fin 5))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Nat.card (Z (family P) b) = 2 := by
  let eL := MulEquiv.subgroupCongr (local_eq_full_of_a5 h d a ef)
  let e₀ := (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans ef
  let ea := e₀.trans Representation.SL2FourNatural.alternatingFiveEquiv.symm
  have hk : Nat.card Representation.SL2FourNatural.F = 4 := by
    rw [Nat.card_eq_fintype_card,Representation.SL2FourNatural.card_field]
  let ep : Representation.SL2FourNatural.SL ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) Representation.SL2FourNatural.F :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi Representation.SL2FourNatural.F)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  have ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^2) :=
    ⟨Representation.SL2FourNatural.F,inferInstance,inferInstance,hk,⟨ea.trans ep⟩⟩
  exact source_linear_four_dihedral_center_card_two h hB hS d hc hb hcomm hbc hac
    (.linear 2 (by decide) ha) ea eb ef hk g hga hgb

/-- A dihedral beta quotient is impossible when the actual full alpha
quotient is A₅. The two turns are obtained from the original graph, and
all core, intersection and center-order premises of the exclusion are proved. -/
theorem source_a5_dihedral_exclusion (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (ef : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃* alternatingGroup (Fin 5))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) : False := by
  let := finite_endpoints h
  have hval (v : Vertex (family P)) : 3 ≤ Nat.card ((graph (family P)).neighborSet v) := by
    rw [card_neighbors_of_indices (family P) (fun i => ((family P (!i)).subgroupOf (family P i)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three h hS v.type
  obtain ⟨c,hbc,hca⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph (family P)).neighborSet b)
    (by rw [←Nat.card_coe_set_eq]; have hh := hval b; omega) a
  obtain ⟨b',hab',hb'b⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph (family P)).neighborSet a)
    (by rw [←Nat.card_coe_set_eq]; have hh := hval a; omega) b
  obtain ⟨g,hga,hgb'⟩ := locally_transitive (family P) (source_critical_one_adjacent hc hb) hab'
  have hgb : g • b ≠ b := by rw [hgb']; exact hb'b
  let eL := MulEquiv.subgroupCongr (local_eq_full_of_a5 h d a ef)
  let e₀ := (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans ef
  let ea := e₀.trans Representation.SL2FourNatural.alternatingFiveEquiv.symm
  have hk : Nat.card Representation.SL2FourNatural.F = 4 := by
    rw [Nat.card_eq_fintype_card,Representation.SL2FourNatural.card_field]
  let ep : Representation.SL2FourNatural.SL ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) Representation.SL2FourNatural.F :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi Representation.SL2FourNatural.F)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  have ha : ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^2) :=
    ⟨Representation.SL2FourNatural.F,inferInstance,inferInstance,hk,⟨ea.trans ep⟩⟩
  exact source_linear_four_dihedral_exclusion_of_center_order h hB d hc hb hcomm hbc
    (Ne.symm hca) (.linear 2 (by decide) ha) ea eb g hga hgb hk
    (source_a5_dihedral_center_card_two h hB hS d hc hb hcomm hbc (Ne.symm hca) ef eb g hga hgb)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

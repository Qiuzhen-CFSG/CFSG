module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearBetaModule
public import Theory.Representation.SL2.FixedGeneratedFieldRatio
public import Theory.Representation.ElementaryAbelianAction
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Exact field and center parameters for arbitrary linear endpoints

The natural beta-core section gives q_beta²<=q_alpha. At alpha, construct
the actual conjugation representation of the earlier local group modulo
its two-core on Z_alpha. Two distinct beta centers are its disjoint Sylow
fixed spaces. Their orders bound |Z_beta| by q_alpha q_beta, and the source
center-generation theorem supplies fixed-space generation. No full-stabilizer
marking or ambient finiteness is required.

Writing q_alpha=2^n and q_beta=2^m, the center count gives dimension
n+m+s with 2m<=n. The fixed-generated representation lemma proves n=2m
and |Z_beta|=2^m. Thus both numerical restrictions are conclusions from
the genuine quotient actions, rather than additional profile assumptions.
Alpha-row selection and the nonlinear beta branch remain separate duties.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.6)(c,d) and (11.7)(c,d), printed pp.172--175.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
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
open Representation.RankOne.QuadraticRecognition

private theorem exists_center_action (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (a : Vertex (family P)) {D : Type*} [Group D]
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* D) :
    letI := source_center_elementary h a
    ∃ ρ : Representation (ZMod 2) D (Additive (Z (family P) a)),
      ∀ (l : d.localGroup a) (z : Additive (Z (family P) a)),
        ((ρ (e (QuotientGroup.mk' (pCore 2 (d.localGroup a)) l)) z).toMul : G) =
          (l : G) * z.toMul * (l : G)⁻¹ := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let H := d.localGroup a
  let V := Z (family P) a
  have hn : H ≤ normalizer (V : Set G) :=
    (d.local_le a).trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ a)).mp (Z_normal _ a))
  let α := V.normalizerMonoidHom.comp (inclusion hn)
  have hker : pCore 2 H ≤ α.ker := by
    intro l hl
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    have hh := (source_core_centralizes_center h a)
      (by rw [←localGroup_core_eq (family P) d a]; exact mem_map_of_mem H.subtype hl)
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


private theorem representation_generated_of_ambient_span
    {H D : Type*} [Group H] [Group D] (V : Subgroup G) [IsElementaryAbelian 2 V]
    (j : H →* G) (T : Subgroup H) (q : H →* D)
    (ρ : Representation (ZMod 2) D (Additive V))
    (hspan : conjugateSpanBy (V ⊓ centralizer (T.map j : Set G)) j.range = V)
    (hact : ∀ (g : H) (w : Additive V),
      ((ρ (q g) w).toMul : G) = j g * w.toMul * (j g)⁻¹) :
    GeneratedByFixedSpace ρ (T.map q) := by
  let A := T.map q
  let W := ⨆ d : D, (fixedSpace ρ A).map (ρ d)
  let C : Subgroup G := W.toAddSubgroup.toSubgroup.map V.subtype
  have hfixed (z : G) (hz : z ∈ V) (hc : z ∈ centralizer (T.map j : Set G)) :
      Additive.ofMul (⟨z,hz⟩ : V) ∈ fixedSpace ρ A := by
    intro a
    obtain ⟨t,ht,he⟩ := a.property
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((ρ a.val (Additive.ofMul (⟨z,hz⟩ : V))).toMul : G) = z
    rw [←he,hact]
    change j t * z * (j t)⁻¹ = z
    rw [hc (j t) (mem_map_of_mem _ ht),mul_inv_cancel_right]
  have hVC : V ≤ C := by
    rw [←hspan]
    apply (closure_le _).mpr
    rintro x ⟨_,⟨g,rfl⟩,z,hz,rfl⟩
    have hw : ρ (q g) (Additive.ofMul (⟨z,hz.1⟩ : V)) ∈ W :=
      (le_iSup (fun d : D => (fixedSpace ρ A).map (ρ d)) (q g))
        ⟨_,hfixed z hz.1 hz.2,rfl⟩
    exact ⟨(ρ (q g) (Additive.ofMul (⟨z,hz.1⟩ : V))).toMul,hw,hact g _⟩
  apply top_unique
  intro w _
  obtain ⟨z,hz,he⟩ := hVC w.toMul.property
  have he' : Additive.ofMul z = w := Additive.toMul.injective (Subtype.ext he)
  exact he' ▸ hz


variable {k : Type*} [Field k] [Finite k] [CharP k 2]
variable {k' : Type*} [Field k'] [Finite k'] [CharP k' 2]

/-- The exact two linear field degrees and beta-center order, from the
actual local conjugation action and the source seed identities. -/
theorem source_linear_linear_parameters (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k'))
    (n m : ℕ) (_hn : 0 < n) (hm : 0 < m) (hk : Nat.card k = 2^n) (hk' : Nat.card k' = 2^m)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    n = 2*m ∧ Nat.card (Z (family P) b) = 2^m := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let H := d.localGroup a
  let V := Z (family P) a
  let A := Z (family P) b
  let C := Z (family P) (g • b)
  let : Finite H := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  let : Finite V := Finite.of_injective
    (inclusion (Z_le_stabilizer _ a)) (inclusion_injective _)
  let : Finite A := Finite.of_injective
    (inclusion (Z_le_stabilizer _ b)) (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  have hVne : V ≠ ⊥ := by
    intro he
    apply hc.2
    change V ≤ U (family P) b
    rw [he]
    exact bot_le
  let : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hVne
  let q := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := ea.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨ρ,hact⟩ := exists_center_action h d a ea
  have hab' : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [show g • a = a from hga] at hh
  have hc' : IsCriticalPair (family P) a (g • b) := by
    simpa only [show g • a = a from hga] using criticalPair_translate (family P) hc g
  have hcomm' : ⁅Z (family P) a,Z (family P) (g • b)⁆ = ⊥ := by
    have hh := commuting_centers_translate (family P) a b g
    simpa only [show g • a = a from hga,hcomm,Subgroup.map_bot] using hh
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hab'
  have hfT := fixedSpace_eq_ambient V H A q ρ hact T
    (hT ▸ center_fixed_edge h hB hS hc hb hcomm)
  have hfR := fixedSpace_eq_ambient V H C q ρ hact R
    (hR ▸ center_fixed_edge h hB hS hc' hb hcomm')
  have hAV : A ≤ V := source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hab.symm
  have hdis : Disjoint A C := source_linear_rankOne_beta_centers_disjoint
    h hB d hc hb hcomm hbc hac Ma Mb ea g hga hgb
  have hfix : ρ.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    have hTv : v ∈ fixedSpace ρ ((T : Subgroup H).map q) := fun u => hv u.val
    have hRv : v ∈ fixedSpace ρ ((R : Subgroup H).map q) := fun u => hv u.val
    rw [hfT] at hTv
    rw [hfR] at hRv
    change (v.toMul : G) ∈ A at hTv
    change (v.toMul : G) ∈ C at hRv
    change v = 0
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mem_bot.mp (hdis.le_bot ⟨hTv,hRv⟩)
  have hgen : RankOne.QuadraticRecognition.GeneratedByFixedSpace ρ (T.mapSurjective hq) := by
    apply representation_generated_of_ambient_span V H.subtype T q ρ _ hact
    rw [range_subtype,hT]
    obtain ⟨T',hT'⟩ := source_edge_vertex_sylow h hS hab
    have he := sylow_image_eq_edge_core (stabilizer (family P) a) _ inf_le_left
      (source_edge_core_sylow h hB hab) T' hT'
    rw [←he]
    exact CommutingNontrivial.source_center_fixed_generation h d a T'
  have hfixedcard : Nat.card (fixedSpace ρ (T.mapSurjective hq)) = Nat.card A := by
    change Nat.card (fixedSpace ρ ((T : Subgroup H).map q)) = _
    rw [hfT]
    change Nat.card (A.subgroupOf V) = Nat.card A
    exact Nat.card_congr (subgroupOfEquivOfLe hAV).toEquiv
  have hratio : Nat.card V = Nat.card k' * Nat.card k * Nat.card A :=
    (source_linear_linear_center_card_ratio h hB d hc hb hcomm hbc hac Ma ea Mb eb).2
  have hcount : Nat.card (Additive V) =
      2^m * Nat.card k * Nat.card (fixedSpace ρ (T.mapSurjective hq)) := by
    rw [hfixedcard,←hk']
    exact hratio
  have hCV : C ≤ V := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hAV
    rwa [←Z_translate,←Z_translate,show g • a = a from hga] at hh
  have hnorm : C ≤ normalizer (A : Set G) :=
    (hCV.trans ((le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative V)).trans (centralizer_le hAV))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hCcard : Nat.card C = Nat.card A := by
    dsimp [C,A]
    rw [Z_translate,card_map_of_injective (MulAut.conj g).injective]
  have hprod := card_sup_eq_mul_of_normalizes_of_disjoint A C hnorm hdis
  rw [hCcard] at hprod
  have hupper := Nat.card_le_card_of_injective (inclusion (sup_le hAV hCV))
    (inclusion_injective _)
  rw [hprod,hratio] at hupper
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hbound : Nat.card (fixedSpace ρ (T.mapSurjective hq)) ≤ 2^m * Nat.card k := by
    rw [hfixedcard,←hk']
    nlinarith
  have hmn : 2*m ≤ n := by
    have hh := source_linear_linear_beta_square_le h hB d hc hb hcomm hbc hac Ma ea Mb eb
    rw [hk,hk',←pow_mul,Nat.mul_comm m 2] at hh
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  have hp := Representation.SL2.field_ratio_of_fixed_generated_order ρ (T.mapSurjective hq)
    hgen hfix hm hmn hk hcount hbound
  exact ⟨hp.1,hfixedcard ▸ hp.2⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

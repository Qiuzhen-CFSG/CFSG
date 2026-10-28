module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CubicPathActor
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.SL2SylowFixedRecognition.Complementary
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.Transport

/-!
# Exact center order in the cubic A₅ branch

The order-three path actor reduces the beta-center order to two or eight.
Distinct beta centers at an alpha turn are disjoint. If their order were
eight, their product would be the whole alpha center of order 64. These
are precisely the fixed spaces of two Sylow subgroups in the literal
quotient action. Complementary Sylow fixed-space recognition for SL₂(4)
then makes that action a sum of natural binary modules, whose dimensions
are divisible by four, contradicting dimension six.

The quotient action is constructed from conjugation on the actual center;
no module-recognition conclusion is included in the hypotheses.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.6)(b,c), printed pp.172--174, specialized to the cubic A₅ branch.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
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

/-- Distinct beta centers at an alpha turn are disjoint. -/
theorem source_cubic_a5_beta_centers_disjoint (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Disjoint (Z (family P) b) (Z (family P) (g • b)) := by
  let := finite_endpoints h
  have hsep := source_cubic_a5_neighbor_intersection_separated h hB hS hc hb hbc hac hcard
    e g hga hgb
  have hZgc : Z (family P) (g • b) ≤ Q (family P) (g • c) := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
      ((source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hbc).trans
        ((source_Z_Q_U h c).1.trans (map_subtype_le _)))
    rwa [←Z_translate,←Q_translate] at hh
  exact disjoint_iff.mpr (bot_unique ((inf_le_inf
    (source_commuting_one_center_le_neighbor_intersection h hB hS hc hb hcomm) hZgc).trans hsep.le))

private theorem center_pair_span_of_eight (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
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
  have hd := source_cubic_a5_beta_centers_disjoint h hB hS hc hb hcomm hbc hac hcard e g hga hgb
  have hcount := card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hd
  have hgcard : Nat.card (Z (family P) (g • b)) = Nat.card (Z (family P) b) := by
    rw [Z_translate,card_map_of_injective (MulAut.conj g).injective]
  rw [hgcard,h8] at hcount
  have hratio := source_cubic_a5_center_card_ratio h hB hS hc hb hcomm hbc hac hcard e
  rw [h8] at hratio
  exact eq_of_le_of_card_ge (sup_le hZa hZga) (by omega)

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

/-- The exact beta-center order in the cubic A₅ branch. -/
theorem source_cubic_a5_center_card_two (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Nat.card (Z (family P) b) = 2 := by
  rcases source_cubic_a5_center_card_two_or_eight h hB hS hc hb hcomm hbc hac hcard e g hga hgb with h2 | h8
  · exact h2
  exfalso
  let := finite_endpoints h
  let := source_center_elementary h a
  let H := stabilizer (family P) a
  let V := Z (family P) a
  let A := Z (family P) b
  let C := Z (family P) (g • b)
  let : Finite V := Finite.of_injective (inclusion (Z_le_stabilizer _ a)) (inclusion_injective _)
  let es := e.trans Representation.SL2FourNatural.alternatingFiveEquiv.symm
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
  have hd := source_cubic_a5_beta_centers_disjoint h hB hS hc hb hcomm hbc hac hcard e g hga hgb
  have hs := center_pair_span_of_eight h hB hS hc hb hcomm hbc hac hcard e g hga hgb h8
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
  have hh := source_cubic_a5_center_card_ratio h hB hS hc hb hcomm hbc hac hcard e
  rw [h8] at hh
  exact hh

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

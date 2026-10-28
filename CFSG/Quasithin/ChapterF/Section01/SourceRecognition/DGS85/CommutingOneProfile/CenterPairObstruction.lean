module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NonquadraticSeeds
public import Theory.Representation.RankOne.QuadraticRecognition.ElementFixedSpaces
public import Theory.Representation.ElementaryAbelianAction

/-!
# Two beta centers cannot span the alpha center

On an alpha turn, the two beta centers are the disjoint fixed spaces of
the actual edge Sylows acting on Z_alpha. If they spanned Z_alpha, the
binary SL2 complementary-fixed-space theorem would make the whole Sylow
quadratic. Its opposite seed would then be quadratic as well, contradicting
(11.3)(f). The proof constructs the original conjugation action and retains
its quotient map. Every beta catalogue row and every binary alpha field
are allowed; no center order or irreducibility is assumed.

RemoteLayerVanishing uses this obstruction to kill the remaining layer on
the escaping source turn. Source: DGS85, Groups and Graphs (1985), proof
of (11.6), printed p.173, equation (*) and its even-characteristic contradiction.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

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



/-- Complementary beta centers would make the alpha Sylow quadratic. -/
theorem source_linear_rankOne_center_pair_ne
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Z (family P) a ≠ Z (family P) b ⊔ Z (family P) (g • b) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let H := d.localGroup a
  let : Finite H := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  let V := Z (family P) a
  let A := Z (family P) b
  let C := Z (family P) (g • b)
  let q := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := ea.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨ρ,hact⟩ := exists_center_action h d a ea
  change ∀ (l : H) (z : Additive V), ((ρ (q l) z).toMul : G) =
    (l : G) * z.toMul * (l : G)⁻¹ at hact
  have hab := source_critical_one_adjacent hc hb
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
  have hdis : Disjoint A C := source_linear_rankOne_beta_centers_disjoint
    h hB d hc hb hcomm hbc hac Ma Mb ea g hga hgb
  intro hspan
  change V = A ⊔ C at hspan
  have hAV : A ≤ V := le_sup_left.trans hspan.ge
  have hCV : C ≤ V := le_sup_right.trans hspan.ge
  have hcomp : IsCompl (fixedSpace ρ (T.mapSurjective hq)) (fixedSpace ρ (R.mapSurjective hq)) := by
    constructor
    · apply disjoint_iff.mpr
      apply bot_unique
      intro z hz
      change z ∈ fixedSpace ρ ((T : Subgroup H).map q) ⊓
        fixedSpace ρ ((R : Subgroup H).map q) at hz
      rw [hfT,hfR] at hz
      apply Additive.toMul.injective
      apply Subtype.ext
      exact mem_bot.mp (hdis.le_bot ⟨hz.1,hz.2⟩)
    · apply codisjoint_iff.mpr
      apply top_unique
      intro z _
      have hz : (z.toMul : G) ∈ A ⊔ C := hspan ▸ z.toMul.property
      have hn : A ≤ normalizer (C : Set G) :=
        (hAV.trans (V.le_centralizer.trans (centralizer_le hCV))).trans
          (Subgroup.centralizer_le_normalizer _)
      rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right A C hn] at hz
      obtain ⟨x,hx,y,hy,hxy⟩ := hz
      apply Submodule.mem_sup.mpr
      refine ⟨Additive.ofMul (⟨x,hAV hx⟩ : V),?_,Additive.ofMul (⟨y,hCV hy⟩ : V),?_,?_⟩
      · change _ ∈ fixedSpace ρ ((T : Subgroup H).map q)
        rw [hfT]
        exact hx
      · change _ ∈ fixedSpace ρ ((R : Subgroup H).map q)
        rw [hfR]
        exact hy
      · exact Additive.toMul.injective (Subtype.ext hxy)
  have hquad := (Representation.SL2SylowFixedRecognition.fixedSpaceHypotheses_of_isCompl
    ρ (T.mapSurjective hq) (R.mapSurjective hq) hcomp).quadratic
  let S := (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2
  change (T : Subgroup H).map H.subtype = S at hT
  have hSL : S ≤ H := hT ▸ map_subtype_le _
  have hST (t : G) (ht : t ∈ S) : (⟨t,hSL ht⟩ : H) ∈ (T : Subgroup H) := by
    obtain ⟨u,hu,he⟩ := (hT.symm ▸ ht)
    exact (Subtype.ext he : u = ⟨t,hSL ht⟩) ▸ hu
  have hdisplace : ⁅S,V⁆ ≤ centralizer (S : Set G) := by
    apply commutator_le.mpr
    intro t ht z hz
    have htq : q ⟨t,hSL ht⟩ ∈ (T.mapSurjective hq : Subgroup SL(2,k)) :=
      mem_map_of_mem q (hST t ht)
    let w : Additive V := Additive.ofMul ⟨z,hz⟩
    have he (u : G) (hu : u ∈ S) :
        u * (t*z*t⁻¹*z⁻¹) * u⁻¹ = t*z*t⁻¹*z⁻¹ := by
      have hh := congrArg (fun v : Additive V => (v.toMul : G))
        (hquad (q ⟨u,hSL hu⟩) (mem_map_of_mem q (hST u hu))
          (q ⟨t,hSL ht⟩) htq w)
      change ((ρ (q ⟨u,hSL hu⟩) (ρ (q ⟨t,hSL ht⟩) w - w)).toMul : G) =
        ((ρ (q ⟨t,hSL ht⟩) w - w).toMul : G) at hh
      rw [hact] at hh
      simp only [toMul_sub,div_eq_mul_inv] at hh
      change u * (((ρ (q ⟨t,hSL ht⟩) w).toMul : G) * z⁻¹) * u⁻¹ =
        ((ρ (q ⟨t,hSL ht⟩) w).toMul : G) * z⁻¹ at hh
      rw [hact] at hh
      exact hh
    intro u hu
    simpa only [commutatorElement_def] using mul_inv_eq_iff_eq_mul.mp (he u hu)
  apply source_linear_rankOne_seed_nonquadratic h hB d hc hb hcomm hbc hac Ma Mb ea
  have hES : Z (family P) c ⊓ Q (family P) b ≤ S := inf_le_right.trans
    (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm)
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [commutator_comm]
  exact ((commutator_mono hES le_rfl).trans hdisplace).trans (centralizer_le hES)



end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

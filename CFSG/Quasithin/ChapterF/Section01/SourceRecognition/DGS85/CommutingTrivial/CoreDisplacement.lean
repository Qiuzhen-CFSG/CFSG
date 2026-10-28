module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborSylow
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.InitialGeometry
public import Theory.GroupTheory.Commutator.NormalSpan
public import Theory.Representation.RankOne.QuadraticRecognition.NaturalDefinition

/-!
# Neighboring core displacement and the natural-center commutator

A quadratic Sylow action on the actual neighboring center places each core
commutator in the common Sylow omega-center. Local conjugate generation
propagates this bound to the entire radius-one span. When the original
center is natural, a nonidentity Sylow displacement covers its fixed space;
this proves both [Q_w,Z_v] = Z_w and [V_w,Q_w] = Z_w.

These are the commutator steps of DGS 9.4(c), retaining the preceding
natural-center premise of 9.4(a), the actual quotient and its conjugation
formula. `ResidualDescent` uses the upper bound on the literal residual
section. Quotient recognition and the preceding natural-center assertion
remain Chapter 9 obligations, not consequences of this module.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
9.4, printed pp.142--143, and natural-module properties (ii)--(iii), p.113.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Quadraticity of the adjacent center bounds its core displacement by the
actual Sylow omega-center at the other endpoint. -/
theorem neighbor_center_core_displacement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {D : Type*} [Group D]
    (q : graphLocalGroup (family P) v →* D)
    (T : Sylow 2 D)
    (hT : ((Q (family P) w).subgroupOf (graphLocalGroup (family P) v)).map q = T) :
    letI := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) v
    ∀ ρ : Representation (ZMod 2) D (Additive (Z (family P) v)),
      (∀ (l : graphLocalGroup (family P) v) (z : Additive (Z (family P) v)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      IsQuadratic ρ T → ⁅Q (family P) w, Z (family P) v⁆ ≤ Z (family P) w := by
  let := finite_endpoints h
  let := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) v
  intro ρ hact hquad
  let F := family P
  let H := graphLocalGroup F v
  obtain ⟨S, R, hSR⟩ := source_common_edge_sylow h hB hS hvw
  let E := (S : Subgroup (stabilizer F v)).map (stabilizer F v).subtype
  have hEH : E ≤ H := sylow_le_sylowGenerated _ S
  have hQE : Q F w ≤ E := (pCoreIn_le_sylow _ R).trans hSR.ge
  have hZQ : Z F v ≤ Q F v := (source_Z_Q_U h v).1.trans (map_subtype_le _)
  have hZE : Z F v ≤ E := hZQ.trans (pCoreIn_le_sylow _ S)
  have hEp : IsPGroup 2 E := S.isPGroup'.map _
  have hEq : (E.subgroupOf H).map q ≤ T := by
    have ht : (T : Subgroup D) ≤ (E.subgroupOf H).map q := by
      rw [← hT]
      exact map_mono (comap_mono hQE)
    exact (T.is_maximal' ((hEp.comap_subtype (K := H)).map q) ht).le
  have hQH : Q F w ≤ H := neighbor_core_le_localGroup h hB hS hvw
  apply commutator_le.mpr
  intro a ha z hz
  let l : H := ⟨a, hQH ha⟩
  let u : Additive (Z F v) := Additive.ofMul ⟨z,hz⟩
  let d := ρ (q l) u - u
  have hqa : q l ∈ (T : Subgroup D) := hT ▸ mem_map_of_mem q ha
  have hd : (d.toMul : G) = ⁅a,z⁆ := by
    dsimp only [d]
    rw [toMul_sub, div_eq_mul_inv]
    change ((ρ (q l) u).toMul : G) * (u.toMul : G)⁻¹ = _
    rw [hact]
    rfl
  have hdE : (d.toMul : G) ∈ E := hZE d.toMul.property
  have hdC : (d.toMul : G) ∈ centralizer (E : Set G) := by
    intro s hs
    let t : H := ⟨s,hEH hs⟩
    have hqt : q t ∈ (T : Subgroup D) := hEq (mem_map_of_mem q hs)
    have hf := hquad (q t) hqt (q l) hqa u
    have hh := congrArg (fun x : Additive (Z F v) => (x.toMul : G)) hf
    rw [hact] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hdO : (d.toMul : G) ∈ omegaCenterIn E :=
    (mem_omegaCenterIn_iff _ _).mpr ⟨hdE,hdC,
      elemPow_eq_one_of_isElementaryAbelian _ d.toMul.property⟩
  rw [hd] at hdO
  have he : omegaCenterIn E ≤ Z F w := by
    dsimp only [E]
    rw [hSR]
    exact le_iSup (fun R : Sylow 2 (stabilizer F w) =>
      omegaCenterIn ((R : Subgroup (stabilizer F w)).map (stabilizer F w).subtype)) R
  exact he hdO

/-- The original local conjugate span propagates a seed displacement bound
without any normality assumption on the ambient completion. -/
theorem neighborhood_core_displacement_of_seed
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hseed : ⁅Q (family P) w, Z (family P) v⁆ ≤ Z (family P) w) :
    ⁅V (family P) w 1, Q (family P) w⁆ ≤ Z (family P) w := by
  let := finite_endpoints h
  let F := family P
  let H := graphLocalGroup F w
  have hnZ : H ≤ normalizer (Z F w : Set G) :=
    (sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z F w)
  have hZH : Z F v ≤ H := ((source_Z_Q_U h v).1.trans (map_subtype_le _)).trans
    (neighbor_core_le_localGroup h hB hS hvw.symm)
  rw [CommutingThreeProfile.V_eq_center_sup_neighbor_conjugates F H (sylowGenerated_le _) hvw.symm
    (fun z hz => graphLocalGroup_transitive h hB hS w ⟨v,hvw.symm⟩ ⟨z,hz⟩)]
  apply commutator_sup_le_of_relative_normal H _ _ _ _ hnZ
    (((source_Z_Q_U h w).1.trans (map_subtype_le _)).trans (core_le_graphLocalGroup h w))
    (conjugateSpanBy_le_self hZH)
  · exact le_normalizer_iff_commutator_le_left.mp
      ((Q_le_stabilizer F w).trans (CommutingNontrivial.stabilizer_normalizes_Z F w))
  · rw [commutator_conjugateSpanBy_of_normalized_right _ H _ hZH
      ((sylowGenerated_le _).trans (stabilizer_normalizes_Q F w))]
    exact conjugateSpanBy_le ((commutator_comm _ _).trans_le hseed) hnZ

/-- A quadratic Sylow on the adjacent center supplies the whole neighborhood
core-displacement bound. The local quotient at w is not assumed linear. -/
theorem linear_neighbor_quadratic_core_displacement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hne : ¬ Q (family P) w ≤ Q (family P) v)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    letI := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) v
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) v)))
    ∀ ρ : Representation (ZMod 2) SL(2,F) (Additive (Z (family P) v)),
      (∀ (l : graphLocalGroup (family P) v) (z : Additive (Z (family P) v)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      (∃ S : Sylow 2 SL(2,F), IsQuadratic ρ S) →
      ⁅V (family P) w 1, Q (family P) w⁆ ≤ Z (family P) w := by
  let := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) v
  dsimp only
  intro ρ hact ⟨S,hquad⟩
  obtain ⟨T,hT,_⟩ := linear_neighbor_core_sylow_image h hB hS hvw hne e
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) S T
  have hquad' := SL2SylowFixedRecognition.quadratic_conjugate ρ hquad g
  exact neighborhood_core_displacement_of_seed h hB hS hvw
    (neighbor_center_core_displacement h hB hS hvw _ _ hT ρ hact hquad')

open Representation.RankOne.QuadraticRecognition

private theorem natural_fixed_range
    {F W : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2,F) W) (hf : Function.Injective ρ)
    (T : Sylow 2 SL(2,F)) {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hnat : IsSourceNatural ρ T n) :
    ∃ t ∈ (T : Subgroup SL(2,F)), LinearMap.range (ρ t - LinearMap.id) = fixedSpace ρ T := by
  have hc : Nat.card T = 2^n := (Nat.card_congr
    (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv).trans hF
  have hne : (T : Subgroup SL(2,F)) ≠ ⊥ := by
    intro hbot
    change Nat.card (T : Subgroup SL(2,F)) = 2^n at hc
    rw [hbot,card_bot] at hc
    have hh : 1 < 2^n := one_lt_pow₀ (by decide) (by omega)
    omega
  obtain ⟨t,ht,ht1⟩ := (T : Subgroup SL(2,F)).bot_or_exists_ne_one.resolve_left hne
  obtain ⟨_,hcard,hfix,_⟩ := sourceNatural_coordinates_and_consequences ρ hf T hn hF hnat
  have hdim : Module.finrank (ZMod 2) W = 2*n := by
    have hh := hnat.1
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hh
  have hdF : Module.finrank (ZMod 2) (fixedSpace ρ T) = n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
    exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hcard
  refine ⟨t,ht,Submodule.eq_of_le_of_finrank_le ?_ ?_⟩
  · rintro _ ⟨x,rfl⟩ s
    exact hnat.2.2 s s.property t ht x
  · have hadd := fixedCodim_add_finrank ρ (zpowers t)
    rw [hfix t ht ht1,hdF,hdim,fixedCodim_zpowers_eq_displacement_rank] at hadd
    omega

/-- Source 9.4(c) from the preceding natural-center assertion: the
commutator is the full original central omega, including the binary field. -/
theorem linear_natural_neighbor_core_commutator
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hne : ¬ Q (family P) w ≤ Q (family P) v)
    (hz : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    letI := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) v
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) v)))
    ∀ ρ : Representation (ZMod 2) SL(2,F) (Additive (Z (family P) v)),
      (∀ (l : graphLocalGroup (family P) v) (z : Additive (Z (family P) v)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      Function.Injective ρ → (∃ S : Sylow 2 SL(2,F), IsSourceNatural ρ S n) →
      ⁅Q (family P) w, Z (family P) v⁆ = Z (family P) w ∧
      ⁅V (family P) w 1, Q (family P) w⁆ = Z (family P) w := by
  let := finite_endpoints h
  let := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) v
  let : Finite (Z (family P) v) := Finite.of_injective
    (inclusion (Z_le_stabilizer (family P) v)) (inclusion_injective _)
  let F₀ := family P
  let H := graphLocalGroup F₀ v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  dsimp only
  intro ρ hact hf ⟨S,hnat⟩
  obtain ⟨T,hT,_⟩ := linear_neighbor_core_sylow_image h hB hS hvw hne e
  have hquad : IsQuadratic ρ T := by
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) S T
    exact SL2SylowFixedRecognition.quadratic_conjugate ρ hnat.2.2 g
  have hnatT : IsSourceNatural ρ T n := ⟨hnat.1,hnat.2.1,hquad⟩
  have hupper := neighbor_center_core_displacement h hB hS hvw q T hT ρ hact hquad
  have hZwZv : Z F₀ w ≤ Z F₀ v := hz ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hvw.symm
  obtain ⟨t,ht,hrange⟩ := natural_fixed_range ρ hf T hn hF hnatT
  have hlower : Z F₀ w ≤ ⁅Q F₀ w,Z F₀ v⁆ := by
    intro z hz'
    let u : Additive (Z F₀ v) := Additive.ofMul ⟨z,hZwZv hz'⟩
    have hu : u ∈ fixedSpace ρ T := by
      intro a
      obtain ⟨l,hl,he⟩ := show a.val ∈ ((Q F₀ w).subgroupOf H).map q from hT.symm ▸ a.property
      apply Additive.toMul.injective
      apply Subtype.ext
      change ((ρ a.val u).toMul : G) = z
      rw [←he,hact]
      have hcz := (CommutingNontrivial.Z_centralizes_Q F₀ w (source_Z_Q_U h w).1) hz'
      exact mul_inv_eq_iff_eq_mul.mpr (hcz l hl)
    obtain ⟨x,hx⟩ := hrange.symm ▸ hu
    obtain ⟨l,hl,he⟩ := show t ∈ ((Q F₀ w).subgroupOf H).map q from hT.symm ▸ ht
    have hh := congrArg (fun y : Additive (Z F₀ v) => (y.toMul : G)) hx
    change ((ρ t x - x).toMul : G) = z at hh
    rw [toMul_sub,div_eq_mul_inv] at hh
    change ((ρ t x).toMul : G) * (x.toMul : G)⁻¹ = z at hh
    rw [←he,hact] at hh
    exact hh ▸ commutator_mem_commutator hl x.toMul.property
  have heq := le_antisymm hupper hlower
  refine ⟨heq,le_antisymm (neighborhood_core_displacement_of_seed h hB hS hvw hupper) ?_⟩
  rw [←heq,commutator_comm]
  exact commutator_mono (CommutingNontrivial.Z_neighbor_le_V F₀ hvw.symm) le_rfl

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

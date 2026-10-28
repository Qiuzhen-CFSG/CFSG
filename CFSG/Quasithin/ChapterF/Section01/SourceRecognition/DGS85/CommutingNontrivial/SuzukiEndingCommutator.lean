module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FactorBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RankOneEndingCommutator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PairedIndexGeometry
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiElementBounds
public import Theory.SpecificGroups.Suzuki.TwoRank

/-!
# DGS 8.3 for every Suzuki ending quotient

A nonidentity element of the critical center image acts on an actual
irreducible constituent of the ending residual section. The Suzuki
individual-involution bound gives a fixed-space index at least q².
Both opposite neighborhood actors have order at most q. Original core
intersection products and the moving-orbit rank bound therefore give the
first paired square inequality. Reciprocal escape selects a genuine
critical configuration for the second inequality, and conjugation transports
the same Suzuki quotient to its ending vertex. No reverse failure or
whole-residual action descent is needed.

The terminal unitary comparison then proves the quotient-omega commutator
inclusion at every chosen moving neighbor for a nonbinary Suzuki ending.
The reduced application constructs that neighbor and its full-edge Sylow,
and includes Sz(2) through the binary-ending result. All literal quotient
maps, the earlier 6.5 obstruction, and the complete local model catalogue
are retained. Linear and unitary ending cases and 8.4--8.7 remain separate.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(5.10)(b) and the paired estimates in (8.3)(2), pp.110--112, 135--137.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CommutingTrivial BenderSuzuki.MatrixGroups
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem suzuki_elementary_field_square {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (m : ℕ) (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) W)
    (hf : Function.Injective ρ) (A : Subgroup (SuzukiMatrixGroup m))
    [IsElementaryAbelian 2 A] (hne : A ≠ ⊥) :
    (2^(2*m+1))^2 ≤ Nat.card (W ⧸ fixedSpace ρ A) := by
  obtain ⟨t,htA,ht1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have ht2 : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t htA) ht1
  have hlo := suzuki_element_fixed_index m ρ hf t ht2
  have hmono := NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr htA)
  have hindex : Nat.card (W ⧸ fixedSpace ρ (zpowers t)) ≤
      Nat.card (W ⧸ fixedSpace ρ A) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W ⧸ fixedSpace ρ (zpowers t)),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W ⧸ fixedSpace ρ A),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hmono
  have hpow : (2^(2*m+1))^2 = 2^(2*(2*m+1)) := by rw [←pow_mul,Nat.mul_comm (2*m+1) 2]
  exact hpow ▸ hlo.trans hindex

/-- The original critical center moves at least the square of the Suzuki
field order on the ending neighborhood, via an actual faithful constituent. -/
theorem reduced_ending_suzuki_field_square (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (m : ℕ)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* SuzukiMatrixGroup m) :
    let Γ := Reduction.reducedFamily L S₀
    (2^(2*m+1)) ^ 2 ≤
      (centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a'
  let A := (V Γ a' 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((Z Γ a).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ a' H (sylowGenerated_le _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_ending_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2 H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite d.space.toSubmodule := d.finiteSpace
  let : d.action.IsIrreducible := d.irreducible
  let : Nontrivial d.space.toSubmodule := Subrepresentation.irreducible_module_nontrivial d.action
  have hf := CommutingNontrivial.suzuki_quotient_action_faithful m e d.action d.residualFixed
  let : IsElementaryAbelian 2 Aq := d.elementary
  have hne : Aq ≠ ⊥ := by
    intro he
    have hcard : Nat.card Aq = (Q Γ a').relIndex (Z Γ a) := d.actorCard
    rw [he,card_bot] at hcard
    exact hc.2 ((relIndex_eq_one.mp hcard.symm).trans (source_Z_Q_U ht a').2)
  exact (suzuki_elementary_field_square m d.action hf Aq hne).trans d.fixedIndex

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem index_product (U Q K : Subgroup G) (h : U ⊓ Q ≤ K) :
    K.relIndex U * Q.relIndex (U ⊓ K) = Q.relIndex U := by
  rw [Nat.mul_comm,inf_comm U K,relIndex_inf_mul_relIndex]
  rw [←inf_relIndex_right (Q ⊓ K) U,←inf_relIndex_right Q U]
  congr 1
  ext x
  exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨⟨hx.1,h ⟨hx.2,hx.1⟩⟩,hx.2⟩⟩

private theorem elementary_index_of_rank (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup v)
    (n : ℕ) (hr : primeRank 2 (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≤ n) :
    (Q (family P) v).relIndex A ≤ 2^n := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 L)
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hi := Representation.BinaryConjugationSection.actor_image_card_eq_relIndex L
    (Q (family P) v) A q (local_quotient_kernel (family P) d v (MulEquiv.refl _)) hAL
  exact hi ▸ (primeRank_le_iff_elementary_card_le _).mp hr _ inferInstance

private theorem elementary_index_at_same_type (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) {v w : Vertex (family P)}
    (ht : v.type = w.type) (n : ℕ)
    (hr : primeRank 2 (d.localGroup w ⧸ pCore 2 (d.localGroup w)) ≤ n)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup v) :
    (Q (family P) v).relIndex A ≤ 2^n := by
  let := finite_endpoints h
  obtain ⟨g,rfl⟩ := (same_orbit_iff (family P) v w).mpr ht
  let e := MulAut.conj g
  let E := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hEL : E ≤ d.localGroup (g • v) := by rw [d.conjugate]; exact map_mono hAL
  have hh := elementary_index_of_rank h d (g • v) E hEL n hr
  rw [Q_translate,relIndex_map_map_of_injective _ _ e.injective] at hh
  exact hh

private theorem paired_square_of_field_bound (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' w : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (M : IsRankOneModel (d.localGroup beta ⧸ pCore 2 (d.localGroup beta)))
    (k m : ℕ)
    (hr : primeRank 2 (d.localGroup a' ⧸ pCore 2 (d.localGroup a')) ≤ k)
    (hrw : primeRank 2 (d.localGroup w ⧸ pCore 2 (d.localGroup w)) ≤ m)
    (htype : a.type = w.type)
    (hlower : (2^k)^2 ≤ (centralizer (Z (family P) a : Set G)).relIndex (V (family P) a' 1)) :
    (Q (family P) a').relIndex (V (family P) beta 1)^2 ≤
      (Q (family P) beta).relIndex (V (family P) a' 1) * 2^m := by
  let := finite_endpoints h
  let F := family P
  have hb3 : 3 ≤ b F := (source_critical_geometry h d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V F a' 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) a'
  let A := V F a' 1 ⊓ Q F beta
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  have hAL : A ≤ d.localGroup a := pGroup_le_localGroup F d a A
    (IsElementaryAbelian.isPGroup 2 A)
    (inf_le_right.trans ((source_Z_Q_U h beta).2.trans
      ((ballKernel_one_le_edge F hab.symm).trans inf_le_right)))
  have hsecondary := elementary_index_at_same_type h d htype m hrw A hAL
  have hfinite : V F a' 1 ≤ stabilizer F a' :=
    V_le_stabilizer_of_dist_add_le_b F h.generate a' a' 1
      (by simp only [SimpleGraph.dist_self,zero_add]; exact hb.le)
  let : Finite (V F a' 1) := Finite.of_injective (inclusion hfinite) (inclusion_injective _)
  have hcentral := relIndex_le_of_le_left
    (le_centralizer_iff.mp (Z_centralizes_Q F a (source_Z_Q_U h a).1))
    (((Q F a).subgroupOf (V F a' 1)).index_ne_zero_of_finite)
  have hproduct := index_product (V F a' 1) (Q F a) (Q F beta)
    (source_reverse_core_intersection h hB d hc hab hd hb hcomm M)
  obtain ⟨hactor,_⟩ := source_ending_rank_actor_bounds h d hc hab hd hb hcomm k hr
  calc
    (Q F a').relIndex (V F beta 1)^2 ≤ (2^k)^2 := Nat.pow_le_pow_left hactor 2
    _ ≤ (centralizer (Z F a : Set G)).relIndex (V F a' 1) := hlower
    _ ≤ (Q F a).relIndex (V F a' 1) := hcentral
    _ = (Q F beta).relIndex (V F a' 1) * (Q F a).relIndex A := hproduct.symm
    _ ≤ (Q F beta).relIndex (V F a' 1) * 2^m := Nat.mul_le_mul_left _ hsecondary

/-- Both source paired estimates for a nonbinary Suzuki ending. The only
numerical input is the rank of the actual quotient in the moving orbit;
there is no reverse nonzero-commutator or failure premise. -/
theorem reduced_suzuki_paired_square
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',V (Reduction.reducedFamily L S₀) a' 1⁆ ≠ ⊥)
    (k : ℕ) (hk : 0 < k)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* SuzukiMatrixGroup k)
    (w : (graph (Reduction.reducedFamily L S₀)).neighborSet a')
    (m : ℕ)
    (hrw : primeRank 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)) ≤ m) :
    let F := Reduction.reducedFamily L S₀
    (Q F a').relIndex (V F beta 1)^2 ≤ (Q F beta).relIndex (V F a' 1) * 2^m ∧
      (Q F beta).relIndex (V F a' 1)^2 ≤ (Q F a').relIndex (V F beta 1) * 2^m := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : Finite (graphLocalGroup F a') :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (graphLocalGroup F beta) :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hr : primeRank 2 (d.localGroup a' ⧸ pCore 2 (d.localGroup a')) ≤ 2*k+1 := by
    change primeRank 2 (graphLocalGroup F a' ⧸ pCore 2 (graphLocalGroup F a')) ≤ _
    rw [primeRank_congr 2 e,suzuki_two_rank k hk]
  have haw : a.type = w.val.type := by
    have hodd := (source_critical_geometry ht d hc hab hd hb hcomm).1
    have hne : a.type ≠ a'.type := by
      intro he
      have heven := (even_dist_iff F ht.generate a a').mpr he
      rw [hc.1] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven
    have hw := w.property.1
    cases hat : a.type <;> cases hwt : w.val.type <;> cases het : a'.type <;> simp_all
  have hfirst := paired_square_of_field_bound ht (Reduction.reduced_borel_core_sylow h) d
    hc hab hd hb hcomm (models beta) (2*k+1) m hr hrw haw
    (reduced_ending_suzuki_field_square h hc hab hd hb hcomm k e)
  obtain ⟨_,z,hz,hzc,hd',hzcomm,_⟩ := reduced_reciprocal_critical_configuration h hob models
    hc hab hd hb hcomm hne
  obtain ⟨_,_,f,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  let e' := f.symm.trans e
  have hr' : primeRank 2 (d.localGroup beta ⧸ pCore 2 (d.localGroup beta)) ≤ 2*k+1 := by
    change primeRank 2 (graphLocalGroup F beta ⧸ pCore 2 (graphLocalGroup F beta)) ≤ _
    rw [primeRank_congr 2 e',suzuki_two_rank k hk]
  have hzw : z.type = w.val.type := by
    have hz' := hz.1
    have hw := w.property.1
    cases hzt : z.type <;> cases hwt : w.val.type <;> cases het : a'.type <;> simp_all
  exact ⟨hfirst,paired_square_of_field_bound ht (Reduction.reduced_borel_core_sylow h) d
    hzc hz hd' hb hzcomm (models a') (2*k+1) m hr' hrw hzw
    (reduced_ending_suzuki_field_square h hzc hz hd' hb hzcomm k e')⟩

/-- Source 8.3 at any specified moving neighbor for a nonbinary Suzuki
ending. Both paired estimates are discharged on the original configuration. -/
theorem reduced_suzuki_moving_omega_commutator
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily L S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      Z (Reduction.reducedFamily L S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily L S₀) w.val).subtype =
        (stabilizer (Reduction.reducedFamily L S₀) w.val ⊓ stabilizer (Reduction.reducedFamily L S₀) a').pCoreIn 2)
    (k : ℕ) (hk : 0 < k)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* SuzukiMatrixGroup k) :
    ⁅quotientSylowOmegaPreimage (graphLocalGroup (Reduction.reducedFamily L S₀) w.val) R,
      Z (Reduction.reducedFamily L S₀) w.val⁆ ≤
        ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
          V (Reduction.reducedFamily L S₀) a' 1⁆ := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have hne : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V F w.property)).trans hz.le))
  apply source_omega_commutator_of_paired_indices ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hm R hR
  intro m hm hu
  change ClassicalGroup.IsPSU (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) 3 (2^m) ∨
    IsSU (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) 3 (2^m) at hu
  apply reduced_suzuki_paired_square h hob models hc hab hd hb hcomm hne k hk e w m
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    let : Finite (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) :=
      Finite.of_injective e e.injective
    rw [primeRank_congr 2 e]
    exact (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    let : Finite (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) :=
      Finite.of_injective e e.injective
    rw [primeRank_congr 2 e,primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
      J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
    exact (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le

/-- Literal reduced-F1.11 application for every Suzuki ending, including
Sz(2), with the moving neighbor and its full-edge Sylow constructed. -/
theorem reduced_ending_suzuki_omega_commutator
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',V (Reduction.reducedFamily L S₀) a' 1⁆ ≠ ⊥)
    (k : ℕ)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* SuzukiMatrixGroup k) :
    let F := Reduction.reducedFamily L S₀
    ¬ V F a' 1 ≤ Q F beta ∧
      ∃ w : (graph F).neighborSet a',
        ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥ ∧
        ∃ R : Sylow 2 (graphLocalGroup F w.val),
          (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype =
            (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ∧
          ⁅quotientSylowOmegaPreimage (graphLocalGroup F w.val) R,Z F w.val⁆ ≤
            ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact reduced_ending_binary_models_omega_commutator h hob models hc hab hd hb hcomm hne
      (Or.inr (Or.inl ⟨e⟩))
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have he := reduced_reciprocal_escape h hob models hc hab hd hb hcomm hne
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d w.property.symm
  exact ⟨he,w,hm,R,hR,reduced_suzuki_moving_omega_commutator h hob models
    hc hab hd hb hcomm w hm R hR k hk e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

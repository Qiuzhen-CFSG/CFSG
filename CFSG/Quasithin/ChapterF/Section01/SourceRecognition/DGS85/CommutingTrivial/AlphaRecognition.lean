module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.TorusOmegaBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AlphaAssembly

/-!
# Both recognized local sections in the commuting trivial branch

The torus orbit bound removes the strictness premise in alpha selection.
An actual alpha marking identifies its Sylow omega order with its field
order, hence with the beta field order. The constructed quadratic action on
Z_alpha then satisfies corrected 5.12 with a strict square bound. This gives
natural coordinates on the entire original center, and the natural-neighbor
calculation gives [Q_beta,V_beta] = Z_beta.

The final theorem combines this with the two-branch initial recognition. It
constructs both local quotient markings, both natural sections, equal fields,
and the original indices and commutators. The earlier catalogues, Chapter 8
exchange and source 6.5 obstruction remain explicit; no alpha marking or
strictness comparison is supplied to the final theorem. The path arguments
of 9.5--9.11 and the terminal distance/field-two conclusions remain separate.
Source: DGS, Groups and Graphs (1985), 9.3--9.4, printed pp.142--143.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The constructed beta section recognizes the actual alpha quotient without
an external strict-square or normalized-opposite-subgroup premise. -/
theorem reduced_natural_residual_alpha_model
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (Mbin : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (M : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hres : NaturalResidualSection h beta e n)
 :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
      0 < m ∧ Nat.card K = 2^m ∧
        Nonempty ((H ⧸ pCore 2 H) ≃* SL(2,K)) := by
  apply reduced_critical_alpha_model_of_normalized_strict h hob hc hab hd hb hcomm
    Mbin M hn hF e hres
  intro R hR
  rw [reduced_natural_residual_omega_eq_field h hob hc hab hd hb hcomm Mbin M hn hF e hres R hR]
  have hpos : 1 < Nat.card F := hF ▸ Nat.one_lt_pow (by omega) (by decide)
  nlinarith

/-- With the recognized alpha marking, the fields agree and the literal
alpha center is natural; the source core commutator is its beta center. -/
theorem reduced_natural_residual_alpha_natural
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (Mbin : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (M : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hres : NaturalResidualSection h beta e n)

    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hm : 0 < m) (hK : Nat.card K = 2^m)
    (eα : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,K)) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    Nat.card K = Nat.card F ∧
      ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅Q Γ beta,V Γ beta 1⁆ = Z Γ beta ∧
      ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)))
        (T : Sylow 2 SL(2,K)),
        (∀ (l : H) (z : Additive (Z Γ a)),
          ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
            (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
        Function.Injective ρ ∧ IsSourceNatural ρ T m ∧
        ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → K),
          ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a
  let q₀ := QuotientGroup.mk' (pCore 2 H)
  let q := eα.toMonoidHom.comp q₀
  let W := conjugateSpanBy (Q Γ a) (stabilizer Γ beta)
  let Z₀ := Z Γ a ⊓ (Subgroup.center W).map W.subtype
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (Z Γ a) := Finite.of_injective (inclusion (Z_le_stabilizer Γ a)) (inclusion_injective _)
  let : Nontrivial (Z Γ a) := CommutingNontrivial.source_center_nontrivial ht a
  obtain ⟨R,hR,_,_,hZY,hquadY,hindex⟩ :=
    reduced_natural_residual_omega_quadratic h hob hc hab hd hb hcomm M hn hF e hres
  let A₀ := omegaCenterIn ((R : Subgroup H).map q₀)
  let A := A₀.map eα.toMonoidHom
  let Y := (A₀.comap q₀).map H.subtype
  have hcard₀ : Nat.card A₀ = Nat.card F :=
    reduced_natural_residual_omega_eq_field h hob hc hab hd hb hcomm Mbin M hn hF e hres R hR
  have heq : Nat.card K = Nat.card F :=
    (linear_marking_quotient_sylow_omega_card eα R).symm.trans hcard₀
  have hcard : Nat.card A = Nat.card F :=
    (card_map_of_injective eα.injective).trans hcard₀
  have hYH : Y ≤ H := map_subtype_le _
  have hYq : (Y.subgroupOf H).map q = A := by
    rw [show q = eα.toMonoidHom.comp q₀ from rfl,←map_map]
    change (((A₀.comap q₀).map H.subtype |>.comap H.subtype).map q₀).map _ = _
    rw [comap_map_eq_self_of_injective H.subtype_injective,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  let T : Sylow 2 SL(2,K) := R.mapSurjective (f := q) (eα.surjective.comp (QuotientGroup.mk'_surjective _))
  have hAT : A ≤ (T : Subgroup SL(2,K)) := by
    change A₀.map eα.toMonoidHom ≤ (R : Subgroup H).map q
    rw [show q = eα.toMonoidHom.comp q₀ from rfl,←map_map]
    exact map_mono (map_subtype_le _)
  obtain ⟨ρ,hact⟩ := CommutingNontrivial.source_exists_center_quotient_action ht d a eα
  change Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)) at ρ
  obtain ⟨T₀⟩ := Sylow.nonempty (p := 2) (G := stabilizer Γ a)
  have hgeom := Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm
  have hz := intrinsic_local_center_eq_bot_of_neighbor_central ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab hgeom.2.2.1
  obtain ⟨S,hS,hgen,hres₀⟩ := CommutingNontrivial.source_center_module_prepared_of_center_eq_bot
    ht d a hz T₀ eα ρ hact
  have hf : Function.Injective ρ :=
    CommutingNontrivial.linear_quotient_action_faithful (W := Additive (Z Γ a)) hm hK eα ρ hres₀
  have hgT : GeneratedByFixedSpace ρ (T : Subgroup SL(2,K)) := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,K) S T
    rw [←hg]
    exact generatedByFixedSpace_of_equivariant_surjection ρ ρ
      (MulAut.conj g).toMonoidHom (ρ g)
      (fun v => ⟨ρ g⁻¹ v,ρ.self_inv_apply g v⟩)
      (by intro a v; simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
        MulAut.conj_apply,map_mul,Module.End.mul_apply,ρ.inv_self_apply]) S hgen
  have hZL : Z Γ a ≤ H := CommutingNontrivial.pGroup_le_localGroup Γ d a _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer Γ a)
  have hnZ : H ≤ normalizer (Z Γ a : Set (Reduction.G₀ L S₀)) :=
    (sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a)
  have hqA : IsQuadratic ρ A := by
    rw [←hYq]
    apply BinaryConjugationSection.isQuadratic_of_triple_commutator_le H (Z Γ a) ⊥ Y
      ρ q (CommutingNontrivial.centerSection H (Z Γ a) hZL hnZ q ρ hact)
    rw [commutator_comm Y (Z Γ a),commutator_comm]
    exact hquadY.le
  have hi := CommutingNontrivial.center_action_fixed_index H (Z Γ a) Y hZL hnZ hYH q ρ hact
  rw [hYq] at hi
  change Z₀.relIndex (Z Γ a) = Nat.card F at hindex
  change Z₀ ≤ centralizer (Y : Set (Reduction.G₀ L S₀)) at hZY
  have hle : Nat.card (Additive (Z Γ a) ⧸ fixedSpace ρ A) ≤ Nat.card F := by
    rw [hi,←hindex]
    exact relIndex_le_of_le_left hZY (by rw [hindex]; exact Nat.card_pos.ne')
  have hs : Nat.card (Additive (Z Γ a) ⧸ fixedSpace ρ A) < Nat.card A ^ 2 := by
    rw [hcard]
    have hpos : 1 < Nat.card F := hF ▸ Nat.one_lt_pow (by omega) (by decide)
    nlinarith
  have hfix : fixedSpace ρ ⊤ = ⊥ := bot_unique ((fixedSpace_antitone ρ le_top).trans hres₀.le)
  obtain ⟨hnat,E,hE⟩ := sl2_strict_actor_natural ρ hf T A hAT hqA hgT hfix hK hs
  obtain ⟨hcQ,hcV⟩ := reduced_critical_natural_core_commutator h hc hab hd hb hcomm
    (hob beta a hab.symm) hm hK eα ρ hact hf ⟨T,hnat⟩
  rw [commutator_comm] at hcV
  exact ⟨heq,hcQ,hcV,ρ,T,hact,hf,hnat,E,hE⟩

/-- Source 9.3--9.4 in both initial branches, retaining the actual quotient
actions and whole residual section, under the genuine earlier-source inputs. -/
theorem reduced_critical_recognized_sections
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z,
        Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓
        Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃*
              SL(2,F)))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓
          Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))
    (Mαsource : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
 :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸
        pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) = Nat.card F ∧
        NaturalResidualSection h beta eβ n ∧
        ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
          0 < m ∧ Nat.card K = 2^m ∧
          ∃ eα : (H ⧸ pCore 2 H) ≃* SL(2,K),
            Nat.card K = Nat.card F ∧
            ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅Q Γ beta,V Γ beta 1⁆ = Z Γ beta ∧
            let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
            letI : Algebra (ZMod 2) K := ZMod.algebra K 2
            ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)))
              (T : Sylow 2 SL(2,K)),
              (∀ (l : H) (z : Additive (Z Γ a)),
                ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
                  (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
              Function.Injective ρ ∧ IsSourceNatural ρ T m ∧
              ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → K),
                ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z) := by
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hC,hC',hres⟩ :=
    reduced_critical_recognized_initial_section h hc hab hd hb hcomm htriv h8 hob Mα Mβ Mα'
  let := instF
  let := finF
  let := charF
  obtain ⟨K,instK,finK,charK,m,hm,hK,⟨eα⟩⟩ :=
    reduced_natural_residual_alpha_model h hob hc hab hd hb hcomm Mα Mαsource hn hF eβ hres
  let := instK
  let := finK
  let := charK
  exact ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hC,hC',hres,
    K,instK,finK,charK,m,hm,hK,eα,
    reduced_natural_residual_alpha_natural h hob hc hab hd hb hcomm
      Mα Mαsource hn hF eβ hres hm hK eα⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

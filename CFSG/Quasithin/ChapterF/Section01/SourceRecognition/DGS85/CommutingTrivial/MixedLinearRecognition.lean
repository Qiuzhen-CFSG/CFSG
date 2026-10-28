module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.MixedConstituent
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.IndexEstimates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ResidualDescent

/-!
# Linear recognition in the small-neighbor case

Assume the literal local quotients at alpha and beta have supplied SL₂
markings. The center action at alpha is constructed, proved faithful, and
shown to satisfy the corrected fixed-generation hypothesis. Its field
bounds and the opposite residual constituent force both mixed indices and
both field orders to coincide. The strict inequality is therefore proved,
so corrected 5.12 gives natural coordinates on the original Z_alpha.
The natural-center commutator theorem then gives both identities of 9.4(c).

The original index of V_beta is also the field order: its image in the
opposite linear quotient contains the image of Z_alpha and fits in a
Sylow subgroup of that order. No whole-residual-section descent is assumed.
MixedResidual uses the resulting natural center to construct that descent.

Source: DGS, *Groups and Graphs* (1985), 9.3--9.4, pp.142--143. Actual
linear quotient markings and the earlier 6.5 obstruction remain explicit;
initial recognition and 9.5--9.11 remain with the Chapter 9 assembly.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The mixed center action is faithful and satisfies the linear field bounds.
Every action, generation and quadraticity premise is constructed. The precise
6.5 obstruction is retained from the earlier-source producer. -/
theorem reduced_small_neighbor_center_linear_control (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (hs : V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    ∃ (ρ : Representation (ZMod 2) SL(2,F) (Additive (Z Γ a))) (T : Sylow 2 SL(2,F)),
      (∀ (l : H) (z : Additive (Z Γ a)),
        ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
          (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
      Function.Injective ρ ∧
      (Q Γ a).relIndex (V Γ a' 1) ≤ Nat.card F ∧
      Nat.card F ≤ (Q Γ a').relIndex (Z Γ a) ∧
      ((Q Γ a').relIndex (Z Γ a) < (Q Γ a).relIndex (V Γ a' 1)^2 →
        IsSourceNatural ρ T n ∧
        ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → F),
          ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let H := graphLocalGroup Γ a
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let Aq := ((V Γ a' 1).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (Z Γ a) := Finite.of_injective (inclusion (Z_le_stabilizer Γ a)) (inclusion_injective _)
  let : Nontrivial (Z Γ a) := CommutingNontrivial.source_center_nontrivial ht a
  obtain ⟨ρ,hact⟩ := CommutingNontrivial.source_exists_center_quotient_action ht d a e
  change Representation (ZMod 2) SL(2,F) (Additive (Z Γ a)) at ρ
  obtain ⟨T₀⟩ := Sylow.nonempty (p := 2) (G := stabilizer Γ a)
  have hgeom := Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm
  have hz := intrinsic_local_center_eq_bot_of_neighbor_central ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab hgeom.2.2.1
  obtain ⟨S,hS,hgen,hres⟩ := CommutingNontrivial.source_center_module_prepared_of_center_eq_bot
    ht d a hz T₀ e ρ hact
  have hf : Function.Injective ρ := by
    exact CommutingNontrivial.linear_quotient_action_faithful (W := Additive (Z Γ a)) hn hF e ρ hres
  have hp : IsPGroup 2 (V Γ a' 1) := (isPGroup_pCoreIn 2 _).to_le hs
  have hVH : V Γ a' 1 ≤ H := CommutingNontrivial.pGroup_le_localGroup Γ d a _ hp
    (hs.trans ((source_Z_Q_U ht beta).2.trans
      ((ballKernel_one_le_edge Γ hab.symm).trans inf_le_right)))
  have hZL : Z Γ a ≤ H := CommutingNontrivial.pGroup_le_localGroup Γ d a _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer Γ a)
  have hnZ : H ≤ normalizer (Z Γ a : Set (Reduction.G₀ L S₀)) :=
    (sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a)
  have hk : q.ker = (Q Γ a).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    have hcore : H.pCoreIn 2 = Q Γ a := graphLocalGroup_core ht a
    rw [←hcore]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hcard : Nat.card Aq = (Q Γ a).relIndex (V Γ a' 1) :=
    BinaryConjugationSection.actor_image_card_eq_relIndex H (Q Γ a) (V Γ a' 1) q hk hVH
  have hne : Aq ≠ ⊥ := by
    intro hbot
    rw [hbot,card_bot] at hcard
    exact mixed_neighbor_escape ht (Reduction.reduced_kernel_sylow h) hc hab hd.le htriv
      (relIndex_eq_one.mp hcard.symm)
  have hAq : IsPGroup 2 Aq := (hp.comap_subtype (K := H)).map q
  obtain ⟨T,hAT⟩ := hAq.exists_le_sylow
  have hgT : GeneratedByFixedSpace (V := Additive (Z Γ a)) ρ (T : Subgroup SL(2,F)) := by
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) S T
    exact generatedByFixedSpace_of_equivariant_surjection ρ ρ
      (MulAut.conj g).toMonoidHom (ρ g)
      (fun v => ⟨ρ g⁻¹ v, ρ.self_inv_apply g v⟩)
      (by intro a v; simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
        MulAut.conj_apply,map_mul,Module.End.mul_apply,ρ.inv_self_apply]) S hgen
  have hindex := CommutingNontrivial.center_action_fixed_index H (Z Γ a) (V Γ a' 1)
    hZL hnZ hVH q ρ hact
  have hc₀ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (Z Γ a))
    (mixed_center_centralizer ht (Reduction.reduced_kernel_sylow h) hab hd.le htriv)
  change (Z Γ a ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (Z Γ a) =
    (Z Γ a ⊓ Q Γ a').relIndex (Z Γ a) at hc₀
  simp only [inf_relIndex_left] at hc₀
  have hi : Nat.card (Additive (Z Γ a) ⧸ fixedSpace ρ Aq) = (Q Γ a').relIndex (Z Γ a) :=
    hindex.trans hc₀
  have hq : IsQuadratic ρ Aq := by
    apply BinaryConjugationSection.isQuadratic_of_triple_commutator_le H (Z Γ a) ⊥ (V Γ a' 1)
      ρ q (CommutingNontrivial.centerSection H (Z Γ a) hZL hnZ q ρ hact)
    have hquad := (reduced_critical_mixed_actions h hc hab hd hb hcomm htriv hs).2.2.2.2.2.2.2.1
    rw [commutator_comm (V Γ a' 1) (Z Γ a),commutator_comm]
    exact hquad.le
  have hlo := sl2_actor_field_bound ρ hf T Aq hAT hne hF
  rw [hi] at hlo
  refine ⟨ρ,T,hact,hf,?_,hlo,?_⟩
  · rw [←hcard]
    exact (Nat.card_le_card_of_injective _ (inclusion_injective hAT)).trans_eq
      (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv)
  · intro hstrict
    have hfix : fixedSpace ρ ⊤ = ⊥ := bot_unique ((fixedSpace_antitone ρ le_top).trans hres.le)
    exact sl2_strict_actor_natural ρ hf T Aq hAT hq hgT hfix hF (by rwa [hi,hcard])

/-- In the small-neighbor case, actual linear local quotients force equal
fields, the original 9.3 indices, and natural coordinates on Z_alpha.
Consequently the exact 9.4(c) core commutators also hold. -/
theorem reduced_small_neighbor_linear_recognition (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (hs : V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {F K : Type*} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2]
    {n m : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hm : 0 < m) (hK : Nat.card K = 2^m)
    (eα : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,F))
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,K)) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    Nat.card F = Nat.card K ∧
      (Q Γ a).relIndex (V Γ a' 1) = Nat.card F ∧
      (Q Γ a').relIndex (Z Γ a) = Nat.card F ∧
      (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
      ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅V Γ beta 1,Q Γ beta⁆ = Z Γ beta ∧
      ∃ (ρ : Representation (ZMod 2) SL(2,F) (Additive (Z Γ a))) (T : Sylow 2 SL(2,F)),
        (∀ (l : H) (z : Additive (Z Γ a)),
          ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
            (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
        Function.Injective ρ ∧ IsSourceNatural ρ T n ∧
        ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → F),
          ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨g,e₀,f,hg,he₀,hf,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  obtain ⟨ρ,T,hact,hfaith,hyF,hFx,hnat⟩ :=
    reduced_small_neighbor_center_linear_control h hc hab hd hb hcomm htriv hs hob hn hF eα
  obtain ⟨hxK,hKc⟩ := reduced_critical_opposite_linear_field_bounds h hc hab hd hb hcomm hm hK (f.trans eβ)
  have hec := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ a' 1))
    (reduced_critical_mixed_centralizers h hc hab hd hb hcomm htriv hs).2.1
  change (V Γ a' 1 ⊓ centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) =
    (V Γ a' 1 ⊓ Q Γ a).relIndex (V Γ a' 1) at hec
  simp only [inf_relIndex_left] at hec
  have hKy : Nat.card K ≤ (Q Γ a).relIndex (V Γ a' 1) := hKc.trans_eq hec
  change (Q Γ a).relIndex (V Γ a' 1) ≤ Nat.card F at hyF
  change Nat.card F ≤ (Q Γ a').relIndex (Z Γ a) at hFx
  change (Q Γ a').relIndex (Z Γ a) ≤ Nat.card K at hxK
  have heq : Nat.card F = Nat.card K := by omega
  have hy : (Q Γ a).relIndex (V Γ a' 1) = Nat.card F := by omega
  have hx : (Q Γ a').relIndex (Z Γ a) = Nat.card F := by omega
  have hstrict : (Q Γ a').relIndex (Z Γ a) < (Q Γ a).relIndex (V Γ a' 1)^2 := by
    rw [hx,hy]
    have hpos : 1 < Nat.card F := hF ▸ one_lt_pow₀ (by decide) (by omega)
    nlinarith
  obtain ⟨hnatural,E,hE⟩ := hnat hstrict
  obtain ⟨hcQ,hcV⟩ := reduced_critical_natural_core_commutator h hc hab hd hb hcomm
    (hob beta a hab.symm) hn hF eα ρ hact hfaith ⟨T,hnatural⟩
  have hVB : (Q Γ a').relIndex (V Γ beta 1) = Nat.card F := by
    let H' := graphLocalGroup Γ a'
    let : Finite H' := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
    let q' := (f.trans eβ).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H'))
    have hVH : V Γ beta 1 ≤ H' := neighbor_le_graphLocalGroup ht
      (Reduction.reduced_kernel_sylow h) beta a' hb hd.le
    let : Finite (V Γ beta 1) := Finite.of_injective (inclusion hVH) (inclusion_injective _)
    have hp : IsPGroup 2 (V Γ beta 1) := (isPGroup_pCoreIn 2 _).to_le
      (V_le_Q Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
        (Reduction.reduced_kernel_sylow h) beta hb)
    obtain ⟨R,hR⟩ := ((hp.comap_subtype (K := H')).map q').exists_le_sylow
    have hk : q'.ker = (Q Γ a').subgroupOf H' := by
      rw [MonoidHom.ker_comp_of_injective _ _ (f.trans eβ).injective,QuotientGroup.ker_mk']
      have hcore : H'.pCoreIn 2 = Q Γ a' := graphLocalGroup_core ht a'
      rw [←hcore]
      exact (comap_map_eq_self_of_injective H'.subtype_injective _).symm
    have hcard := BinaryConjugationSection.actor_image_card_eq_relIndex H' (Q Γ a') (V Γ beta 1) q' hk hVH
    have hu : (Q Γ a').relIndex (V Γ beta 1) ≤ Nat.card K := by
      rw [←hcard]
      exact (Nat.card_le_card_of_injective _ (inclusion_injective hR)).trans_eq
        (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 R).symm.toEquiv)
    have hl : (Q Γ a').relIndex (Z Γ a) ≤ (Q Γ a').relIndex (V Γ beta 1) :=
      relIndex_le_of_le_right (CommutingNontrivial.Z_neighbor_le_V Γ hab.symm) (by
        exact index_ne_zero_of_finite)
    omega
  exact ⟨heq,hy,hx,hVB,hcQ,hcV,ρ,T,hact,hfaith,hnatural,E,hE⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

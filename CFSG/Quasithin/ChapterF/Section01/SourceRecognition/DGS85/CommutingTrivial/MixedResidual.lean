module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.MixedActor

/-!
# Naturality of the whole residual section in the mixed linear branch

The proved natural-center assertion supplies quadraticity at alpha.
The core-displacement theorem then constructs the action of the actual
beta quotient on V_beta/C_V_beta(O²(L_beta)), with its original conjugation,
faithfulness and Sylow-fixed generation. Transport Z_alpha by the original
graph element taking alpha-prime to beta. Its two literal indices are the
common field order, so corrected 5.12 applies to this whole residual section.
The output retains the exact quotient homomorphism and natural coordinates.

The abstract final representation calculation keeps the vector-space
instance opaque to avoid repeatedly elaborating the nested source quotients.
All declarations compile with Lean's default heartbeat limit.

Source: DGS, *Groups and Graphs* (1985), 9.3(c) and 9.4, pp.142--143;
corrected 5.12, pp.113--114. This is the small-neighbor case with supplied
actual linear quotients and the earlier 6.5 obstruction. Their initial
recognition, the other neighbor case, and 9.5--9.11 remain assembly work.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem linear_natural_of_field_indices {K W : Type*}
    [Field K] [Finite K] [CharP K 2] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) SL(2,K) W) (hf : Function.Injective σ)
    (S : Sylow 2 SL(2,K)) (hgen : GeneratedByFixedSpace σ S)
    (hr : fixedSpace σ (pResidual 2 SL(2,K)) = ⊥)
    (A : Subgroup SL(2,K)) (hp : IsPGroup 2 A) (hq : IsQuadratic σ A)
    (hc : Nat.card A = Nat.card K) (hi : Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card K)
    {m : ℕ} (hm : 0 < m) (hK : Nat.card K = 2^m) :
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    ∃ T : Sylow 2 SL(2,K), IsSourceNatural σ T m ∧
      ∃ E : W ≃ₗ[ZMod 2] (Fin 2 → K), ∀ g z, E (σ g z) = Matrix.mulVec g.val (E z) := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨T,hT⟩ := hp.exists_le_sylow
  have hgT : GeneratedByFixedSpace σ (T : Subgroup SL(2,K)) := by
    obtain ⟨k,rfl⟩ := MulAction.exists_smul_eq SL(2,K) S T
    exact generatedByFixedSpace_of_equivariant_surjection σ σ
      (MulAut.conj k).toMonoidHom (σ k)
      (fun v => ⟨σ k⁻¹ v,σ.self_inv_apply k v⟩)
      (by intro a v; simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
        MulAut.conj_apply,map_mul,Module.End.mul_apply,σ.inv_self_apply]) S hgen
  have hx : fixedSpace σ ⊤ = ⊥ := bot_unique ((fixedSpace_antitone σ le_top).trans hr.le)
  have hstrict : Nat.card (W ⧸ fixedSpace σ A) < Nat.card A^2 := by
    rw [hc]
    have hpos : 1 < Nat.card K := hK ▸ one_lt_pow₀ (by decide) (by omega)
    nlinarith only [hi,hpos]
  exact ⟨T,sl2_strict_actor_natural σ hf T A hT hq hgT hx hK hstrict⟩

/-- Naturality of the whole original residual section in the small-neighbor
linear branch. The actor is the actual conjugate of Z_alpha carrying
alpha-prime to beta; descent and fixed-space generation are proved. -/
theorem reduced_small_neighbor_natural_residual (h : HypothesisF11 L S₀)
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
    let H := graphLocalGroup Γ beta
    let A := (V Γ beta 1).subgroupOf H
    let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    letI : ∀ i, Finite (Γ i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
    ∃ hb2 : 2 < b Γ,
      letI := neighborhoodIn_elementary Γ (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) beta hb2 H
      letI : Algebra (ZMod 2) K := ZMod.algebra K 2
      ∃ (σ : Representation (ZMod 2) SL(2,K) (FixedQuotient A (pResidual 2 H)))
        (T : Sylow 2 SL(2,K)),
        (∀ l : H, σ (q l) = fixedQuotientAction A (pResidual 2 H) l) ∧
        Function.Injective σ ∧ IsSourceNatural σ T m ∧
        ∃ E : FixedQuotient A (pResidual 2 H) ≃ₗ[ZMod 2] (Fin 2 → K),
          ∀ g z, E (σ g z) = Matrix.mulVec g.val (E z) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  obtain ⟨hFK,hy,hx,hVB,hcQ,hcV,ρ,R,hρ,hρf,hρnat,_⟩ :=
    reduced_small_neighbor_linear_recognition h hc hab hd hb hcomm htriv hs hob hn hF hm hK eα eβ
  obtain ⟨hb2,σ,S,hσ,hS,hgen,hres,hfaith,hquadr,_⟩ := reduced_critical_linear_residual_action
    h hc hab hd hb hcomm (hob a beta hab) (hob beta a hab.symm) hm hK eα eβ
    ρ hρ ⟨R,hρnat.2.2⟩
  refine ⟨hb2,?_⟩
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  change Representation (ZMod 2) SL(2,K) (FixedQuotient A (pResidual 2 H)) at σ
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨_,hnz,⟨c⟩,hr,hVH,hquad⟩ := reduced_critical_residual_section h hc hab hd hb hcomm
  have hself : (graph Γ).dist beta beta + 1 ≤ b Γ := by
    rw [SimpleGraph.dist_self,zero_add]
    exact hb.le
  have hVL : V Γ beta 1 ≤ H := neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) beta beta hb hself
  let : Finite (V Γ beta 1) := Finite.of_injective (inclusion hVL) (inclusion_injective _)
  let : Finite (FixedQuotient A (pResidual 2 H)) :=
    Finite.of_surjective (fun x : V Γ beta 1 => (c.coordinates x).toAdd)
      (Multiplicative.toAdd.surjective.comp c.onto)
  have hcomp : σ.comp q = fixedQuotientAction A (pResidual 2 H) := MonoidHom.ext hσ
  obtain ⟨g,hg,hEL,hp,hEidx,hCidx,hquadE⟩ :=
    reduced_small_neighbor_transported_actor h hc hab hd hb hcomm htriv hs hob hn hF hm hK eα eβ
  let E := (Z Γ a).map (MulAut.conj g).toMonoidHom
  let Eq := (E.subgroupOf H).map q
  have hpEq : IsPGroup 2 Eq := (hp.comap_subtype (K := H)).map q
  have hk : q.ker = (Q Γ beta).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ eβ.injective,QuotientGroup.ker_mk']
    have hcore : H.pCoreIn 2 = Q Γ beta := graphLocalGroup_core ht beta
    rw [←hcore]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hcard : Nat.card Eq = Nat.card K :=
    (BinaryConjugationSection.actor_image_card_eq_relIndex H (Q Γ beta) E q hk hEL).trans hEidx
  have hindex := BinaryConjugationSection.fixed_quotient_card_le_centralizer_index σ q
    (hcomp.symm ▸ c) E
  rw [hCidx] at hindex
  have hq : IsQuadratic σ Eq := by
    apply BinaryConjugationSection.isQuadratic_of_triple_commutator_le H (V Γ beta 1) _ E
      σ q (hcomp.symm ▸ c)
    exact hquadE.le.trans bot_le
  obtain ⟨T,hnatural,F₀,hF₀⟩ := linear_natural_of_field_indices σ hfaith S hgen hres
    Eq hpEq hq hcard hindex hm hK
  exact ⟨σ,T,hσ,hfaith,hnatural,F₀,hF₀⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

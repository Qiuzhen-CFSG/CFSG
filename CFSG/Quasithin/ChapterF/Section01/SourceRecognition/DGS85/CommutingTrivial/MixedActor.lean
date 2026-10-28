module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.MixedLinearRecognition
public import Theory.GroupTheory.CentralizerInjectiveImage
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.IndexEstimates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ResidualDescent

/-!
# The transported critical-center actor and the full neighborhood centralizer

Conjugate Z_alpha by the actual graph element carrying alpha-prime to
beta. The original mixed indices become the core and centralizer indices
of this actor on V_beta, and its quadratic commutator identity is retained.
This separates the group calculation from the dependent residual action.

Equality of the two quotient-image orders also proves
V_beta = Z_alpha join (V_beta intersect Q_alpha_prime). The assumed trivial
neighbor commutator then identifies C_V_alpha_prime(V_beta), giving the
second literal index of 9.3(b), with the whole V_beta in the centralizer.
MixedResidual applies the transported actor to the original residual section.

Source: DGS, *Groups and Graphs* (1985), 9.3, printed p.142. Supplied linear
quotient markings and the earlier 6.5 input retain their original owners.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Transport the mixed actor by the actual graph element carrying
alpha-prime to beta. Both original indices and quadraticity are retained. -/
theorem reduced_small_neighbor_transported_actor (h : HypothesisF11 L S₀)
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
    ∃ g : Reduction.G₀ L S₀, g • a' = beta ∧
      let E := (Z Γ a).map (MulAut.conj g).toMonoidHom
      E ≤ graphLocalGroup Γ beta ∧ IsPGroup 2 E ∧
      (Q Γ beta).relIndex E = Nat.card K ∧
      (centralizer (E : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) = Nat.card K ∧
      ⁅E,⁅E,V Γ beta 1⁆⁆ = ⊥ := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  obtain ⟨hFK,hy,hx,_,_,_,_⟩ :=
    reduced_small_neighbor_linear_recognition h hc hab hd hb hcomm htriv hs hob hn hF hm hK eα eβ
  obtain ⟨g,e₀,f,hg,he₀,hf,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  let φ := (MulAut.conj g).toMonoidHom
  let E := (Z Γ a).map φ
  have hV : (V Γ a' 1).map φ = V Γ beta 1 := by rw [←V_translate,hg]
  have hQ : (Q Γ a').map φ = Q Γ beta := by rw [←Q_translate,hg]
  have hlocal : (graphLocalGroup Γ a').map φ = H := by
    have hh := graphLocalGroup_conjugate ht g a'
    change graphLocalGroup Γ (g • a') = (graphLocalGroup Γ a').map φ at hh
    rw [hg] at hh
    exact hh.symm
  have hZV : Z Γ a ≤ V Γ beta 1 := CommutingNontrivial.Z_neighbor_le_V Γ hab.symm
  have hEL : E ≤ H := hlocal ▸ map_mono (hZV.trans (neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) beta a' hb hd.le))
  have hEidx : (Q Γ beta).relIndex E = Nat.card K := by
    rw [←hQ]
    exact (relIndex_map_map_of_injective _ _ (MulAut.conj g).injective).trans (hx.trans hFK)
  have hec := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ a' 1))
    (reduced_critical_mixed_centralizers h hc hab hd hb hcomm htriv hs).2.1
  change (V Γ a' 1 ⊓ centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) =
    (V Γ a' 1 ⊓ Q Γ a).relIndex (V Γ a' 1) at hec
  simp only [inf_relIndex_left] at hec
  have hCidx : (centralizer (E : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) = Nat.card K := by
    rw [←inf_relIndex_left (V Γ beta 1),←hV]
    change ((V Γ a' 1).map φ ⊓ centralizer ((Z Γ a).map φ : Set (Reduction.G₀ L S₀))).relIndex
      ((V Γ a' 1).map φ) = _
    rw [map_inf_centralizer_of_injective φ (MulAut.conj g).injective,
      relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,inf_relIndex_left]
    exact hec.trans (hy.trans hFK)
  have hquad0 : ⁅Z Γ a,⁅Z Γ a,V Γ a' 1⁆⁆ = ⊥ := by
    rw [commutator_comm (Z Γ a) ⁅Z Γ a,V Γ a' 1⁆]
    exact (reduced_critical_mixed_actions h hc hab hd hb hcomm htriv hs).2.2.2.2.2.2.1
  have he := congrArg (map φ) hquad0
  rw [map_commutator,map_commutator,Subgroup.map_bot,hV] at he
  exact ⟨g,hg,hEL,(IsElementaryAbelian.isPGroup 2 (Z Γ a)).map φ,hEidx,hCidx,he⟩

/-- The literal span decomposition and the second centralizer index in 9.3(b).
The full V_beta, rather than only Z_alpha, occurs in the centralizer. -/
theorem reduced_small_neighbor_span_and_centralizer (h : HypothesisF11 L S₀)
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
    V Γ beta 1 = Z Γ a ⊔ (V Γ beta 1 ⊓ Q Γ a') ∧
      V Γ a' 1 ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) = V Γ a' 1 ⊓ Q Γ a ∧
      (centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) = Nat.card K := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a'
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨hFK,hy,hx,hVB,_,_,_⟩ :=
    reduced_small_neighbor_linear_recognition h hc hab hd hb hcomm htriv hs hob hn hF hm hK eα eβ
  obtain ⟨g,e₀,f,hg,he₀,hf,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  let q := (f.trans eβ).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hVH : V Γ beta 1 ≤ H := neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) beta a' hb hd.le
  have hZV : Z Γ a ≤ V Γ beta 1 := CommutingNontrivial.Z_neighbor_le_V Γ hab.symm
  have hk : q.ker = (Q Γ a').subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ (f.trans eβ).injective,QuotientGroup.ker_mk']
    have hcore : H.pCoreIn 2 = Q Γ a' := graphLocalGroup_core ht a'
    rw [←hcore]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hcardZ := BinaryConjugationSection.actor_image_card_eq_relIndex H (Q Γ a') (Z Γ a)
    q hk (hZV.trans hVH)
  have hcardV := BinaryConjugationSection.actor_image_card_eq_relIndex H (Q Γ a') (V Γ beta 1)
    q hk hVH
  have he : ((Z Γ a).subgroupOf H).map q = ((V Γ beta 1).subgroupOf H).map q := by
    apply eq_of_le_of_card_ge (map_mono (comap_mono hZV))
    exact le_of_eq ((hcardV.trans hVB).trans (hcardZ.trans hx).symm)
  have hspan : V Γ beta 1 = Z Γ a ⊔ (V Γ beta 1 ⊓ Q Γ a') := by
    apply le_antisymm ?_ (sup_le hZV inf_le_left)
    intro x hx'
    have hm : q ⟨x,hVH hx'⟩ ∈ ((V Γ beta 1).subgroupOf H).map q :=
      mem_map_of_mem q hx'
    rw [←he] at hm
    obtain ⟨z,hz,hzx⟩ := hm
    have hkz : z⁻¹ * (⟨x,hVH hx'⟩ : H) ∈ q.ker := by
      simp only [MonoidHom.mem_ker,map_mul,map_inv,hzx,inv_mul_cancel]
    have hdiff : (z : Reduction.G₀ L S₀)⁻¹*x ∈ Q Γ a' := by
      have hh : z⁻¹ * (⟨x,hVH hx'⟩ : H) ∈ (Q Γ a').subgroupOf H := hk ▸ hkz
      exact hh
    have hdiffV : (z : Reduction.G₀ L S₀)⁻¹*x ∈ V Γ beta 1 := mul_mem (inv_mem (hZV hz)) hx'
    have hmem : (z : Reduction.G₀ L S₀) * ((z : Reduction.G₀ L S₀)⁻¹*x) ∈
        Z Γ a ⊔ (V Γ beta 1 ⊓ Q Γ a') :=
      mul_mem_sup hz ⟨hdiffV,hdiff⟩
    simpa only [mul_inv_cancel_left] using hmem
  have hC : V Γ a' 1 ⊓ centralizer (Z Γ a : Set (Reduction.G₀ L S₀)) ≤
      centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) := by
    rw [le_centralizer_iff,hspan]
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      ((commutator_eq_bot_iff_le_centralizer.mp htriv).trans (centralizer_le inf_le_left))
  have hcent : V Γ a' 1 ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) =
      V Γ a' 1 ⊓ Q Γ a := by
    calc
      _ = V Γ a' 1 ⊓ centralizer (Z Γ a : Set (Reduction.G₀ L S₀)) :=
        le_antisymm (inf_le_inf_left _ (centralizer_le hZV)) (le_inf inf_le_left hC)
      _ = _ := (reduced_critical_mixed_centralizers h hc hab hd hb hcomm htriv hs).2.1
  refine ⟨hspan,hcent,?_⟩
  have hi := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ a' 1)) hcent
  simp only [inf_relIndex_left] at hi
  exact hi.trans (hy.trans hFK)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

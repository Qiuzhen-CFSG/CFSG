module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.InitialGeometry

/-!
# Literal reorientation and local parameter transport in DGS 9.1--9.2

At critical distance the center is a two-subgroup of the intrinsic local
actor at the opposite vertex. Consequently a reverse critical pair
selected by span escape has commuting centers, because the beta center
is central in that actor. Its actual vertices and spans therefore satisfy
the Chapter 8 branch assumptions when reverse displacement is nontrivial.
The Chapter 8 distance and exchange conclusion is still required to
exclude that branch.

Odd critical distance puts alpha-prime and beta in the same orbit. The
resulting element of the original reduced completion transports their
local groups, spans and cores. It induces the actual quotient isomorphism
on every representative, and Sylow conjugacy identifies the source
q-parameters for arbitrary quotient Sylows. This proves the remaining
parameter statement of 9.1(a), without recognizing either local quotient.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
9.1(a) and 9.2, printed pp.141--142; q is defined on p.118.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A center at distance at most b lies in the intrinsic local actor,
not merely in the full stabilizer. -/
theorem center_le_localGroup_of_dist_le_b (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hd : (graph (family P)).dist v w ≤ b (family P)) :
    Z (family P) v ≤ graphLocalGroup (family P) w := by
  let := finite_endpoints h
  let := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) v
  have hp : IsPGroup 2 (Z (family P) v) := IsElementaryAbelian.isPGroup 2 _
  have hZS := Z_le_stabilizer_of_dist_le_b (family P) h.generate v w hd
  obtain ⟨T, hT⟩ := (hp.comap_subtype (K := stabilizer (family P) w)).exists_le_sylow
  intro z hz
  exact sylow_le_sylowGenerated _ T (mem_map_of_mem _
    (hT (show (⟨z, hZS hz⟩ : stabilizer (family P) w) ∈
      (Z (family P) v).subgroupOf (stabilizer (family P) w) from hz)))

/-- A selected reverse critical pair really has commuting centers: the beta
center is central in its actual local actor. -/
theorem reverse_critical_centers_commute (h : LocallyRankOneTriple P B)
    {z beta : Vertex (family P)} (hc : IsCriticalPair (family P) z beta)
    (hz : Z (family P) beta = omegaCenterIn (graphLocalGroup (family P) beta)) :
    ⁅Z (family P) z, Z (family P) beta⁆ = ⊥ := by
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
  intro x hx
  exact centralizer_le (center_le_localGroup_of_dist_le_b h hc.1.le)
    ((mem_omegaCenterIn_iff _ _).mp (hz ▸ hx)).2.1

private theorem omega_sylow_card_eq_of_equiv {D E : Type*} [Group D] [Group E] [Finite E]
    (e : D ≃* E) (T : Sylow 2 D) (R : Sylow 2 E) :
    Nat.card (omegaCenterIn (T : Subgroup D)) = Nat.card (omegaCenterIn (R : Subgroup E)) := by
  let : Finite D := Finite.of_equiv E e.toEquiv.symm
  let U := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hm : (omegaCenterIn (T : Subgroup D)).map e.toMonoidHom =
      omegaCenterIn (U : Subgroup E) :=
    NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective _
  have hc : Nat.card (omegaCenterIn (T : Subgroup D)) =
      Nat.card (omegaCenterIn (U : Subgroup E)) := by
    rw [← hm]
    exact Nat.card_congr ((omegaCenterIn (T : Subgroup D)).equivMapOfInjective
      e.toMonoidHom e.injective).toEquiv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq E U R
  have hr : (R : Subgroup E) = (U : Subgroup E).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  rw [hr, ← NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g).injective]
  exact hc.trans (Nat.card_congr ((omegaCenterIn (U : Subgroup E)).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv)

/-- Any actual local conjugation identifies the literal core quotients and
the source q-parameters for every choice of quotient Sylows. -/
theorem local_quotient_parameter_transport (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (g : G) (hg : g • v = w) :
    ∃ (e : graphLocalGroup (family P) v ≃* graphLocalGroup (family P) w)
      (f : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃*
        (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w))),
      (∀ x, (e x : G) = g * (x : G) * g⁻¹) ∧
      (∀ x, f (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (e x)) ∧
      ∀ (T : Sylow 2 (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)))
        (R : Sylow 2 (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w))),
        Nat.card (omegaCenterIn (T : Subgroup (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)))) =
          Nat.card (omegaCenterIn (R : Subgroup (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)))) := by
  let := finite_endpoints h
  let H := graphLocalGroup (family P) w
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have he : (graphLocalGroup (family P) v).map (MulAut.conj g).toMonoidHom =
      graphLocalGroup (family P) w := by rw [← hg, graphLocalGroup_conjugate h]
  let e := ((graphLocalGroup (family P) v).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr he)
  let f := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  refine ⟨e, f, fun _ => rfl, fun _ => rfl, ?_⟩
  intro T R
  exact omega_sylow_card_eq_of_equiv f T R


variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The two neighborhood vertices are conjugate by an element of the literal
reduced completion, with both local groups and both spans transported. -/
theorem reduced_critical_neighbor_transporter (h : HypothesisF11 L S)
    {a beta a' : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 = b (Reduction.reducedFamily L S))
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) a, Z (Reduction.reducedFamily L S) a'⁆ = ⊥) :
    ∃ g : Reduction.G₀ L S, g • a' = beta ∧
      graphLocalGroup (Reduction.reducedFamily L S) beta =
        (graphLocalGroup (Reduction.reducedFamily L S) a').map (MulAut.conj g).toMonoidHom ∧
      V (Reduction.reducedFamily L S) beta 1 =
        (V (Reduction.reducedFamily L S) a' 1).map (MulAut.conj g).toMonoidHom ∧
      Q (Reduction.reducedFamily L S) beta =
        (Q (Reduction.reducedFamily L S) a').map (MulAut.conj g).toMonoidHom := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hodd : Odd (b F) := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).1
  have hdF : (graph F).dist beta a' + 1 = b F := hd
  have heven : Even ((graph F).dist a' beta) := by
    rw [SimpleGraph.dist_comm]
    rcases hodd with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  have htypes : a'.type = beta.type := (even_dist_iff F ht.generate a' beta).mp heven
  obtain ⟨g, hg⟩ := (same_orbit_iff F a' beta).mpr htypes
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · rw [← hg]
    exact graphLocalGroup_conjugate ht g a'
  · rw [← hg, V_translate]
  · rw [← hg, Q_translate]

/-- Source 9.1(a) includes equality of the actual quotient Sylow-center
parameters at alpha-prime and beta. The quotient equivalence is induced by
the same element of the reduced completion, on every representative. -/
theorem reduced_critical_parameter_transport (h : HypothesisF11 L S)
    {a beta a' : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 = b (Reduction.reducedFamily L S))
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) a, Z (Reduction.reducedFamily L S) a'⁆ = ⊥) :
    let F := Reduction.reducedFamily L S
    ∃ (g : Reduction.G₀ L S) (e : graphLocalGroup F a' ≃* graphLocalGroup F beta)
      (f : (graphLocalGroup F a' ⧸ pCore 2 (graphLocalGroup F a')) ≃*
        (graphLocalGroup F beta ⧸ pCore 2 (graphLocalGroup F beta))),
      g • a' = beta ∧ (∀ x, (e x : Reduction.G₀ L S) = g * (x : Reduction.G₀ L S) * g⁻¹) ∧
      (∀ x, f (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (e x)) ∧
      ∀ (T : Sylow 2 (graphLocalGroup F a' ⧸ pCore 2 (graphLocalGroup F a')))
        (R : Sylow 2 (graphLocalGroup F beta ⧸ pCore 2 (graphLocalGroup F beta))),
        Nat.card (omegaCenterIn (T : Subgroup (graphLocalGroup F a' ⧸ pCore 2 (graphLocalGroup F a')))) =
          Nat.card (omegaCenterIn (R : Subgroup (graphLocalGroup F beta ⧸ pCore 2 (graphLocalGroup F beta)))) := by
  obtain ⟨g, hg, _⟩ := reduced_critical_neighbor_transporter h hc hab hd hb hcomm
  obtain ⟨e, f, he, hf, hq⟩ := local_quotient_parameter_transport (Reduction.reduced_triple h) g hg
  exact ⟨g, e, f, hg, he, hf, hq⟩

/-- The selected reverse pair has all three Chapter 8 branch assumptions,
using the same spans and the same completion as the original Chapter 9 data.
The Chapter 8 distance/exchange theorem is still needed to contradict it. -/
theorem reduced_reverse_branch_configuration (h : HypothesisF11 L S)
    {a beta a' : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 = b (Reduction.reducedFamily L S))
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) a, Z (Reduction.reducedFamily L S) a'⁆ = ⊥)
    (he : ¬ V (Reduction.reducedFamily L S) a' 1 ≤ Q (Reduction.reducedFamily L S) beta)
    (hrev : ⁅V (Reduction.reducedFamily L S) a' 1 ⊓ Q (Reduction.reducedFamily L S) beta,
      V (Reduction.reducedFamily L S) beta 1⁆ ≠ ⊥) :
    let F := Reduction.reducedFamily L S
    ∃ z : Vertex F, (graph F).Adj z a' ∧ IsCriticalPair F z beta ∧
      (graph F).dist a' beta + 1 = b F ∧
      ⁅Z F z, Z F beta⁆ = ⊥ ∧ 1 < b F ∧
      ⁅V F a' 1 ⊓ Q F beta, V F beta 1⁆ ≠ ⊥ := by
  obtain ⟨z, hz, hc', _⟩ := reduced_reverse_criticalPair h
    (Reduction.reduced_kernel_sylow h) hd he
  refine ⟨z, hz.symm, hc', ?_, ?_, hb, hrev⟩
  · rwa [SimpleGraph.dist_comm]
  · exact reverse_critical_centers_commute (Reduction.reduced_triple h) hc'
      (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

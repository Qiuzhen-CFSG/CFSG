module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CommutatorCentralizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CanonicalCoreProduct

/-!
# The geometric bound on the normal commutator in DGS 9.8

Put R = [V_beta,V_alpha-prime] and w = alpha-prime-2. The actual
linear markings and the source 6.5 obstruction imply that Q_w is the
product of its intersections with the cores at two distinct neighbors.
The proof uses full normality of the generated intersections and the
irreducible Sylow-normalizer action in the opposite linear quotient;
it includes the field of order two.

The full-index actor V_beta saturates Q_w intersect Q_(alpha-prime-1).
Since R centralizes V_beta, the original 9.4 commutator identity bounds
the resulting displacement by Z_alpha-prime. The proved centralizer
supplement transports that bound to the other intersection. Thus
[R,Q_w] lies in Z_(alpha-prime-1) Z_(alpha-prime-3), and hence in V_w.
Its normality in the actual local group is retained.

The F1.11 application constructs the last three vertices on the same
geodesic from beta, both original markings and natural sections, and
the shifted natural section. Catalogue, Chapter 8 and source 6.5 remain
genuine earlier inputs. The final natural-section dichotomy and whole-span
identity of 9.8, and the later distance and field conclusions, remain open.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
9.8, printed p.146; 6.5, printed pp.121--122; 9.3--9.4, pp.142--143.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem index_of_local_image
    (h : LocallyRankOneTriple P B) (v : Vertex (family P))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (A : Subgroup G) (hAH : A ≤ graphLocalGroup (family P) v)
    (T : Sylow 2 SL(2,F))
    (hi : (A.subgroupOf (graphLocalGroup (family P) v)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) v)))) = T) :
    (Q (family P) v).relIndex A = Nat.card F := by
  let H := graphLocalGroup (family P) v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkmap : q.ker.map H.subtype = Q (family P) v := hk ▸ graphLocalGroup_core h v
  have hh := relIndex_ker (A.subgroupOf H) q
  rw [←relIndex_map_map_of_injective _ _ H.subtype_injective,hkmap,
    map_subgroupOf_eq_of_le hAH,hi] at hh
  exact hh.trans (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv)

/-- The adjacent-core obstruction and the two actual linear markings force
any two distinct neighboring intersections to generate the whole middle core. -/
theorem linear_middle_core_product
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {w v r : Vertex (family P)} (hv : (graph (family P)).Adj w v)
    (hr : (graph (family P)).Adj w r) (hne : v ≠ r)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (ew : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F))
    (ev : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,K)) :
    Q (family P) w = (Q (family P) v ⊓ Q (family P) w) ⊔
      (Q (family P) r ⊓ Q (family P) w) := by
  let := finite_endpoints h
  let Γ := family P
  let N := (Q Γ v ⊓ Q Γ w) ⊔ (Q Γ r ⊓ Q Γ w)
  have hNW : N ≤ Q Γ w := sup_le inf_le_right inf_le_right
  have hind (x : Vertex Γ) (hx : (graph Γ).Adj w x) :
      (Q Γ w).relIndex (Q Γ x) = Nat.card F := by
    obtain ⟨T,hT,_⟩ := linear_neighbor_core_sylow_image h hB hS hx
      (core_escape_of_intersection_obstruction Γ (hob x w hx.symm)) ew
    exact index_of_local_image h w ew _ (neighbor_core_le_localGroup h hB hS hx) T hT
  have hgen : graphLocalGroup Γ w = (Q Γ v ⊔ Q Γ r) ⊔ Q Γ w := by
    have hh := linear_local_two_actor_generation h hB hS hv hr hne ew
      (Q Γ v) (Q Γ r) (neighbor_core_le_localGroup h hB hS hv)
      (neighbor_core_le_localGroup h hB hS hr)
      (isPGroup_pCoreIn 2 _) (isPGroup_pCoreIn 2 _) (hind v hv) (hind r hr)
      (Q_le_stabilizer Γ v) (Q_le_stabilizer Γ r)
    simpa only [sup_comm,sup_left_comm,sup_assoc] using hh
  have hn : stabilizer Γ w ≤ normalizer (N : Set G) :=
    CommutingThreeProfile.middle_core_product_full_normalizer Γ
      (fun x => (source_Z_Q_U h x).2) hv.symm hr.symm
      (graphLocalGroup Γ w) (sylowGenerated_le _) hgen
      (fun x hx => graphLocalGroup_transitive h hB hS w ⟨r,hr⟩ ⟨x,hx⟩)
  have hescape : ¬ N ≤ Q Γ v := by
    intro hh
    have he : N = Q Γ v ⊓ Q Γ w := le_antisymm (le_inf hh hNW) le_sup_left
    exact hob w v hv (he ▸ hn)
  let H := graphLocalGroup Γ v
  let q := ev.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hWH : Q Γ w ≤ H := neighbor_core_le_localGroup h hB hS hv.symm
  have hNH : N ≤ H := hNW.trans hWH
  obtain ⟨T,hT,hfix⟩ := linear_neighbor_core_sylow_image h hB hS hv.symm
    (core_escape_of_intersection_obstruction Γ (hob w v hv)) ev
  let I := (N.subgroupOf H).map q
  have hIT : I ≤ T := (map_mono (comap_mono hNW)).trans hT.le
  have hIne : I ≠ ⊥ := by
    intro he
    have hk : q.ker = pCore 2 H := by
      rw [MonoidHom.ker_comp_of_injective _ _ ev.injective,QuotientGroup.ker_mk']
    have hh := (map_eq_bot_iff (N.subgroupOf H)).mp he
    apply hescape
    intro x hx
    have hx' := hh (show (⟨x,hNH hx⟩ : H) ∈ N.subgroupOf H from hx)
    rw [hk] at hx'
    exact graphLocalGroup_core h v ▸ mem_map_of_mem H.subtype hx'
  have hnI : normalizer (T : Set SL(2,K)) ≤ normalizer (I : Set SL(2,K)) := by
    intro x hx
    obtain ⟨l,rfl⟩ := (ev.surjective.comp (QuotientGroup.mk'_surjective _)) x
    have hl : l ∈ normalizer (N.subgroupOf H : Set H) := by
      rw [←subgroupOf_normalizer_eq hNH]
      exact hn ((hfix l).mp hx)
    exact le_normalizer_map q (mem_map_of_mem q hl)
  have hfull : I = T := Matrix.SpecialLinearGroup.sylow_eq_of_normalized T I hIT hIne hnI
  have hi := index_of_local_image h v ev N hNH T hfull
  have he := linear_local_pgroup_saturation h v ev N (Q Γ w) hNW hWH
    (isPGroup_pCoreIn 2 _) hi
  exact he.trans (sup_eq_left.mpr (by rw [inf_comm]; exact le_sup_left))


/-- Saturation of the original intersection bounds its commutator by the
terminal omega-center. Only the actual opposite full-index actor is used. -/
theorem linear_commutator_intersection_bound
    (h : LocallyRankOneTriple P B)
    {a' v w : Vertex (family P)} (hv : (graph (family P)).Adj a' v)
    (A R : Subgroup G) [IsMulCommutative A]
    (hAQ : A ≤ Q (family P) w ⊓ Q (family P) v) (hRA : R ≤ A)
    (hRD : R ≤ V (family P) a' 1)
    (hcore : ⁅Q (family P) a',V (family P) a' 1⁆ ≤ Z (family P) a')
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) a' ⧸ pCore 2 (graphLocalGroup (family P) a')) ≃* SL(2,F))
    (hIH : Q (family P) w ⊓ Q (family P) v ≤ graphLocalGroup (family P) a')
    (hi : (Q (family P) a').relIndex A = Nat.card F) :
    ⁅R,Q (family P) w ⊓ Q (family P) v⁆ ≤ Z (family P) a' := by
  let := finite_endpoints h
  let Γ := family P
  let I := Q Γ w ⊓ Q Γ v
  have hprod := linear_local_pgroup_saturation h a' e A I hAQ hIH
    ((isPGroup_pCoreIn 2 (stabilizer Γ w)).to_le inf_le_left) hi
  have hIR : I ≤ normalizer (Z Γ a' : Set G) :=
    (inf_le_right.trans ((source_Z_Q_U h v).2.trans
      ((ballKernel_one_le_edge Γ hv.symm).trans inf_le_right))).trans
        (CommutingNontrivial.stabilizer_normalizes_Z Γ a')
  change ⁅R,I⁆ ≤ Z Γ a'
  rw [commutator_comm,hprod]
  apply commutator_sup_le_of_relative_normal I A (I ⊓ Q Γ a') R (Z Γ a')
    hIR hAQ inf_le_left
  · exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hRA.trans (le_centralizer A)))).le.trans bot_le
  · exact (commutator_mono inf_le_right hRD).trans hcore

/-- A centralizer supplement transfers a bound at one neighboring core
intersection to every neighbor, without assuming R is normal in the local group. -/
theorem commutator_neighbor_bound_of_centralizer_supplement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {w v : Vertex (family P)} (hv : (graph (family P)).Adj w v)
    (R : Subgroup G)
    (hsupp : graphLocalGroup (family P) w =
      (graphLocalGroup (family P) w ⊓ centralizer (R : Set G)) ⊔ Q (family P) w)
    (hbound : ⁅R,Q (family P) w ⊓ Q (family P) v⁆ ≤ Z (family P) v) :
    ∀ r : Vertex (family P), (graph (family P)).Adj w r →
      ⁅R,Q (family P) w ⊓ Q (family P) r⁆ ≤ Z (family P) r := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ w
  let C := H ⊓ centralizer (R : Set G)
  have hn : C ≤ normalizer (Q Γ w : Set G) :=
    (inf_le_left.trans (sylowGenerated_le _)).trans (stabilizer_normalizes_Q Γ w)
  intro r hr
  obtain ⟨g,hg,hgv⟩ := graphLocalGroup_transitive h hB hS w ⟨v,hv⟩ ⟨r,hr⟩
  change g • v = r at hgv
  have hg' : g ∈ C ⊔ Q Γ w := hsupp ▸ hg
  change g ∈ (↑(C ⊔ Q Γ w) : Set G) at hg'
  rw [coe_mul_of_left_le_normalizer_right C (Q Γ w) hn] at hg'
  obtain ⟨c,hc,q,hq,rfl⟩ := hg'
  have hqv : q • v = v := (source_Z_Q_U h w).2.trans
    ((ballKernel_one_le_edge Γ hv).trans inf_le_right) hq
  rw [mul_smul,hqv] at hgv
  have hcw : c • w = w := sylowGenerated_le _ hc.1
  have hRc : R.map (MulAut.conj c).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer (R : Set G) hc.2)
  have hh := map_mono (f := (MulAut.conj c).toMonoidHom) hbound
  rw [map_commutator,hRc,Subgroup.map_inf _ _ _ (MulAut.conj c).injective,
    ←Q_translate,←Q_translate,←Z_translate,hcw,hgv] at hh
  exact hh

/-- The normal commutator lies in the product of any two distinct neighboring
centers once its single-intersection bound is known. -/
theorem linear_commutator_core_bound
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {w v r : Vertex (family P)} (hv : (graph (family P)).Adj w v)
    (hr : (graph (family P)).Adj w r) (hne : v ≠ r)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (ew : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F))
    (ev : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,K))
    (R : Subgroup G)
    (hsupp : graphLocalGroup (family P) w =
      (graphLocalGroup (family P) w ⊓ centralizer (R : Set G)) ⊔ Q (family P) w)
    (hbound : ⁅R,Q (family P) w ⊓ Q (family P) v⁆ ≤ Z (family P) v) :
    ⁅R,Q (family P) w⁆ ≤ Z (family P) v ⊔ Z (family P) r := by
  let := finite_endpoints h
  let Γ := family P
  have hbound' := commutator_neighbor_bound_of_centralizer_supplement h hB hS hv R hsupp hbound r hr
  have hn (x : Vertex Γ) (hx : (graph Γ).Adj w x) :
      Q Γ w ≤ normalizer (Z Γ x : Set G) :=
    ((source_Z_Q_U h w).2.trans ((ballKernel_one_le_edge Γ hx).trans inf_le_right)).trans
      (CommutingNontrivial.stabilizer_normalizes_Z Γ x)
  have hnZ : Q Γ w ≤ normalizer ((Z Γ v ⊔ Z Γ r : Subgroup G) : Set G) :=
    (le_inf (hn v hv) (hn r hr)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  rw [commutator_comm,linear_middle_core_product h hB hS hob hv hr hne ew ev]
  apply commutator_sup_le_of_relative_normal (Q Γ w) _ _ R _ hnZ inf_le_right inf_le_right
  · simpa only [commutator_comm,inf_comm] using hbound.trans le_sup_left
  · simpa only [commutator_comm,inf_comm] using hbound'.trans le_sup_right


private theorem neighbor_span_le_core_of_distance
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hd : (graph (family P)).dist v w + 1 < b (family P)) :
    V (family P) v 1 ≤ Q (family P) w := by
  let := finite_endpoints h
  let Γ := family P
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  apply Z_le_Q_of_dist_lt_b Γ (fun x => (source_Z_Q_U h x).1) (source_kernel_sylow h hB hS)
  have hz' := (mem_ball_iff Γ h.generate v z 1).mp hz
  have ht := (connected Γ h.generate).dist_triangle (u := z) (v := v) (w := w)
  rw [SimpleGraph.dist_comm (u := z) (v := v)] at ht
  change (graph Γ).dist v w + 1 < b Γ at hd
  omega

universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The large-distance geometric bound in 9.8 on the actual chosen path.
The forward full-index span fills the core intersection; its elementary
commutator gives the terminal center bound, which the centralizer supplement
transports to the other neighboring intersection. -/
theorem reduced_linear_path_commutator_bound
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {a beta a' v w r : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 3 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (eα : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,K))
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (ew : (graphLocalGroup (Reduction.reducedFamily L S₀) w ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w)) ≃* SL(2,F))
    (hi : (Q (Reduction.reducedFamily L S₀) a').relIndex
      (V (Reduction.reducedFamily L S₀) beta 1) = Nat.card F)
    (hcore : ⁅Q (Reduction.reducedFamily L S₀) beta,V (Reduction.reducedFamily L S₀) beta 1⁆ =
      Z (Reduction.reducedFamily L S₀) beta)
    (hv : (graph (Reduction.reducedFamily L S₀)).Adj a' v)
    (hw : (graph (Reduction.reducedFamily L S₀)).Adj v w)
    (hr : (graph (Reduction.reducedFamily L S₀)).Adj w r) (hne : v ≠ r)
    (hdv : (graph (Reduction.reducedFamily L S₀)).dist beta v + 2 = b (Reduction.reducedFamily L S₀))
    (hdw : (graph (Reduction.reducedFamily L S₀)).dist beta w + 3 = b (Reduction.reducedFamily L S₀))
    (hsupp : let Γ := Reduction.reducedFamily L S₀
      graphLocalGroup Γ w = (graphLocalGroup Γ w ⊓
        centralizer ((⁅V Γ beta 1,V Γ a' 1⁆ : Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀))) ⊔ Q Γ w) :
    let Γ := Reduction.reducedFamily L S₀
    let R := ⁅V Γ beta 1,V Γ a' 1⁆
    ⁅R,Q Γ w ⊓ Q Γ v⁆ ≤ Z Γ a' ∧
      ⁅R,Q Γ w⁆ ≤ Z Γ v ⊔ Z Γ r ∧ ⁅R,Q Γ w⁆ ≤ V Γ w 1 := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hZ := fun z => (source_Z_Q_U ht z).1
  have hSyl := Reduction.reduced_kernel_sylow h
  have hb1 : 1 < b Γ := by change 3 < b Γ at hb; omega
  have hb2 : 2 < b Γ := by change 3 < b Γ at hb; omega
  obtain ⟨hodd,_,hω,_⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb1 hcomm
  have hba : beta.type = a'.type := by
    apply (even_dist_iff Γ ht.generate beta a').mp
    obtain ⟨k,hk⟩ := hodd
    change b Γ = 2*k+1 at hk
    change (graph Γ).dist beta a' + 1 = b Γ at hd
    exact ⟨k,by omega⟩
  have hav : a.type = v.type := by
    have ha := hab.1
    have hv' := hv.1
    rw [←hba] at hv'
    cases ha' : a.type <;> cases hb' : beta.type <;> cases hv'' : v.type <;> simp_all
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ beta a').mpr hba
  obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport ht g hg
  let ea' := f.symm.trans eβ
  have hcore' : ⁅Q Γ a',V Γ a' 1⁆ = Z Γ a' := by
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hcore
    rw [map_commutator,←Q_translate,←V_translate,←Z_translate,hg] at hh
    exact hh
  have hω' : Z Γ a' = omegaCenterIn (graphLocalGroup Γ a') := by
    have he := graphLocalGroup_conjugate ht g beta
    change graphLocalGroup Γ (g • beta) = (graphLocalGroup Γ beta).map (MulAut.conj g).toMonoidHom at he
    change Z Γ beta = omegaCenterIn (graphLocalGroup Γ beta) at hω
    rw [←hg,Z_translate,he,
      ←NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g).injective,hω]
  have hZZ : Z Γ a' ≤ Z Γ v := hω' ▸ intrinsic_local_omega_le_neighbor_Z ht hB hS hv
  obtain ⟨k,hk⟩ := (same_orbit_iff Γ a v).mpr hav
  obtain ⟨_,fv,_,_,_⟩ := local_quotient_parameter_transport ht k hk
  let ev := fv.symm.trans eα
  let A := V Γ beta 1
  let R := ⁅A,V Γ a' 1⁆
  let := V_elementary Γ ht.generate hZ hSyl beta (r := 1) (by simpa using hb2)
  have hAQ : A ≤ Q Γ w ⊓ Q Γ v := le_inf
    (neighbor_span_le_core_of_distance ht hB hS (by
      change (graph Γ).dist beta w + 1 < b Γ
      change (graph Γ).dist beta w + 3 = b Γ at hdw
      omega))
    (neighbor_span_le_core_of_distance ht hB hS (by
      change (graph Γ).dist beta v + 1 < b Γ
      change (graph Γ).dist beta v + 2 = b Γ at hdv
      omega))
  have hRA : R ≤ A := le_normalizer_iff_commutator_le_left.mp
    ((V_le_stabilizer Γ ht.generate a' beta (by rw [SimpleGraph.dist_comm]; exact hd.le)).trans
      (stabilizer_normalizes_V Γ beta 1))
  have hRD : R ≤ V Γ a' 1 := le_normalizer_iff_commutator_le_right.mp
    ((V_le_stabilizer Γ ht.generate beta a' hd.le).trans (stabilizer_normalizes_V Γ a' 1))
  have hbound : ⁅R,Q Γ w ⊓ Q Γ v⁆ ≤ Z Γ a' :=
    linear_commutator_intersection_bound ht hv A R hAQ hRA hRD hcore'.le ea'
      (inf_le_right.trans (neighbor_core_le_localGroup ht hB hS hv)) hi
  have hfull := linear_commutator_core_bound ht hB hS hob hw.symm hr hne ew ev R hsupp (hbound.trans hZZ)
  exact ⟨hbound,hfull,hfull.trans (sup_le (CommutingNontrivial.Z_neighbor_le_V Γ hw.symm)
    (CommutingNontrivial.Z_neighbor_le_V Γ hr))⟩


/-- Original F1.11 application of the large-distance normal commutator bound.
The last three vertices are constructed on the same chosen geodesic from beta.
Both original markings and natural sections, the shifted natural section and
all genuine earlier-source inputs are retained. -/
theorem reduced_critical_commutator_geometric_bound
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 3 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (h8 : ChapterEightDistance (Reduction.reducedFamily L S₀))
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
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧ NaturalResidualSection h beta eβ n ∧
        ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
          0 < m ∧ Nat.card K = 2^m ∧
          ∃ eα : (H ⧸ pCore 2 H) ≃* SL(2,K),
            Nat.card K = Nat.card F ∧
            ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅Q Γ beta,V Γ beta 1⁆ = Z Γ beta ∧
            (let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
             letI : Algebra (ZMod 2) K := ZMod.algebra K 2
             ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)))
               (T : Sylow 2 SL(2,K)),
               (∀ (l : H) (z : Additive (Z Γ a)),
                 ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
                   (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
               Function.Injective ρ ∧ IsSourceNatural ρ T m ∧
               ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → K),
                 ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) ∧
            ∃ v w r : Vertex Γ,
              (graph Γ).Adj a' v ∧ (graph Γ).Adj v w ∧ (graph Γ).Adj w r ∧ v ≠ r ∧
              (graph Γ).dist a v + 1 = b Γ ∧ (graph Γ).dist a w + 2 = b Γ ∧
              (graph Γ).dist beta v + 2 = b Γ ∧ (graph Γ).dist beta w + 3 = b Γ ∧
              (graph Γ).dist beta r + 4 = b Γ ∧
            ∃ ew : (graphLocalGroup Γ w ⧸ pCore 2 (graphLocalGroup Γ w)) ≃* SL(2,F),
              NaturalResidualSection h w ew n ∧
              (Q Γ w).relIndex (V Γ a 2) = Nat.card F ∧
              (∃ g : Reduction.G₀ L S₀, g • w = w ∧
                ⁅V Γ a' 1,(V Γ a 2).map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
                graphLocalGroup Γ w = Q Γ w ⊔ V Γ a 2 ⊔
                  (V Γ a 2).map (MulAut.conj g).toMonoidHom) ∧
              graphLocalGroup Γ w = (graphLocalGroup Γ w ⊓
                centralizer ((⁅V Γ beta 1,V Γ a' 1⁆ : Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀))) ⊔ Q Γ w ∧
              graphLocalGroup Γ w ≤ normalizer
                (⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w⁆ : Subgroup (Reduction.G₀ L S₀)) ∧
              ⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w⁆ ≤ Q Γ w ∧
              ⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w ⊓ Q Γ v⁆ ≤ Z Γ a' ∧
              ⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w⁆ ≤ Z Γ v ⊔ Z Γ r ∧
              ⁅⁅V Γ beta 1,V Γ a' 1⁆,Q Γ w⁆ ≤ V Γ w 1 := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hb1 : 1 < b Γ := by change 3 < b Γ at hb; omega
  have htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥ := by
    by_contra he
    exact Nat.ne_of_gt hb (h8 a beta a' hc hab hd hb1 hcomm he)
  have hzero (z : Vertex Γ) (hz : (graph Γ).Adj z a')
      (hzc : IsCriticalPair Γ z beta) (hzcomm : ⁅Z Γ z,Z Γ beta⁆ = ⊥)
      (he : ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ ≠ ⊥) : False :=
    Nat.ne_of_gt hb (h8 z a' beta hzc hz
      (by rwa [SimpleGraph.dist_comm]) hb1 hzcomm he)
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,_,_,hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,_,_,hi,hpath,hcQ,hcV,hnat⟩ :=
    reduced_critical_reciprocal_sections h hc hab hd hb1 hcomm htriv
      (fun z hz hzc hzcomm he => (hzero z hz hzc hzcomm he).elim) hob Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  have hodd := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb1 hcomm).1
  have hb4 : 4 < b Γ := by
    obtain ⟨k,hk⟩ := hodd
    change b Γ = 2*k+1 at hk
    change 3 < b Γ at hb
    omega
  change (graph Γ).dist beta a' + 1 = b Γ at hd
  have hcd : (graph Γ).dist a a' = b Γ := hc.1
  have hne₀ : beta ≠ a' := by
    intro he
    rw [he,SimpleGraph.dist_self] at hd
    omega
  obtain ⟨v,hv,hdv₀⟩ := exists_predecessor Γ ht.generate beta a' hne₀
  have hdbv : (graph Γ).dist beta v + 2 = b Γ := by omega
  have hne₁ : beta ≠ v := by
    intro he
    rw [he,SimpleGraph.dist_self] at hdbv
    omega
  obtain ⟨w,hw,hdw₀⟩ := exists_predecessor Γ ht.generate beta v hne₁
  have hdbw : (graph Γ).dist beta w + 3 = b Γ := by omega
  have hne₂ : beta ≠ w := by
    intro he
    rw [he,SimpleGraph.dist_self] at hdbw
    omega
  obtain ⟨r,hr,hdr₀⟩ := exists_predecessor Γ ht.generate beta w hne₂
  have hdbr : (graph Γ).dist beta r + 4 = b Γ := by omega
  have hne : v ≠ r := by intro he; rw [he] at hdbv; omega
  have hdav : (graph Γ).dist a v + 1 = b Γ := by
    have h₁ := (connected Γ ht.generate).dist_triangle (u := a) (v := beta) (w := v)
    have h₂ := (connected Γ ht.generate).dist_triangle (u := a) (v := v) (w := a')
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab] at h₁
    rw [hcd,SimpleGraph.dist_eq_one_iff_adj.mpr hv.symm] at h₂
    omega
  have hdaw : (graph Γ).dist a w + 2 = b Γ := by
    have h₁ := (connected Γ ht.generate).dist_triangle (u := a) (v := beta) (w := w)
    have h₂ := (connected Γ ht.generate).dist_triangle (u := a) (v := w) (w := v)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab] at h₁
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hw.symm] at h₂
    omega
  obtain ⟨ew,hnatw,hiW,hgen,hsupp,hnorm,hDQ⟩ :=
    reduced_linear_commutator_centralizer_supplement h h8 hob hc hab hd hb hcomm hn hF eα eβ
      hx hi hpath hv hw hdav hdaw
  have hbounds := reduced_linear_path_commutator_bound h hob hc hab hd hb hcomm eα eβ ew hx hcV
    hv hw hr hne hdbv hdbw hsupp
  exact ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hres,K,instK,finK,charK,m,hm,hK,eα,
    heq,hcQ,hcV,hnat,v,w,r,hv,hw,hr,hne,hdav,hdaw,hdbv,hdbw,hdbr,
    ew,hnatw,hiW,hgen,hsupp,hnorm,hDQ,hbounds⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.PathCartanExtension
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicCentralNeighbors

/-!
# The extended Cartan and the remote permutation kernel

The original natural center is the direct product of two central neighbor
lines. Criticality then makes the new preceding line escape the terminal
core. Its image, normalized by the same full Cartan, is the full linear
root group and acts transitively on the other neighbors. A commuting
actor fixing a second neighbor therefore lies in the entire local kernel.

Cardinality identifies the resulting factor with the full Cartan kernel
intersection. Oddness and the adjacent-kernel equality give its next
kernel exclusion. `DistanceThreeRemoteKernel` applies these arguments to
the original F.1.11 configuration, retaining both natural sections.

Source: DGS, *Groups and Graphs* (1985), 9.10(2)--(3), printed p.148;
the local root action is the characteristic-two case of 5.1.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Two distinct central neighboring centers fill the actual natural center,
using their original orders and disjointness. -/
theorem reduced_natural_neighbor_centers_split
    (h : HypothesisF11 L S)
    {a beta l : Vertex (Reduction.reducedFamily L S)}
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hal : (graph (Reduction.reducedFamily L S)).Adj a l) (hne : beta ≠ l)
    (hω : Z (Reduction.reducedFamily L S) beta =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) beta))
    {q : ℕ} (ha : Nat.card (Z (Reduction.reducedFamily L S) a) = q^2)
    (hb : Nat.card (Z (Reduction.reducedFamily L S) beta) = q) :
    Z (Reduction.reducedFamily L S) a =
      Z (Reduction.reducedFamily L S) beta ⊔ Z (Reduction.reducedFamily L S) l ∧
    Disjoint (Z (Reduction.reducedFamily L S) beta) (Z (Reduction.reducedFamily L S) l) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  let : Finite (Z Γ a) := Finite.of_injective (inclusion (Z_le_stabilizer Γ a)) (inclusion_injective _)
  obtain ⟨g,_,hg⟩ := locally_transitive Γ hab hal
  have hωl : Z Γ l = omegaCenterIn (graphLocalGroup Γ l) := by
    have hh := graphLocalGroup_conjugate ht g beta
    change graphLocalGroup Γ (g • beta) = (graphLocalGroup Γ beta).map (MulAut.conj g).toMonoidHom at hh
    rw [←hg,Z_translate,hh,
      ←NilesRankOneKernel.omegaCenterIn_map_injective
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,hω]
  have hba : Z Γ beta ≤ Z Γ a := hω ▸ intrinsic_local_omega_le_neighbor_Z ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab.symm
  have hla : Z Γ l ≤ Z Γ a := hωl ▸ intrinsic_local_omega_le_neighbor_Z ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hal.symm
  have hcardl : Nat.card (Z Γ l) = q := by
    rw [←hg,Z_translate,card_map_of_injective (MulAut.conj g).injective]
    exact hb
  have hdis := Reduction.reduced_intrinsic_central_neighbor_centers_disjoint h hab hal hne hω
  have hn : Z Γ l ≤ normalizer (Z Γ beta : Set (Reduction.G₀ L S)) :=
    (hla.trans (le_centralizer (Z Γ a))).trans
      ((centralizer_le hba).trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨(eq_of_le_of_card_ge (sup_le hba hla) ?_).symm,hdis⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hdis,ha,hb,hcardl,pow_two]

/-- The new preceding center escapes the original terminal core: otherwise
the two neighboring lines would put the critical natural center in it. -/
theorem reduced_critical_extended_center_escape
    (h : HypothesisF11 L S)
    {a beta a' l : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 = b (Reduction.reducedFamily L S))
    (hal : (graph (Reduction.reducedFamily L S)).Adj a l) (hne : beta ≠ l)
    (hω : Z (Reduction.reducedFamily L S) beta =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) beta))
    {q : ℕ} (ha : Nat.card (Z (Reduction.reducedFamily L S) a) = q^2)
    (hb : Nat.card (Z (Reduction.reducedFamily L S) beta) = q) :
    Z (Reduction.reducedFamily L S) a =
      Z (Reduction.reducedFamily L S) beta ⊔ Z (Reduction.reducedFamily L S) l ∧
    Disjoint (Z (Reduction.reducedFamily L S) beta) (Z (Reduction.reducedFamily L S) l) ∧
    ¬ Z (Reduction.reducedFamily L S) l ≤ Q (Reduction.reducedFamily L S) a' := by
  obtain ⟨he,hdis⟩ := reduced_natural_neighbor_centers_split h hab hal hne hω ha hb
  refine ⟨he,hdis,?_⟩
  intro hl
  apply hc.2
  apply le_trans _ (source_Z_Q_U (Reduction.reduced_triple h) a').2
  rw [he]
  apply sup_le ?_ hl
  let : ∀ i, Finite (Reduction.reducedFamily L S i) := finite_endpoints (Reduction.reduced_triple h)
  exact Z_le_Q_of_dist_lt_b (Reduction.reducedFamily L S)
    (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
    (Reduction.reduced_kernel_sylow h) beta a' (by omega)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial


namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A nontrivial two-subgroup normalized by a full path Cartan acts
transitively on the other neighbors of its marked linear vertex. -/
theorem cartan_normalized_two_subgroup_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (C A : Subgroup G)
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hc : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hAE : A ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hp : IsPGroup 2 A) (hn : C ≤ normalizer (A : Set G))
    (hne : ¬ A ≤ Q (family P) v) :
    ∀ x y : (graph (family P)).neighborSet v, x.val ≠ w → y.val ≠ w →
      ∃ g ∈ A, g • x.val = y.val := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let E := stabilizer Γ v ⊓ stabilizer Γ w
  let S := E.pCoreIn 2
  let T := C ⊓ H
  let D := T ⊔ A
  have hAH : A ≤ H := pGroup_le_sylowGenerated _ A (hAE.trans inf_le_left) hp
  have hDH : D ≤ H := sup_le inf_le_right hAH
  have hDE : D ≤ E := sup_le (inf_le_left.trans hCE) hAE
  have hTS : S ⊔ T = H ⊓ E := (edge_complement_local_torus h hB hS hvw e C hCE hc hg).2
  have hSH : S ≤ H := le_sup_left.trans (hTS.le.trans inf_le_left)
  have hDS : D ⊔ S = H ⊓ E := by
    apply le_antisymm (sup_le (le_inf hDH hDE) (le_inf hSH (pCoreIn_le 2 E)))
    rw [←hTS]
    exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
  have hDN : D ≤ normalizer (A : Set G) := sup_le (inf_le_left.trans hn) A.le_normalizer
  let q₀ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk₀ : q₀.ker = (Q Γ v).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    rw [←graphLocalGroup_core h v]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  obtain ⟨s,hs⟩ := source_linear_borel_marking h hB hS hvw q₀ hq₀ hk₀
  let q := (MulAut.conj s).toMonoidHom.comp q₀
  have hk : q.ker = (Q Γ v).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj s).injective,hk₀]
  have hgen : D.subgroupOf H ⊔ S.subgroupOf H = (Matrix.SpecialLinearGroup.rankOneBorel F).comap q := by
    rw [←hs]
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hDH,map_subgroupOf_eq_of_le hSH,hDS,
      subgroupOf_map_subtype]
    apply le_antisymm (le_inf (inf_le_right.trans inf_le_right) inf_le_left)
    intro z hz
    exact ⟨hz.2,⟨sylowGenerated_le _ hz.2,hz.1⟩⟩
  have hnorm : D.subgroupOf H ≤ normalizer (A.subgroupOf H : Set H) := by
    apply le_normalizer_iff.mpr
    intro d hd a ha
    exact (mem_normalizer_iff.mp (hDN hd) (a : G)).mp ha
  have him := Matrix.SpecialLinearGroup.normal_two_image_of_borel_supplement q
    ((MulAut.conj s).surjective.comp hq₀) (D.subgroupOf H) (S.subgroupOf H)
    (A.subgroupOf H) hgen (isPGroup_pCoreIn 2 E).comap_subtype hp.comap_subtype
    (comap_mono (show A ≤ D from le_sup_right)) hnorm (by
      intro he
      apply hne
      intro a ha
      have hh := he (show (⟨a,hAH ha⟩ : H) ∈ A.subgroupOf H from ha)
      rw [hk] at hh
      exact hh)
  intro x y hx hy
  have horbit (z : (graph Γ).neighborSet v) : ∃ g : H, g • w = z.val := by
    obtain ⟨g,hg,hgz⟩ := graphLocalGroup_transitive h hB hS v ⟨w,hvw⟩ z
    exact ⟨⟨g,hg⟩,hgz⟩
  obtain ⟨g,hg,hgxy⟩ := Matrix.SpecialLinearGroup.moves_of_root_image q (A.subgroupOf H)
    him.ge w x.val y.val hs hx hy (horbit x) (horbit y)
  exact ⟨g,hg,hgxy⟩

/-- A centralizer fixing two neighbors fixes the entire local action when
the centralized subgroup is transitive off one of those neighbors. -/
theorem centralizer_le_kernel_of_two_fixed_neighbors
    {Γ : Bool → Subgroup G} {v w r : Vertex Γ}
    (hr : (graph Γ).Adj v r) (hrw : r ≠ w)
    (A D : Subgroup G)
    (htrans : ∀ x y : (graph Γ).neighborSet v, x.val ≠ w → y.val ≠ w →
      ∃ g ∈ A, g • x.val = y.val)
    (hDv : D ≤ stabilizer Γ v) (hDw : D ≤ stabilizer Γ w)
    (hDr : D ≤ stabilizer Γ r) (hDA : D ≤ centralizer (A : Set G)) :
    D ≤ ballKernel Γ v 1 := by
  intro d hd x hx
  rcases (mem_ball_one Γ v x).mp hx with hx | rfl
  · by_cases he : x = w
    · subst x; exact hDw hd
    · obtain ⟨g,hg,hgr⟩ := htrans ⟨r,hr⟩ ⟨x,hx⟩ hrw he
      change g • r = x at hgr
      have hcomm : g*d = d*g := hDA hd g hg
      rw [←hgr,←mul_smul,←hcomm,mul_smul,hDr hd]
  · exact hDv hd



universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The alpha-minus-one factor of the same Cartan is in the full
alpha-prime permutation kernel, as required in source 9.10(2). -/
theorem reduced_extended_cartan_remote_kernel
    (h : HypothesisF11 L S₀)
    {a beta x a' l r : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hbx : (graph (Reduction.reducedFamily L S₀)).Adj beta x)
    (hxd : (graph (Reduction.reducedFamily L S₀)).Adj x a')
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb3 : b (Reduction.reducedFamily L S₀) = 3)
    (hal : (graph (Reduction.reducedFamily L S₀)).Adj a l) (hlb : l ≠ beta)
    (hdr : (graph (Reduction.reducedFamily L S₀)).Adj a' r) (hrx : r ≠ x)
    (hω : Z (Reduction.reducedFamily L S₀) beta =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S₀) beta))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eb : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (ha : Nat.card (Z (Reduction.reducedFamily L S₀) a) = Nat.card F ^ 2)
    (hb : Nat.card (Z (Reduction.reducedFamily L S₀) beta) = Nat.card F)
    (C : Subgroup (Reduction.G₀ L S₀))
    (hfix : C ≤ stabilizer (Reduction.reducedFamily L S₀) a ⊓
      stabilizer (Reduction.reducedFamily L S₀) beta ⊓ stabilizer (Reduction.reducedFamily L S₀) x ⊓
      stabilizer (Reduction.reducedFamily L S₀) a')
    (hext : C ≤ stabilizer (Reduction.reducedFamily L S₀) l ⊓ stabilizer (Reduction.reducedFamily L S₀) r)
    (ho : Odd (Nat.card C))
    (hdis : Disjoint C ((stabilizer (Reduction.reducedFamily L S₀) a ⊓
      stabilizer (Reduction.reducedFamily L S₀) beta : Subgroup (Reduction.G₀ L S₀)).pCoreIn 2))
    (hgen : C ⊔ (stabilizer (Reduction.reducedFamily L S₀) a ⊓
      stabilizer (Reduction.reducedFamily L S₀) beta : Subgroup (Reduction.G₀ L S₀)).pCoreIn 2 =
      stabilizer (Reduction.reducedFamily L S₀) a ⊓ stabilizer (Reduction.reducedFamily L S₀) beta) :
    let Γ := Reduction.reducedFamily L S₀
    Z Γ a = Z Γ beta ⊔ Z Γ l ∧ Disjoint (Z Γ beta) (Z Γ l) ∧
      ¬ Z Γ l ≤ Q Γ a' ∧ C ⊓ graphLocalGroup Γ l ≤ ballKernel Γ a' 1 := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let hB := Reduction.reduced_borel_core_sylow h
  let hS := Reduction.reduced_vertex_sylow h
  obtain ⟨hspan,hzl,hne⟩ := reduced_critical_extended_center_escape h hc hab hd hal hlb.symm hω ha hb
  have bool_eq {i j k : Bool} (hi : i ≠ k) (hj : j ≠ k) : i = j := by
    cases i <;> cases j <;> cases k <;> first | rfl | exact (hi rfl).elim | exact (hj rfl).elim
  have hbl : beta.type = l.type := bool_eq hab.1.symm hal.1.symm
  obtain ⟨g,hgl⟩ := (same_orbit_iff Γ beta l).mpr hbl
  have hωl : Z Γ l = omegaCenterIn (graphLocalGroup Γ l) := by
    have hh := graphLocalGroup_conjugate ht g beta
    change graphLocalGroup Γ (g • beta) = (graphLocalGroup Γ beta).map (MulAut.conj g).toMonoidHom at hh
    rw [←hgl,Z_translate,hh,←NilesRankOneKernel.omegaCenterIn_map_injective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,hω]
  have hbd : beta.type = a'.type := bool_eq hbx.1 hxd.1.symm
  obtain ⟨g,hgd⟩ := (same_orbit_iff Γ beta a').mpr hbd
  obtain ⟨_,e,_,_,_⟩ := local_quotient_parameter_transport ht g hgd
  have hCdx : C ≤ stabilizer Γ a' ⊓ stabilizer Γ x :=
    le_inf (hfix.trans inf_le_right) (hfix.trans (inf_le_left.trans inf_le_right))
  obtain ⟨hdC,hgC⟩ := path_cartan_complement_at_edge ht hab hxd.symm C
    (hfix.trans (inf_le_left.trans inf_le_left)) hCdx ho hdis hgen
  have hla : Z Γ l ≤ Z Γ a := hspan ▸ le_sup_right
  have hax : (graph Γ).dist a x ≤ 2 := by
    have hh := (connected Γ ht.generate).dist_triangle (u := a) (v := beta) (w := x)
    have h₁ : (graph Γ).dist a beta = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hab
    have h₂ : (graph Γ).dist beta x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hbx
    rwa [h₁,h₂] at hh
  have hAE : Z Γ l ≤ stabilizer Γ a' ⊓ stabilizer Γ x := le_inf
    (hla.trans (Z_le_stabilizer_of_dist_le_b Γ ht.generate a a' hc.1.le))
    (hla.trans (Z_le_stabilizer_of_dist_le_b Γ ht.generate a x (by rw [show b Γ = 3 from hb3]; omega)))
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) l
  have htrans := cartan_normalized_two_subgroup_transitive ht hB hS hxd.symm
    (e.symm.trans eb) C (Z Γ l) hCdx hdC hgC hAE (IsElementaryAbelian.isPGroup 2 _)
    ((hext.trans inf_le_left).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ l)) hne
  refine ⟨hspan,hzl,hne,centralizer_le_kernel_of_two_fixed_neighbors hdr hrx
    (Z Γ l) (C ⊓ graphLocalGroup Γ l) htrans
    (inf_le_left.trans (hCdx.trans inf_le_left))
    (inf_le_left.trans (hCdx.trans inf_le_right))
    (inf_le_left.trans (hext.trans inf_le_right)) ?_⟩
  apply le_centralizer_iff.mpr
  intro z hz
  exact centralizer_le (show C ⊓ graphLocalGroup Γ l ≤ graphLocalGroup Γ l from inf_le_right)
    ((mem_omegaCenterIn_iff _ _).mp (hωl ▸ hz)).2.1


/-- In an abelian full Cartan, two disjoint factors of the expected orders
are complementary. A factor contained in a kernel is its exact Cartan intersection. -/
theorem cartan_kernel_factor_of_orders
    {G : Type*} [Group G] (C T D U : Subgroup G) [Finite C] [IsMulCommutative C]
    (hTC : T ≤ C) (hDC : D ≤ C) (hTU : T ≤ U) (hDU : Disjoint D U)
    {q : ℕ} (hC : Nat.card C = q^2) (hT : Nat.card T = q) (hD : Nat.card D = q) :
    C = T ⊔ D ∧ T = C ⊓ U ∧ Disjoint T D := by
  have hd : Disjoint T D := (hDU.mono_right hTU).symm
  have hn : D ≤ normalizer (T : Set G) := (hDC.trans (le_centralizer C)).trans
    ((centralizer_le hTC).trans (Subgroup.centralizer_le_normalizer _))
  have he : C = T ⊔ D := (eq_of_le_of_card_ge (sup_le hTC hDC) (by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hd,hC,hT,hD,pow_two])).symm
  refine ⟨he,le_antisymm (le_inf hTC hTU) ?_,hd⟩
  rintro z ⟨hzC,hzU⟩
  have hz : z ∈ (T : Set G) * (D : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left T D hn,←he]
    exact hzC
  obtain ⟨t,ht,d,hd',rfl⟩ := hz
  have hdU : d ∈ U := by
    simpa only [inv_mul_cancel_left] using U.mul_mem (U.inv_mem (hTU ht)) hzU
  have hd1 : d = 1 := disjoint_def.mp hDU hd' hdU
  change t * d ∈ T
  rw [hd1,mul_one]
  exact ht


/-- An odd subgroup in one full kernel avoids the adjacent full kernel
once their intersection is the intersection of the two-cores. -/
theorem odd_subgroup_disjoint_adjacent_kernel
    {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) {v w : Vertex (family P)}
    (hi : ballKernel (family P) v 1 ⊓ ballKernel (family P) w 1 =
      Q (family P) v ⊓ Q (family P) w)
    (T : Subgroup G) (hT : T ≤ ballKernel (family P) v 1)
    (ho : Odd (Nat.card T)) : Disjoint T (ballKernel (family P) w 1) := by
  let := finite_endpoints h
  let : Finite (Q (family P) v) := Finite.of_injective
    (inclusion (Q_le_stabilizer (family P) v)) (inclusion_injective _)
  have hp : IsPGroup 2 (Q (family P) v) := isPGroup_pCoreIn 2 _
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hd : Disjoint T (Q (family P) v) := disjoint_of_coprime_natCard (by
    rw [hn]
    exact ho.coprime_two_right.pow_right n)
  apply disjoint_def.mpr
  intro t ht hw
  exact disjoint_def.mp hd ht ((hi.le ⟨hT ht,hw⟩).1)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

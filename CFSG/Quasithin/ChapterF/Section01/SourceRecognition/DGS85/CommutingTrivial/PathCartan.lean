module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeTorus
public import CFSG.Quasithin.ChapterF.Section01.SourceCartan

/-!
# The full path Cartan and both intrinsic local factors

The proved F.1.3(5) Cartan construction and the normal reduced Sylow show
that every odd subgroup of the actual reduced Borel is abelian. This
property transports to every graph edge. Hypothesis B's literal Borel
product also transports, now expressed with the intrinsic local actors.

Schur--Zassenhaus places a full edge complement in a regular path fixer.
Its intersections with both adjacent actors are the complete local tori,
each isomorphic to the units of its marked field. The Borel product shows
that these two intersections generate the same full complement. The
natural-center argument separating the factors is in `TorusKernels`, and
`DistanceThreeCartan` applies everything to the original critical path.

Source: DGS, *Groups and Graphs* (1985), Hypothesis B, printed p.95;
6.7--6.8, pp.123--124; 9.9 and the opening of 9.10, p.147. The abelian
complement proof reuses Aschbacher--Smith F.1.3(5), printed p.260.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G]

private theorem odd_commutative_of_complement [Finite G]
    (P A : Subgroup G) [P.Normal] (hp : IsPGroup 2 P)
    (hc : P.IsComplement' A) (ha : IsMulCommutative A)
    (D : Subgroup G) (ho : Odd (Nat.card D)) : IsMulCommutative D := by
  let := ha
  let e := hc.symm.QuotientMulEquiv
  let q := (QuotientGroup.mk' P).comp D.subtype
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  have hd : Disjoint D P := disjoint_of_coprime_natCard (by
    rw [hk]; exact ho.coprime_two_right.pow_right k)
  have hi : Function.Injective q := (injective_iff_map_eq_one q).mpr (by
    intro d hdq
    apply Subtype.ext
    exact disjoint_def.mp hd d.property ((QuotientGroup.eq_one_iff (d : G)).mp hdq))
  let j := e.toMonoidHom.comp q
  have hj : Function.Injective j := e.injective.comp hi
  exact ⟨⟨fun x y => hj ((map_mul j x y).trans ((mul_comm (j x) (j y)).trans (map_mul j y x).symm))⟩⟩

/-- Every odd subgroup of the literal reduced Borel is abelian. -/
theorem reduced_borel_odd_commutative {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (D : Subgroup (Reduction.G₀ L S))
    (hD : D ≤ (Reduction.B₀ L S).subgroupOf (Reduction.G₀ L S))
    (ho : Odd (Nat.card D)) : IsMulCommutative D := by
  let S' := SuzukiContainment.reducedSylow L S
  let B' := commonBorel L S'
  let h' := SuzukiContainment.reduced_hypothesis h
  let := h'.finite_commonBorel
  let : (S'.subgroupOf B').Normal := SuzukiContainment.reduced_sylow_normal h
  obtain ⟨c⟩ := h'.exists_compatibleCartans
  let := c.joint_abelian h'
  let f : D →* B' := {
    toFun d := ⟨(d.val : G),by
      have hd := hD d.property
      change (d.val : G) ∈ Reduction.B₀ L S at hd
      rwa [Reduction.B₀_eq_source h] at hd⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro d e he
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (fun x : B' => (x : G)) he
  have hr : Odd (Nat.card f.range) := by
    rwa [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  let := odd_commutative_of_complement (S'.subgroupOf B')
    ((c.D 0 ⊔ c.D 1).subgroupOf B') h'.S_isP.comap_subtype c.joint_complement
    inferInstance f.range hr
  let e := MonoidHom.ofInjective hf
  exact ⟨⟨fun x y => e.injective ((map_mul e x y).trans ((mul_comm (e x) (e y)).trans (map_mul e y x).symm))⟩⟩

/-- The preceding assertion transports to every actual edge. -/
theorem reduced_edge_odd_commutative {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) {v w : Vertex (Reduction.reducedFamily L S)}
    (hvw : (graph (Reduction.reducedFamily L S)).Adj v w)
    (D : Subgroup (Reduction.G₀ L S))
    (hD : D ≤ stabilizer (Reduction.reducedFamily L S) v ⊓
      stabilizer (Reduction.reducedFamily L S) w)
    (ho : Odd (Nat.card D)) : IsMulCommutative D := by
  let Γ := Reduction.reducedFamily L S
  obtain ⟨g,hg⟩ := edgeStabilizer_map_base Γ hvw
  have hbase : Γ false ⊓ Γ true = (Reduction.B₀ L S).subgroupOf (Reduction.G₀ L S) :=
    (Reduction.reduced_triple h).intersection
  rw [hbase] at hg
  let f := (MulAut.conj g).symm
  let T := D.map f.toMonoidHom
  have hT : T ≤ (Reduction.B₀ L S).subgroupOf (Reduction.G₀ L S) := by
    have hh := map_mono (f := f.toMonoidHom) hD
    rw [hg,map_map] at hh
    have he : f.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro z; exact (MulAut.conj g).symm_apply_apply z
    rw [he,Subgroup.map_id] at hh
    exact hh
  have hTo : Odd (Nat.card T) := by
    rwa [card_map_of_injective f.injective]
  let := reduced_borel_odd_commutative h T hT hTo
  let e := D.equivMapOfInjective f.toMonoidHom f.injective
  exact ⟨⟨fun x y => e.injective ((map_mul e x y).trans ((mul_comm (e x) (e y)).trans (map_mul e y x).symm))⟩⟩

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Intersect one full edge complement with the intrinsic actor. The result
is the complete local torus, with its literal Sylow product. -/
theorem edge_complement_local_torus
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (C : Subgroup G)
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hdis : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2))
    (hCS : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w) :
    Nonempty ((C ⊓ graphLocalGroup (family P) v : Subgroup G) ≃* Fˣ) ∧
      (stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2 ⊔
        (C ⊓ graphLocalGroup (family P) v) =
          graphLocalGroup (family P) v ⊓ (stabilizer (family P) v ⊓ stabilizer (family P) w) := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let E := stabilizer Γ v ⊓ stabilizer Γ w
  let S := E.pCoreIn 2
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hES : E ≤ normalizer (S : Set G) := E.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  obtain ⟨R,hR⟩ := local_edge_sylow h hB hS hvw
  change (R : Subgroup H).map H.subtype = S at hR
  have hSH : S ≤ H := hR ▸ map_subtype_le _
  have hR' : (R : Subgroup H) = S.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hSH,hR]
  have hN (l : H) : l ∈ normalizer (R : Set H) ↔ (l : G) ∈ E := by
    change l ∈ normalizer ((R : Subgroup H) : Set H) ↔ _
    rw [hR',←subgroupOf_normalizer_eq hSH]
    change (l : G) ∈ normalizer (S : Set G) ↔ _
    constructor
    · intro hl
      exact (local_edge_core_normalizer h hB hS hvw).le ⟨sylowGenerated_le _ l.property,hl⟩
    · exact fun hl => hES hl
  let D := C ⊓ H
  let DH := D.subgroupOf H
  have hDH : D ≤ H := inf_le_right
  have hDN : DH ≤ normalizer (R : Set H) := fun l hl => (hN l).mpr (hCE hl.1)
  have hd : Disjoint (R : Subgroup H) DH := by
    apply disjoint_def.mpr
    intro l hl hlD
    apply Subtype.ext
    apply disjoint_def.mp hdis hlD.1
    change (l : G) ∈ S
    rw [←hR]
    exact mem_map_of_mem H.subtype hl
  have hs : (R : Subgroup H) ⊔ DH = normalizer (R : Set H) := by
    apply le_antisymm (sup_le (R : Subgroup H).le_normalizer hDN)
    intro l hl
    have hlE := (hN l).mp hl
    have hm : (l : G) ∈ (C : Set G) * (S : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right C S (hCE.trans hES),hCS]
      exact hlE
    obtain ⟨c,hc,s,hs,hcs⟩ := hm
    have hcH : c ∈ H := by
      have he : c = (l : G)*s⁻¹ := by rw [←hcs,mul_inv_cancel_right]
      rw [he]
      exact H.mul_mem l.property (H.inv_mem (hSH hs))
    have hsR : (⟨s,hSH hs⟩ : H) ∈ R := by change (⟨s,hSH hs⟩ : H) ∈ (R : Subgroup H); rw [hR']; exact hs
    have hcD : (⟨c,hcH⟩ : H) ∈ DH := ⟨hc,hcH⟩
    have hh := ((R : Subgroup H) ⊔ DH).mul_mem (mem_sup_right hcD) (mem_sup_left hsR)
    exact (show (⟨c,hcH⟩ : H)*⟨s,hSH hs⟩ = l from Subtype.ext hcs) ▸ hh
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨f⟩ := Matrix.SpecialLinearGroup.sylow_normalizer_complement_equiv_units q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) R
    (hk ▸ pCore_isPGroup.le_sylow_of_normal R) DH hDN hd hs
  have he : S ⊔ D = H ⊓ E := by
    have hm := congrArg (fun U : Subgroup H => U.map H.subtype) hs
    rw [Subgroup.map_sup,hR,map_subgroupOf_eq_of_le hDH] at hm
    have hn : (normalizer (R : Set H)).map H.subtype = H ⊓ E := by
      ext z
      constructor
      · rintro ⟨l,hl,rfl⟩; exact ⟨l.property,(hN l).mp hl⟩
      · intro hz; exact ⟨⟨z,hz.1⟩,(hN ⟨z,hz.1⟩).mpr hz.2,rfl⟩
    exact hm.trans hn
  exact ⟨⟨(subgroupOfEquivOfLe hDH).symm.trans f⟩,he⟩

/-- Hypothesis B's literal reduced Borel is generated by its intersections
with the two intrinsic local actors. -/
theorem reduced_base_edge_local_product {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) :
    let Γ := Reduction.reducedFamily L S
    let E := (Reduction.B₀ L S).subgroupOf (Reduction.G₀ L S)
    E = (E ⊓ graphLocalGroup Γ (base Γ false)) ⊔
      (E ⊓ graphLocalGroup Γ (base Γ true)) := by
  let Γ := Reduction.reducedFamily L S
  have hBG : Reduction.B₀ L S ≤ Reduction.G₀ L S :=
    (show Reduction.B₀ L S ≤ Reduction.P₀ L S 0 from le_sup_right).trans le_sup_left
  have he : Reduction.B₀ L S =
      (Reduction.B₀ L S ⊓ Reduction.enlargedEndpoint L S 0) ⊔
      (Reduction.B₀ L S ⊓ Reduction.enlargedEndpoint L S 1) := by
    apply le_antisymm ?_ (sup_le inf_le_left inf_le_left)
    change ((commonBorel L S ⊓ starredParabolic L S 0) ⊔
      (commonBorel L S ⊓ starredParabolic L S 1) ⊔ (commonBorel L S).pCoreIn 2) ≤ _
    apply sup_le (sup_le ?_ ?_) ?_
    · exact (le_inf (le_sup_left.trans le_sup_left) (inf_le_right.trans le_sup_left)).trans le_sup_left
    · exact (le_inf (le_sup_right.trans le_sup_left) (inf_le_right.trans le_sup_left)).trans le_sup_right
    · exact (le_inf le_sup_right le_sup_right).trans le_sup_left
  apply Subgroup.map_injective (Reduction.G₀ L S).subtype_injective
  rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ (Reduction.G₀ L S).subtype_injective,
    Subgroup.map_inf _ _ _ (Reduction.G₀ L S).subtype_injective,
    map_subgroupOf_eq_of_le hBG,Reduction.reduced_graphLocalGroup_image h false,
    Reduction.reduced_graphLocalGroup_image h true]
  exact he

/-- The same product holds at each edge, with its two original local actors. -/
theorem reduced_edge_local_product {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) {v w : Vertex (Reduction.reducedFamily L S)}
    (hvw : (graph (Reduction.reducedFamily L S)).Adj v w) :
    let Γ := Reduction.reducedFamily L S
    let E := stabilizer Γ v ⊓ stabilizer Γ w
    E = (E ⊓ graphLocalGroup Γ v) ⊔ (E ⊓ graphLocalGroup Γ w) := by
  let Γ := Reduction.reducedFamily L S
  obtain ⟨g,hv,hw⟩ := incident_common_translate Γ hvw.2
  have hi : Γ v.type ⊓ Γ w.type = (Reduction.B₀ L S).subgroupOf (Reduction.G₀ L S) := by
    have he := (Reduction.reduced_triple h).intersection
    have hn := hvw.1
    cases hvt : v.type <;> cases hwt : w.type
    · exact (hn (hvt.trans hwt.symm)).elim
    · exact he
    · exact (inf_comm _ _).trans he
    · exact (hn (hvt.trans hwt.symm)).elim
  have hprod : Γ v.type ⊓ Γ w.type =
      ((Γ v.type ⊓ Γ w.type) ⊓ graphLocalGroup Γ (base Γ v.type)) ⊔
      ((Γ v.type ⊓ Γ w.type) ⊓ graphLocalGroup Γ (base Γ w.type)) := by
    rw [hi]
    have hh := reduced_base_edge_local_product h
    have hn := hvw.1
    cases hvt : v.type <;> cases hwt : w.type
    · exact (hn (hvt.trans hwt.symm)).elim
    · exact hh
    · exact hh.trans (sup_comm _ _)
    · exact (hn (hvt.trans hwt.symm)).elim
  have hm := congrArg (fun U : Subgroup (Reduction.G₀ L S) =>
    U.map (MulAut.conj g).toMonoidHom) hprod
  simp only [Subgroup.map_sup,Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective] at hm
  have hsa := stabilizer_translate Γ g (base Γ v.type)
  have hsb := stabilizer_translate Γ g (base Γ w.type)
  rw [hv] at hsa
  rw [hw] at hsb
  rw [show stabilizer Γ (base Γ v.type) = Γ v.type from Subgroup.CosetGeometry.stabilizer_base _ _] at hsa
  rw [show stabilizer Γ (base Γ w.type) = Γ w.type from Subgroup.CosetGeometry.stabilizer_base _ _] at hsb
  have hla := graphLocalGroup_conjugate (Reduction.reduced_triple h) g (base Γ v.type)
  have hlb := graphLocalGroup_conjugate (Reduction.reduced_triple h) g (base Γ w.type)
  change graphLocalGroup Γ (g • base Γ v.type) = _ at hla
  change graphLocalGroup Γ (g • base Γ w.type) = _ at hlb
  rw [hv] at hla
  rw [hw] at hlb
  change (stabilizer Γ v ⊓ stabilizer Γ w) = _
  rw [hsa,hsb,hla,hlb]
  exact hm


private theorem complement_eq_sup_of_local_products
    (C S E A D : Subgroup G) (hCE : C ≤ E) (hCS : Disjoint C S)
    (hSE : E ≤ normalizer (S : Set G)) (hAC : A ≤ C) (hDC : D ≤ C)
    (hgen : E = (S ⊔ A) ⊔ (S ⊔ D)) : C = A ⊔ D := by
  have hADC : A ⊔ D ≤ C := sup_le hAC hDC
  apply le_antisymm ?_ hADC
  intro c hc
  have hm : c ∈ (S : Set G) * ((A ⊔ D : Subgroup G) : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left S (A ⊔ D) ((hADC.trans hCE).trans hSE)]
    have he : S ⊔ (A ⊔ D) = E := by
      rw [hgen]; ac_rfl
    rw [he]; exact hCE hc
  obtain ⟨s,hs,d,hd,he⟩ := hm
  have hsC : s ∈ C := by
    rw [show s = c*d⁻¹ by rw [←he,mul_inv_cancel_right]]
    exact C.mul_mem hc (C.inv_mem (hADC hd))
  have hs1 : s = 1 := disjoint_def.mp hCS hsC hs
  have he' : d = c := by simpa only [hs1,one_mul] using he
  exact he' ▸ hd

open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon

/-- A common abelian complement fixes the entire path. Its intersections
with the two adjacent intrinsic actors are the full marked local tori,
and together they generate that same complement. -/
theorem reduced_linear_path_cartan {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}
    (h : HypothesisF11 L S₀)
    {v a beta : Vertex (Reduction.reducedFamily L S₀)} {n : ℕ}
    (p : BasedWalk (graph (Reduction.reducedFamily L S₀)) (n+1) v)
    (hp : p.Nonbacktracking)
    (ht : RootPathTransitive (graph (Reduction.reducedFamily L S₀)) (Reduction.G₀ L S₀) v (n+1))
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (ha : a ∈ p.vertices) (hb : beta ∈ p.vertices)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (ea : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,K))
    (eb : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    let E := stabilizer Γ a ⊓ stabilizer Γ beta
    ∃ C : Subgroup (Reduction.G₀ L S₀),
      C ≤ pathStabilizer Γ p ∧ Disjoint C (E.pCoreIn 2) ∧
      C ⊔ E.pCoreIn 2 = E ∧ Odd (Nat.card C) ∧ IsMulCommutative C ∧
      Nonempty ((C ⊓ graphLocalGroup Γ a : Subgroup (Reduction.G₀ L S₀)) ≃* Kˣ) ∧
      Nonempty ((C ⊓ graphLocalGroup Γ beta : Subgroup (Reduction.G₀ L S₀)) ≃* Fˣ) ∧
      C = (C ⊓ graphLocalGroup Γ a) ⊔ (C ⊓ graphLocalGroup Γ beta) := by
  let Γ := Reduction.reducedFamily L S₀
  let htr := Reduction.reduced_triple h
  let hB := Reduction.reduced_borel_core_sylow h
  let hS := Reduction.reduced_vertex_sylow h
  let : ∀ i, Finite (Γ i) := finite_endpoints htr
  let E := stabilizer Γ a ⊓ stabilizer Γ beta
  let S := E.pCoreIn 2
  let A := pathStabilizer Γ p
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer Γ a from inf_le_left)) (inclusion_injective _)
  have hAE : A ≤ E := pathStabilizer_le_edge Γ p ha hb
  have hES : E ≤ normalizer (S : Set (Reduction.G₀ L S₀)) := E.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  have hprod := source_path_edge_product htr hB (source_rankOne_branching htr) ht p hp hab ha hb
  have hgen : A ⊔ S = E := by
    apply SetLike.coe_injective
    rw [coe_mul_of_left_le_normalizer_right A S (hAE.trans hES)]
    exact hprod.symm
  obtain ⟨C,hCA,hd,hCE,ho⟩ := exists_complement_le_of_core_supplement 2 E A hAE
    (source_edge_core_sylow htr hB hab) hgen
  have hC : C ≤ E := hCA.trans hAE
  have hodd : Odd (Nat.card C) := Nat.coprime_two_left.mp ho
  obtain ⟨ea',hpa⟩ := edge_complement_local_torus htr hB hS hab ea C hC hd hCE
  obtain ⟨eb',hpb⟩ := edge_complement_local_torus htr hB hS hab.symm eb C
    (by change C ≤ stabilizer Γ beta ⊓ stabilizer Γ a; exact hC.trans (inf_comm _ _).le)
    (by change Disjoint C ((stabilizer Γ beta ⊓ stabilizer Γ a : Subgroup (Reduction.G₀ L S₀)).pCoreIn 2); rw [inf_comm]; exact hd)
    (by change C ⊔ (stabilizer Γ beta ⊓ stabilizer Γ a : Subgroup (Reduction.G₀ L S₀)).pCoreIn 2 = stabilizer Γ beta ⊓ stabilizer Γ a; rw [inf_comm (stabilizer Γ beta) (stabilizer Γ a)]; exact hCE)
  change S ⊔ (C ⊓ graphLocalGroup Γ a) = graphLocalGroup Γ a ⊓ E at hpa
  change (stabilizer Γ beta ⊓ stabilizer Γ a : Subgroup (Reduction.G₀ L S₀)).pCoreIn 2 ⊔
    (C ⊓ graphLocalGroup Γ beta) = graphLocalGroup Γ beta ⊓ (stabilizer Γ beta ⊓ stabilizer Γ a) at hpb
  have he : E = (S ⊔ (C ⊓ graphLocalGroup Γ a)) ⊔
      (S ⊔ (C ⊓ graphLocalGroup Γ beta)) := by
    rw [hpa]
    have hpb' : S ⊔ (C ⊓ graphLocalGroup Γ beta) = graphLocalGroup Γ beta ⊓ E := by
      simpa only [inf_comm (stabilizer Γ beta)] using hpb
    rw [hpb']
    exact (reduced_edge_local_product h hab).trans (congrArg₂ (· ⊔ ·) (inf_comm _ _) (inf_comm _ _))
  exact ⟨C,hCA,hd,hCE,hodd,reduced_edge_odd_commutative h hab C hC hodd,ea',eb',
    complement_eq_sup_of_local_products C S E _ _ hC hd hES inf_le_left inf_le_left he⟩


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.PathCartan
public import Theory.GroupAction.CoprimePointStabilizer
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Extending the same Cartan along the critical path

Hall conjugacy inside the old path stabilizer extends a prescribed full
edge complement by one vertex. Edge conjugacy and cardinality then show
that this same odd complement is full at every edge it fixes. On the
critical three-edge path this constructs both additional endpoints and
marks their intrinsic tori by the original fields, without replacing the
Cartan or either previously constructed natural section.

The literal F.1.11 application is `DistanceThreeExtendedCartan`.
Source: DGS, *Groups and Graphs* (1985), 9.10, printed p.147.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G]
private theorem complement_hall [Finite G] (T : Sylow 2 G)
    (C : Subgroup G) (hc : (T : Subgroup G).IsComplement' C) :
    IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} C := by
  refine ⟨?_,?_⟩
  · intro p hp he
    change p.val = 2 at he
    rw [←hc.symm.index_eq_card,he] at hp
    exact T.not_dvd_index hp
  · intro p hp hne
    rw [hc.index_eq_card] at hp
    obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn] at hp
    exact hne (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two hp)

private theorem complement_conjugate_into [Finite G]
    (T : Sylow 2 G) (hsolv : Group.IsSolvable G)
    (C H D : Subgroup G) (hCH : C ≤ H) (hDH : D ≤ H)
    (hc : (T : Subgroup G).IsComplement' C)
    (hd : (T : Subgroup G).IsComplement' D) :
    ∃ g ∈ H, C.map (MulAut.conj g).toMonoidHom ≤ D := by
  let := hsolv
  have hHallC := (complement_hall T C hc).subgroupOf hCH
  have hHallD := (complement_hall T D hd).subgroupOf hDH
  obtain ⟨g,hg⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable
    (inferInstance : Group.IsSolvable H) hHallC hHallD
  refine ⟨g,g.property,?_⟩
  rintro z ⟨c,hcC,rfl⟩
  have hh : (MulAut.conj g) (⟨c,hCH hcC⟩ : H) ∈ D.subgroupOf H := by
    rw [hg]
    exact mem_map_of_mem _ hcC
  exact hh

private theorem edge_complement_conjugate_into
    (E H C D : Subgroup G) [Finite E]
    (hs : ∃ T : Sylow 2 E, (T : Subgroup E) = pCore 2 E)
    (hsolv : Group.IsSolvable E) (hHE : H ≤ E)
    (hCH : C ≤ H) (hDH : D ≤ H)
    (hc : Disjoint C (E.pCoreIn 2)) (hd : Disjoint D (E.pCoreIn 2))
    (hcgen : C ⊔ E.pCoreIn 2 = E) (hdgen : D ⊔ E.pCoreIn 2 = E) :
    ∃ g ∈ H, C.map (MulAut.conj g).toMonoidHom ≤ D := by
  obtain ⟨T,hT⟩ := hs
  have comp (A : Subgroup G) (hAE : A ≤ E)
      (hdis : Disjoint A (E.pCoreIn 2)) (hgen : A ⊔ E.pCoreIn 2 = E) :
      (T : Subgroup E).IsComplement' (A.subgroupOf E) := by
    rw [hT]
    have hdis' : Disjoint (pCore 2 E) (A.subgroupOf E) := by
      apply disjoint_def.mpr
      intro z hz hzA
      apply Subtype.ext
      exact disjoint_def.mp hdis hzA (mem_map_of_mem E.subtype hz)
    have hgen' : pCore 2 E ⊔ A.subgroupOf E = ⊤ := by
      apply Subgroup.map_injective E.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAE,←MonoidHom.range_eq_map,range_subtype]
      exact (sup_comm _ _).trans hgen
    apply isComplement'_of_disjoint_and_mul_eq_univ hdis'
    rw [←coe_mul_of_right_le_normalizer_left _ _ le_normalizer_of_normal,hgen']
    rfl
  obtain ⟨g,hg,hgD⟩ := complement_conjugate_into T hsolv
    (C.subgroupOf E) (H.subgroupOf E) (D.subgroupOf E)
    (comap_mono hCH) (comap_mono hDH)
    (comp C (hCH.trans hHE) hc hcgen) (comp D (hDH.trans hHE) hd hdgen)
  refine ⟨g,hg,?_⟩
  rintro z ⟨c,hcC,rfl⟩
  exact hgD (mem_map_of_mem (MulAut.conj g).toMonoidHom
    (show (⟨c,hCH.trans hHE hcC⟩ : E) ∈ C.subgroupOf E from hcC))
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Extend a regular path fixed by a prescribed full edge complement.
Hall conjugacy takes place inside the old path stabilizer. -/
theorem path_cartan_fixed_extension
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v a b : Vertex (family P)} {n : ℕ}
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    (ht : RootPathTransitive (graph (family P)) G v (n+2))
    (hab : (graph (family P)).Adj a b) (ha : a ∈ p.vertices) (hb : b ∈ p.vertices)
    (C : Subgroup G) (hCp : C ≤ pathStabilizer (family P) p)
    (hCdis : Disjoint C ((stabilizer (family P) a ⊓ stabilizer (family P) b : Subgroup G).pCoreIn 2))
    (hCgen : C ⊔ (stabilizer (family P) a ⊓ stabilizer (family P) b : Subgroup G).pCoreIn 2 =
      stabilizer (family P) a ⊓ stabilizer (family P) b)
    (hCa : IsMulCommutative C)
    {z : Vertex (family P)} (hz : (graph (family P)).Adj p.endpoint z)
    (hzne : z ≠ p.penultimate) :
    ∃ y : Vertex (family P), (graph (family P)).Adj p.endpoint y ∧
      y ≠ p.penultimate ∧ C ≤ stabilizer (family P) y := by
  let := finite_endpoints h
  let Γ := family P
  let E := stabilizer Γ a ⊓ stabilizer Γ b
  let S := E.pCoreIn 2
  let H := pathStabilizer Γ p
  let r := p.snoc hz
  have hr : r.Nonbacktracking := (nonbacktracking_snoc_iff p hz).mpr ⟨hp,hzne⟩
  have hH : H ≤ E := pathStabilizer_le_edge Γ p ha hb
  have hrH : pathStabilizer Γ r ≤ H := by
    intro g hg x hx
    exact hg x (by rw [vertices_snoc,List.mem_append]; exact Or.inl hx)
  have hra : a ∈ r.vertices := by rw [vertices_snoc,List.mem_append]; exact Or.inl ha
  have hrb : b ∈ r.vertices := by rw [vertices_snoc,List.mem_append]; exact Or.inl hb
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer Γ a from inf_le_left))
    (inclusion_injective _)
  have hES : E ≤ normalizer (S : Set G) := E.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  have hgen : pathStabilizer Γ r ⊔ S = E := by
    apply SetLike.coe_injective
    rw [coe_mul_of_left_le_normalizer_right _ _ ((hrH.trans hH).trans hES)]
    exact (source_path_edge_product h hB (source_rankOne_branching h) ht r hr hab hra hrb).symm
  obtain ⟨D,hDr,hDdis,hDgen,_⟩ := exists_complement_le_of_core_supplement 2 E
    (pathStabilizer Γ r) (hrH.trans hH) (source_edge_core_sylow h hB hab) hgen
  let : Finite S := Finite.of_injective (inclusion (show S ≤ E from map_subtype_le _)) (inclusion_injective _)
  have hsolv : Group.IsSolvable E := by
    let := hCa
    let : Group.IsSolvable S := @IsNilpotent.to_isSolvable _ _ (isPGroup_pCoreIn 2 E).isNilpotent
    have hh := Group.isSolvable_sup_of_normalizes S C ((hCp.trans hH).trans hES)
    rwa [sup_comm,hCgen] at hh
  obtain ⟨g,hg,hgD⟩ := edge_complement_conjugate_into E H C D
    (source_edge_core_sylow h hB hab) hsolv hH hCp (hDr.trans hrH)
    hCdis hDdis hCgen hDgen
  have hgEnd : g • p.endpoint = p.endpoint := hg _ (by
    simpa only [support_toWalk] using p.toWalk.end_mem_support)
  have hgPen : g • p.penultimate = p.penultimate := hg _ (by
    have hh := (p.take n (Nat.le_succ n)).toWalk.end_mem_support
    rw [support_toWalk,endpoint_take_penultimate,vertices_take] at hh
    exact List.mem_of_mem_take hh)
  refine ⟨g⁻¹ • z,?_,?_,?_⟩
  · have hh := (Subgroup.CosetGeometry.translationGraphIso Γ g⁻¹).map_adj_iff.mpr hz
    change (graph Γ).Adj (g⁻¹ • p.endpoint) (g⁻¹ • z) at hh
    rwa [inv_smul_eq_iff.mpr hgEnd.symm] at hh
  · intro he
    apply hzne
    have hh := congrArg (g • ·) he
    simpa only [smul_inv_smul,hgPen] using hh
  · intro c hc
    have hh := hDr (hgD (mem_map_of_mem (MulAut.conj g).toMonoidHom hc)) z (by
      rw [vertices_snoc,List.mem_append,List.mem_singleton]; exact Or.inr rfl)
    change (g*c*g⁻¹) • z = z at hh
    have he := congrArg (g⁻¹ • ·) hh
    change c • (g⁻¹ • z) = g⁻¹ • z
    simpa only [mul_smul,inv_smul_smul] using he

/-- An odd full complement remains a full complement in every edge it fixes. -/
theorem path_cartan_complement_at_edge
    (h : LocallyRankOneTriple P B)
    {a b v w : Vertex (family P)}
    (hab : (graph (family P)).Adj a b) (hvw : (graph (family P)).Adj v w)
    (C : Subgroup G)
    (hCE : C ≤ stabilizer (family P) a ⊓ stabilizer (family P) b)
    (hCF : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer (family P) a ⊓ stabilizer (family P) b : Subgroup G).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) a ⊓ stabilizer (family P) b : Subgroup G).pCoreIn 2 =
      stabilizer (family P) a ⊓ stabilizer (family P) b) :
    Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2) ∧
      C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G).pCoreIn 2 =
        stabilizer (family P) v ⊓ stabilizer (family P) w := by
  let := finite_endpoints h
  let Γ := family P
  let E := stabilizer Γ a ⊓ stabilizer Γ b
  let F := stabilizer Γ v ⊓ stabilizer Γ w
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer Γ a from inf_le_left)) (inclusion_injective _)
  let : Finite F := Finite.of_injective (inclusion (show F ≤ stabilizer Γ v from inf_le_left)) (inclusion_injective _)
  let : Finite C := Finite.of_injective (inclusion hCE) (inclusion_injective _)
  let : Finite (F.pCoreIn 2) := Finite.of_injective (inclusion (show F.pCoreIn 2 ≤ F from map_subtype_le _)) (inclusion_injective _)
  have norm (X : Subgroup G) : X ≤ normalizer (X.pCoreIn 2 : Set G) :=
    X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hdF : Disjoint C (F.pCoreIn 2) := by
    obtain ⟨n,hn⟩ := (isPGroup_pCoreIn 2 F).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact ho.coprime_two_right.pow_right n
  have hcard (x y : Vertex Γ) (hxy : (graph Γ).Adj x y) :
      Nat.card ((stabilizer Γ x ⊓ stabilizer Γ y : Subgroup G).pCoreIn 2) =
        Nat.card ((Γ false ⊓ Γ true : Subgroup G).pCoreIn 2) := by
    obtain ⟨g,he⟩ := edgeStabilizer_map_base Γ hxy
    rw [he,Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (MulAut.conj g).injective]
    exact card_map_of_injective (MulAut.conj g).injective
  have hc : Nat.card (F.pCoreIn 2) = Nat.card (E.pCoreIn 2) :=
    (hcard v w hvw).trans (hcard a b hab).symm
  refine ⟨hdF,eq_of_le_of_card_ge (sup_le hCF (map_subtype_le _)) ?_⟩
  have hprod (X : Subgroup G) (hCX : C ≤ X) (hdis : Disjoint C (X.pCoreIn 2)) :
      Nat.card (C ⊔ X.pCoreIn 2 : Subgroup G) = Nat.card (X.pCoreIn 2) * Nat.card C := by
    rw [sup_comm]
    exact card_sup_eq_mul_of_normalizes_of_disjoint _ _ (hCX.trans (norm X)) hdis.symm
  have hE := hprod E hCE hd
  rw [hg] at hE
  change Nat.card F ≤ Nat.card (C ⊔ F.pCoreIn 2 : Subgroup G)
  rw [hprod F hCF hdF,hc,←hE]
  exact (card_edgeStabilizer Γ hvw).trans (card_edgeStabilizer Γ hab).symm |>.le

/-- The same full Cartan fixes an extension at each end of the critical
three-edge path. All four endpoint tori use the original two fields. -/
theorem distance_three_cartan_extensions
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {a b x d : Vertex (family P)}
    (hab : (graph (family P)).Adj a b) (hbx : (graph (family P)).Adj b x)
    (hxd : (graph (family P)).Adj x d) (hgeo : (graph (family P)).dist a d = 3)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (ea : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,K))
    (eb : (graphLocalGroup (family P) b ⧸ pCore 2 (graphLocalGroup (family P) b)) ≃* SL(2,F))
    (C : Subgroup G)
    (hfix : C ≤ stabilizer (family P) a ⊓ stabilizer (family P) b ⊓
      stabilizer (family P) x ⊓ stabilizer (family P) d)
    (hd : Disjoint C ((stabilizer (family P) a ⊓ stabilizer (family P) b : Subgroup G).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) a ⊓ stabilizer (family P) b : Subgroup G).pCoreIn 2 =
      stabilizer (family P) a ⊓ stabilizer (family P) b)
    (ho : Odd (Nat.card C)) (hCa : IsMulCommutative C) :
    ∃ l r : Vertex (family P), (graph (family P)).Adj a l ∧ l ≠ b ∧
      (graph (family P)).Adj d r ∧ r ≠ x ∧
      C ≤ stabilizer (family P) l ⊓ stabilizer (family P) r ∧
      Nonempty ((C ⊓ graphLocalGroup (family P) l : Subgroup G) ≃* Fˣ) ∧
      Nonempty ((C ⊓ graphLocalGroup (family P) d : Subgroup G) ≃* Fˣ) ∧
      Nonempty ((C ⊓ graphLocalGroup (family P) r : Subgroup G) ≃* Kˣ) := by
  let := finite_endpoints h
  let Γ := family P
  let p : BasedWalk (graph Γ) 3 a := ⟨⟨b,hab⟩,⟨⟨x,hbx⟩,⟨⟨d,hxd⟩,PUnit.unit⟩⟩⟩
  let q : BasedWalk (graph Γ) 3 d := ⟨⟨x,hxd.symm⟩,⟨⟨b,hbx.symm⟩,⟨⟨a,hab.symm⟩,PUnit.unit⟩⟩⟩
  have hp : p.Nonbacktracking := nonbacktracking_of_geodesic p hgeo
  have hq : q.Nonbacktracking := nonbacktracking_of_geodesic q (by change (graph Γ).dist d a = 3; rw [SimpleGraph.dist_comm]; exact hgeo)
  have hCp : C ≤ pathStabilizer Γ p := by
    intro c hc z hz
    change z ∈ [a,b,x,d] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact (hfix hc).1.1.1
    · exact (hfix hc).1.1.2
    · exact (hfix hc).1.2
    · exact (hfix hc).2
  have hCq : C ≤ pathStabilizer Γ q := by
    intro c hc z hz
    change z ∈ [d,x,b,a] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact (hfix hc).2
    · exact (hfix hc).1.2
    · exact (hfix hc).1.1.2
    · exact (hfix hc).1.1.1
  have hdeg : HasTwoNeighbors (graph Γ) := by
    intro v w
    apply Set.exists_ne_of_one_lt_ncard (s := (graph Γ).neighborSet v) ?_ w
    rw [←Nat.card_coe_set_eq,card_neighbors_of_indices Γ
      (fun i => ((Γ (!i)).subgroupOf (Γ i)).index) (fun _ => rfl)]
    exact lt_of_lt_of_le (by decide) (source_valence_ge_three h hS v.type)
  have ht := adjacent_linear_short_path_transitive h hB hS hob hab ea eb
  obtain ⟨z,hz,hzne⟩ := hdeg q.endpoint q.penultimate
  obtain ⟨l,hal,hlb,hCl⟩ := path_cartan_fixed_extension h hB q hq (ht d 4 le_rfl)
    hab (by simp [q,BasedWalk.vertices]) (by simp [q,BasedWalk.vertices]) C hCq hd hg hCa hz hzne
  obtain ⟨z,hz,hzne⟩ := hdeg p.endpoint p.penultimate
  obtain ⟨r,hdr,hrx,hCr⟩ := path_cartan_fixed_extension h hB p hp (ht a 4 le_rfl)
    hab (by exact List.Mem.head _) (by exact List.Mem.tail _ (List.Mem.head _)) C hCp hd hg hCa hz hzne
  change (graph Γ).Adj a l at hal
  change l ≠ b at hlb
  change (graph Γ).Adj d r at hdr
  change r ≠ x at hrx
  have hCE : C ≤ stabilizer Γ a ⊓ stabilizer Γ b := hfix.trans (inf_le_left.trans inf_le_left)
  have hCla : C ≤ stabilizer Γ l ⊓ stabilizer Γ a := le_inf hCl (hCE.trans inf_le_left)
  have hCdr : C ≤ stabilizer Γ d ⊓ stabilizer Γ r := le_inf (hfix.trans inf_le_right) hCr
  obtain ⟨hdl,hgl⟩ := path_cartan_complement_at_edge h hab hal.symm C hCE hCla ho hd hg
  obtain ⟨hdd,hgd⟩ := path_cartan_complement_at_edge h hab hdr C hCE hCdr ho hd hg
  have heq {i j k : Bool} (hi : i ≠ k) (hj : j ≠ k) : i = j := by
    cases i <;> cases j <;> cases k <;> simp_all
  have hbl : b.type = l.type := heq hab.1.symm hal.1.symm
  have hbd : b.type = d.type := heq hbx.1 hxd.1.symm
  have har : a.type = r.type := heq (hbd ▸ hab.1) hdr.1.symm
  obtain ⟨gl,hglv⟩ := (same_orbit_iff Γ b l).mpr hbl
  obtain ⟨_,el,_,_,_⟩ := local_quotient_parameter_transport h gl hglv
  obtain ⟨gd,hgdv⟩ := (same_orbit_iff Γ b d).mpr hbd
  obtain ⟨_,ed,_,_,_⟩ := local_quotient_parameter_transport h gd hgdv
  obtain ⟨gr,hgrv⟩ := (same_orbit_iff Γ a r).mpr har
  obtain ⟨_,er,_,_,_⟩ := local_quotient_parameter_transport h gr hgrv
  refine ⟨l,r,hal,hlb,hdr,hrx,le_inf hCl hCr,
    (edge_complement_local_torus h hB hS hal.symm (el.symm.trans eb) C hCla hdl hgl).1,
    (edge_complement_local_torus h hB hS hdr (ed.symm.trans eb) C hCdr hdd hgd).1,?_⟩
  exact (edge_complement_local_torus h hB hS hdr.symm (er.symm.trans ea) C
    (hCdr.trans (inf_comm _ _).le) (by simpa only [inf_comm] using hdd)
    (by simpa only [inf_comm] using hgd)).1
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

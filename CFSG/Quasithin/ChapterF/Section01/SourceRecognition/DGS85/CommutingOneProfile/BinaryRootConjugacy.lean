module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.BinaryAlphaCartanReflection
public import Theory.GroupTheory.WeakBNPair.RegularTree.CubicRootReflection

/-!
# The binary reflection choice for prescribed four-path roots

The binary beta endpoint has three neighbors. Its actual nontrivial
four-path radical therefore has order two: evaluation on the two exits is
injective because five-path stabilizers are odd. The full Cartan normalizes
and hence centralizes this radical. Conjugating its prescribed involution
by the already constructed Cartan-centralizing beta mover gives the required
reflection, in the same original local-actor conjugacy class.

For either endpoint, the original full-Borel factorization and five-path
transitivity construct an involution in every prescribed Cartan-fixed
four-path radical. Odd extensions keep it outside the full local permutation
kernel. Combining the alpha and beta constructions supplies DGS (14.2) for
both original binary endpoints, including the full Cartan/kernel clause and
the literal universal-tree map. No root involution, catalogue, reflection or
path-regularity premise is supplied. The prescribed path itself retains the
source's path, length, marked-edge and Cartan-fixation hypotheses.

Binary and unitary exchange, remaining unitary inputs and catalogue exclusions,
and the full marked (11.7)--(11.8) assembly remain separate obligations.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.7), pp.174--175, and (14.1)--(14.2), pp.210--211.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Theory.GroupTheory.WeakBNPair.RegularTree
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
variable {G : Type*} [Group G]
section Original
open Reduction NoncommutingProfile CommutingNontrivial
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
local notation "α" => base F false
local notation "β" => base F true
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S)
      (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S)=1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆=⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf
        (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))
    (hbinary : ClassicalGroup.IsPSL
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype ⧸
      pCore 2 ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype)) 2 2)
include h hc hb hcomm helem hbinary


omit hcomm helem in
/-- The literal binary beta marking gives a cubic universal-tree endpoint. -/
theorem original_elementary_binary_beta_tree_neighbor_card :
    Nat.card ((sourceGraph A).neighborSet (base T true))=3 := by
  let H := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let j := (graphLocalGroup F β).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let e := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  have mb : ClassicalGroup.IsPSL (d.localGroup β ⧸ pCore 2 (d.localGroup β)) 2 2 :=
    hbinary.of_mulEquiv e
  obtain ⟨k,fk,fink,hk,⟨eb⟩⟩ := mb
  let _ := fk
  let _ := fink
  let _ : Fintype k := Fintype.ofFinite k
  let _ : CharP k 2 := charP_of_card_eq_prime_pow
    (show Fintype.card k=2^1 by simpa only [Nat.card_eq_fintype_card,pow_one] using hk)
  let eSL : (d.localGroup β ⧸ pCore 2 (d.localGroup β)) ≃* SL(2,k) :=
    eb.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have M : IsRankOneModel (d.localGroup β ⧸ pCore 2 (d.localGroup β)) :=
    .linear 1 (by decide) ⟨k,fk,fink,hk,⟨eb⟩⟩
  have hcard : Nat.card ((graph F).neighborSet β)=3 := by
    have hh := source_linear_neighbor_card H (reduced_borel_core_sylow h) d
      (source_critical_one_adjacent hc hb) M eSL
    change Nat.card ((graph F).neighborSet β)=Nat.card k+1 at hh
    rw [hk] at hh
    exact hh
  let cov := bOne_tree_cover h
  have he := Nat.card_congr (Equiv.ofBijective _ (cov.neighbor_bijective (base T true)))
  change Nat.card ((sourceGraph A).neighborSet (base T true)) =
    Nat.card ((graph F).neighborSet (cov.vertex (base T true))) at he
  rw [cov.vertex_base,hcard] at he
  exact he

/-- Any specified involution in a Cartan-fixed four-path root has a
beta-local conjugate centralizing the full Cartan and moving the marked neighbor. -/
theorem original_elementary_binary_beta_prescribed_root_reflection
    (c : CompatibleCartans L (reducedSylow L S))
    {d : SourceVertex A} (p : (sourceGraph A).Walk d (base T true))
    (hp : p.IsPath) (hl : p.length=4) (hpPrev : p.penultimate=base T false)
    (hCp : cartan c≤pathFixer (X := (A).Universal) p)
    (x : (A).Universal) (hx : x∈pathRoot (X := (A).Universal) p) (hxo : orderOf x=2) :
    ∃ t : (A).Universal, t • base T true=base T true ∧
      t • base T false≠base T false ∧ t*t=1 ∧
      t∈centralizer (cartan c : Set (A).Universal) ∧
      ∃ g∈T true, (bOne_tree_map h) g∈graphLocalGroup F β ∧ g*x*g⁻¹=t := by
  let φ := bOne_tree_map h
  obtain ⟨t,htfix,htmove,htsq,htC,v,hv,_,htZ⟩ :=
    original_elementary_binary_beta_tree_reflection h hc hb hcomm helem hbinary c
  have htree := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hpath := original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem
  have hpnil : ¬p.Nil := by
    intro hn
    have hh := hn.length_eq_zero
    omega
  have hodd {z : SourceVertex A} (hz : (sourceGraph A).Adj (base T true) z)
      (hzprev : z≠p.penultimate) :
      Odd (Nat.card (pathFixer (X := (A).Universal) (p.concat hz))) := by
    have hnew : z∉p.support := fun hzmem =>
      hzprev (htree.eq_penultimate_of_adj_end hp hz hzmem)
    exact hpath.2 (p.concat hz) (hp.concat hnew hz) (by rw [Walk.length_concat,hl])
  have hx1 : x≠1 := by intro he; simp [he] at hxo
  have hx2 : x*x=1 := by simpa only [hxo,pow_two] using pow_orderOf_eq_one x
  obtain ⟨hfix,hmove,hsq,hcentral⟩ := cubic_pathRoot_conjugate_reflection
    (source_action A) p hpnil (original_elementary_binary_beta_tree_neighbor_card h hc hb hbinary)
    (cartan c) hCp hodd x hx hx1 hx2 t htfix (hpPrev.symm ▸ htmove) htsq htC
  have htT : t∈T true := by
    rw [←Subgroup.CosetGeometry.stabilizer_base T true]
    exact htfix
  have hZ : Z F v≤stabilizer F β :=
    ((source_Z_Q_U (reduced_triple h) v).1.trans (map_subtype_le _)).trans
      ((source_Z_Q_U (reduced_triple h) v).2.trans
        ((ballKernel_one_le_edge F hv.symm).trans inf_le_right))
  have htJ : φ t∈graphLocalGroup F β :=
    pGroup_le_sylowGenerated _ (Z F v) hZ ((isPGroup_pCoreIn 2 (stabilizer F v)).to_le
      ((source_Z_Q_U (reduced_triple h) v).1.trans (map_subtype_le _))) htZ
  exact ⟨t*x*t⁻¹,hfix,hpPrev ▸ hmove,hsq,hcentral,t,htT,htJ,rfl⟩

/-- DGS (14.2)'s beta choice on an actual original four-path, retaining
its full Cartan centralization and conjugator in the original local actor. -/
theorem original_elementary_binary_beta_four_path_reflection
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ d, ∃ p : (sourceGraph A).Walk d (base T true),
      p.IsPath ∧ p.length=4 ∧ p.penultimate=base T false ∧
      cartan c≤pathFixer (X := (A).Universal) p ∧
      ∃ x∈pathRoot (X := (A).Universal) p, orderOf x=2 ∧
      ∃ t : (A).Universal, t • base T true=base T true ∧
        t • base T false≠base T false ∧ t*t=1 ∧
        t∈centralizer (cartan c : Set (A).Universal) ∧
        ∃ g∈T true, (bOne_tree_map h) g∈graphLocalGroup F β ∧ g*x*g⁻¹=t := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_binary_tree_reflections h hc hb hcomm helem hbinary c
  have hpath := original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem
  have hthick := original_source_tree_thickness h t
  let p := reflectionPath c t htfix htmove htnorm 4 (by decide) true
  obtain ⟨x,hx,hxo,_⟩ := pathRoots_exists_involution_outside_localKernel
    h c 4 (by decide) t htfix htmove htsq htnorm hpath.1 hthick hpath.2 true
  change x∈pathRoot (X := (A).Universal) p.walk at hx
  obtain ⟨u,hu,hum,hu2,huC,g,hg,hgJ,hgxu⟩ :=
    original_elementary_binary_beta_prescribed_root_reflection h hc hb hcomm helem hbinary
      c p.walk p.isPath p.length_eq p.previous p.fixed x hx hxo
  exact ⟨p.start,p.walk,p.isPath,p.length_eq,p.previous,p.fixed,
    x,hx,hxo,u,hu,hum,hu2,huC,g,hg,hgJ,hgxu⟩


/-- Every prescribed Cartan-fixed elementary four-path contains an
involution surviving the full local permutation action. -/
theorem original_elementary_binary_prescribed_path_involution
    (c : CompatibleCartans L (reducedSylow L S)) (i : Bool)
    {d : SourceVertex A} (p : (sourceGraph A).Walk d (base T i))
    (hp : p.IsPath) (hl : p.length=4) (hpPrev : p.penultimate=base T (!i))
    (hCp : cartan c≤pathFixer (X := (A).Universal) p) :
    ∃ x∈pathRoot (X := (A).Universal) p, orderOf x=2 ∧
      x∉ballKernel T (base T i) 1 := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_binary_tree_reflections h hc hb hcomm helem hbinary c
  have hpath := original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem
  have htree := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hpnil : ¬p.Nil := by intro hn; have hh := hn.length_eq_zero; omega
  have hexit : (sourceGraph A).Adj (base T i) (t i • base T (!i)) := by
    have hadj : (sourceGraph A).Adj (base T i) (base T (!i)) :=
      ⟨by change i≠!i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
    simpa only [htfix i] using source_action A (t i) hadj
  have hexitprev : t i • base T (!i)≠p.penultimate := hpPrev.symm ▸ htmove i
  have hfixexit : ∀ k∈cartan c, k • (t i • base T (!i))=t i • base T (!i) := by
    intro k hk
    apply reflectionApartment_fixed c t htnorm k hk
    exact cartanApartment_preserves A (reflectionGroup c t) (reflectionGroup_mem c t i)
      (cartanApartment_base A (reflectionGroup c t) (!i))
  obtain ⟨z,hz,hzprev,hzne⟩ := original_source_tree_thickness h t i
  obtain ⟨x,hx,hxz⟩ := pathRoot_transitive_exits htree p hp
    (by rw [hl]; exact hpath.1) (cartan c) hexit hexitprev hfixexit
    (pathFixer_factorization c h p hpPrev hCp) z hz (hpPrev.symm ▸ hzprev)
  let v : pathRoot (X := (A).Universal) p := ⟨x,hx⟩
  have hv : v≠1 := by
    intro he
    have he' : x=1 := congrArg Subtype.val he
    rw [he',one_smul] at hxz
    exact hzne hxz.symm
  have htwo := pathRoot_isTwo (X := (A).Universal) p
  obtain ⟨k,hk⟩ := htwo.exists_orderOf_eq_pow v
  let w : pathRoot (X := (A).Universal) p := v^(orderOf v/2)
  have hw : orderOf w=2 := orderOf_pow_orderOf_div
    (by rw [hk]; exact pow_ne_zero _ (by decide)) (htwo.dvd_orderOf hv)
  have hwo : orderOf (w : (A).Universal)=2 := (Subgroup.orderOf_coe w).trans hw
  refine ⟨w,w.property,hwo,?_⟩
  intro hwU
  have hwfix : (w : (A).Universal) • (t i • base T (!i))=t i • base T (!i) :=
    hwU _ ((mem_ball_one T _ _).mpr (Or.inl hexit))
  have hnew : t i • base T (!i)∉p.support := fun he =>
    hexitprev (htree.eq_penultimate_of_adj_end hp hexit he)
  have hodd := hpath.2 (p.concat hexit) (hp.concat hnew hexit)
    (by rw [Walk.length_concat,hl])
  have hmem : (w : (A).Universal)∈pathRoot (X := (A).Universal) p ⊓
      MulAction.stabilizer (A).Universal (t i • base T (!i)) := ⟨w.property,hwfix⟩
  rw [pathRoot_inf_stabilizer_eq_bot p hexit hodd] at hmem
  have hoone := orderOf_eq_one_iff.mpr hmem
  omega

/-- DGS (14.2) for either original binary endpoint and a prescribed
Cartan-fixed four-path: construct the root involution, its local conjugate,
and centralization of the full Cartan/local-kernel intersection. -/
theorem original_elementary_binary_prescribed_four_path_reflection
    (c : CompatibleCartans L (reducedSylow L S)) (i : Bool)
    {d : SourceVertex A} (p : (sourceGraph A).Walk d (base T i))
    (hp : p.IsPath) (hl : p.length=4) (hpPrev : p.penultimate=base T (!i))
    (hCp : cartan c≤pathFixer (X := (A).Universal) p) :
    ∃ x∈pathRoot (X := (A).Universal) p, orderOf x=2 ∧
      ∃ t : (A).Universal, t • base T i=base T i ∧
        t • base T (!i)≠base T (!i) ∧ t*t=1 ∧
        t∈normalizer (cartan c : Set (A).Universal) ∧
        (∀ k∈cartan c ⊓ (U F (base F i)).comap (bOne_tree_map h), Commute t k) ∧
        ∃ g∈T i, (bOne_tree_map h) g∈graphLocalGroup F (base F i) ∧ g*x*g⁻¹=t := by
  obtain ⟨x,hx,hxo,hxU⟩ := original_elementary_binary_prescribed_path_involution
    h hc hb hcomm helem hbinary c i p hp hl hpPrev hCp
  refine ⟨x,hx,hxo,?_⟩
  cases i
  · obtain ⟨t,ht,hm,hs,hn,g,hg,hgJ,hgxt⟩ :=
      original_elementary_binary_alpha_prescribed_root_reflection h hc hb hcomm helem hbinary
        c p hpPrev x hx (by simpa only [hxo,pow_two] using pow_orderOf_eq_one x) hxU
    refine ⟨t,ht,hm,hs,hn,?_,g,hg,hgJ,hgxt⟩
    intro k hk
    have he : k=1 := (original_elementary_binary_alpha_tree_cartan_kernel_eq_bot
      h hc hb hcomm helem hbinary c).le hk
    rw [he]
    exact Commute.one_right t
  · obtain ⟨t,ht,hm,hs,hn,g,hg,hgJ,hgxt⟩ :=
      original_elementary_binary_beta_prescribed_root_reflection h hc hb hcomm helem hbinary
        c p hp hl hpPrev hCp x hx hxo
    refine ⟨t,ht,hm,hs,Subgroup.centralizer_le_normalizer _ hn,?_,g,hg,hgJ,hgxt⟩
    intro k hk
    exact (mem_centralizer_iff.mp hn k hk.1).symm

end Original
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

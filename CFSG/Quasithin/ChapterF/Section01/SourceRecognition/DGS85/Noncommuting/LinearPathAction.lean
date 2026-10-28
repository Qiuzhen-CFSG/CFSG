module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.PathComplement
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear.MatrixBorel
public import Theory.GroupAction.MatchedPointOrbit
public import Theory.SpecificGroups.SL2.SylowCharacteristicImage

/-!
# Linear local actions on path continuations

For a local SL₂ quotient, an edge supplement whose two-part escapes the
vertex core has the full root-group image. The affine action of that root
group is transitive on all continuations except the preceding vertex.
Transport through the literal quotient and neighbor actions then makes a
path right regular whenever its stabilizer contains an escaping two-group.

Source: DGS, *Groups and Graphs* (1985), (5.1) and the linear case of
(7.5)(5), printed p.130.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
open BenderSuzuki.Converse
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {k : Type*} [Field k] [CharP k 2]

private theorem unip_transitive (a b : P1 k) (ha : a ≠ pInf k) (hb : b ≠ pInf k) :
    ∃ u ∈ Unip k, u • a = b := by
  have hzero : pInf k ≠ pZero k := by
    intro he
    apply weyl_notMem_Borel (F := k)
    change weyl k • pInf k = pInf k
    exact weyl_smul_pInf.trans he.symm
  have hreach (c : P1 k) (hc : c ≠ pInf k) : ∃ u ∈ Unip k, u • pZero k = c := by
    obtain ⟨g, hgi, hgc⟩ := MulAction.is_two_pretransitive_iff.mp
      (inferInstance : MulAction.IsMultiplyPretransitive (SL2 k) (P1 k) 2)
      hzero hc.symm
    have hg : g ∈ (Unip k : Set (SL2 k)) * (Torus k : Set (SL2 k)) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _
        (Torus_le_Borel.trans (CFSG.Quasithin.ChapterF.Source.Linear.unip_normalizer.ge)),
        Unip_sup_Torus]
      exact hgi
    obtain ⟨u, hu, t, ht, rfl⟩ := hg
    refine ⟨u, hu, ?_⟩
    rwa [mul_smul, (show t • pZero k = pZero k from ht.2)] at hgc
  obtain ⟨u, hu, hua⟩ := hreach a ha
  obtain ⟨v, hv, hvb⟩ := hreach b hb
  refine ⟨v * u⁻¹, (Unip k).mul_mem hv ((Unip k).inv_mem hu), ?_⟩
  rw [← hua, mul_smul, inv_smul_smul, hvb]


variable [Finite k]

private theorem sylow_affine_transitive (T : Sylow 2 (SL2 k)) :
    ∃ p : P1 k, normalizer (T : Set (SL2 k)) = MulAction.stabilizer (SL2 k) p ∧
      ∀ a b : P1 k, a ≠ p → b ≠ p → ∃ t ∈ (T : Subgroup (SL2 k)), t • a = b := by
  let P := Matrix.SpecialLinearGroup.upperUnipotentSylow k 2
  have hP : (P : Subgroup (SL2 k)) = Unip k :=
    CFSG.Quasithin.ChapterF.Source.Linear.unip_eq_upper.symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL2 k) P T
  have hmap : (P : Subgroup (SL2 k)).map (MulAut.conj g).toMonoidHom = T := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g • pInf k, ?_, ?_⟩
  · have he := Subgroup.map_equiv_normalizer_eq (P : Subgroup (SL2 k)) (MulAut.conj g)
    rw [hmap, hP, CFSG.Quasithin.ChapterF.Source.Linear.unip_normalizer] at he
    simp only [Sylow.coe_coe] at he
    rw [← he, Borel, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  · intro a b ha hb
    have ha' : g⁻¹ • a ≠ pInf k := by
      intro he
      exact ha (by rw [← he, smul_inv_smul])
    have hb' : g⁻¹ • b ≠ pInf k := by
      intro he
      exact hb (by rw [← he, smul_inv_smul])
    obtain ⟨u, hu, he⟩ := unip_transitive (g⁻¹ • a) (g⁻¹ • b) ha' hb'
    refine ⟨g * u * g⁻¹, ?_, ?_⟩
    · rw [← hmap]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hP ▸ hu)
    · rw [mul_smul, mul_smul, he, smul_inv_smul]


variable {G : Type*} [Group G]

private theorem linear_borel_supplement_image
    {H : Type*} [Group H] [Finite H]
    (π : H →* SL(2,k)) (hπ : Function.Surjective π)
    (S : Sylow 2 H) (D : Subgroup H)
    (hD : D ≤ normalizer (S : Set H))
    (hgen : D ⊔ (S : Subgroup H) = normalizer (S : Set H))
    (hescape : ¬ D ⊓ (S : Subgroup H) ≤ π.ker) :
    (D ⊓ (S : Subgroup H)).map π = (S : Subgroup H).map π := by
  let T := S.mapSurjective hπ
  let A := (D ⊓ (S : Subgroup H)).map π
  have hAT : A ≤ (T : Subgroup SL(2,k)) := map_mono inf_le_right
  have hAn : D ≤ normalizer (D ⊓ (S : Subgroup H) : Set H) :=
    (le_inf D.le_normalizer hD).trans inf_normalizer_le_normalizer_inf
  have hDn : D.map π ≤ normalizer (A : Set SL(2,k)) :=
    (map_mono hAn).trans ((D ⊓ (S : Subgroup H)).le_normalizer_map π)
  let : IsMulCommutative T :=
    ⟨⟨fun x y => (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T).symm.injective
      (by simp [mul_comm])⟩⟩
  have hTn : (T : Subgroup SL(2,k)) ≤ normalizer (A : Set SL(2,k)) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rw [le_centralizer_iff]
    exact hAT.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  apply Matrix.SpecialLinearGroup.subgroup_eq_sylow_of_normalizer_invariant T A hAT
    (fun hz => hescape ((Subgroup.map_eq_bot_iff _).mp hz))
  change normalizer ((S : Subgroup H).map π : Set SL(2,k)) ≤ _
  rw [←S.normalizer_map_surjective π hπ,←hgen,Subgroup.map_sup]
  exact sup_le hDn hTn

/-- A subgroup supplementing the edge core and escaping the vertex core has
full root image at a linear local quotient. -/
theorem graph_linear_supplement_root_image
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v t : Vertex (family P)} (hvt : (graph (family P)).Adj v t)
    (c : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) t))
    (ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) v))
    (π : c.Pstar →* SL(2,k)) (hπ : Function.Surjective π)
    (hk : π.ker = (Q (family P) v).subgroupOf c.Pstar)
    (D : Subgroup G) (hD : D ≤ stabilizer (family P) v ⊓ stabilizer (family P) t)
    (hgen : D ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) t).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) t)
    (hescape : ¬ D ⊓ (stabilizer (family P) v ⊓ stabilizer (family P) t).pCoreIn 2 ≤
      Q (family P) v) :
    ((D ⊓ (stabilizer (family P) v ⊓ stabilizer (family P) t).pCoreIn 2).subgroupOf
      c.Pstar).map π = (c.sylow : Subgroup c.Pstar).map π := by
  let := c.finite_P
  let : Finite c.Pstar := Finite.of_injective (inclusion c.Pstar_le) (inclusion_injective _)
  let E := stabilizer (family P) v ⊓ stabilizer (family P) t
  let S := E.pCoreIn 2
  have hS : (c.sylow : Subgroup c.Pstar).map c.Pstar.subtype = S :=
    local_sylow_eq_edgeCore c ho (source_edge_core_sylow h hB hvt)
  have hSL : S ≤ c.Pstar := hS.symm.le.trans (map_subtype_le _)
  have hSE : S ≤ E := pCoreIn_le 2 E
  have hn : E ≤ normalizer (S : Set G) := E.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  have hf : (D : Set G) * (S : Set G) = E := by
    rw [←coe_mul_of_left_le_normalizer_right D S (hD.trans hn),hgen]
  have hs : S.subgroupOf c.Pstar = c.sylow := by
    apply map_injective c.Pstar.subtype_injective
    rw [map_subgroupOf_eq_of_le hSL,hS]
  have hDn : D.subgroupOf c.Pstar ≤ normalizer (c.sylow : Set c.Pstar) := by
    rw [←source_star_borel c]
    exact subgroupOf_mono _ hD
  have hGn : D.subgroupOf c.Pstar ⊔ (c.sylow : Subgroup c.Pstar) =
      normalizer (c.sylow : Set c.Pstar) := by
    apply le_antisymm (sup_le hDn (c.sylow : Subgroup c.Pstar).le_normalizer)
    intro x hx
    have hxE : (x : G) ∈ E := by rwa [←source_star_borel c] at hx
    change (x : G) ∈ (E : Set G) at hxE
    rw [←hf] at hxE
    obtain ⟨a,ha,s,hs',has⟩ := hxE
    have haL : a ∈ c.Pstar := by
      have hh : (x : G) * s⁻¹ ∈ c.Pstar := c.Pstar.mul_mem x.property (c.Pstar.inv_mem (hSL hs'))
      simpa only [←has,mul_inv_cancel_right] using hh
    have hsS : (⟨s,hSL hs'⟩ : c.Pstar) ∈ (c.sylow : Subgroup c.Pstar) := by
      rw [←hs]; exact hs'
    have he : (⟨a,haL⟩ : c.Pstar) * ⟨s,hSL hs'⟩ = x := Subtype.ext has
    rw [←he]
    exact (D.subgroupOf c.Pstar ⊔ (c.sylow : Subgroup c.Pstar)).mul_mem
      (mem_sup_left ha) (mem_sup_right hsS)
  have hesc : ¬ D.subgroupOf c.Pstar ⊓ (c.sylow : Subgroup c.Pstar) ≤ π.ker := by
    intro hh
    apply hescape
    intro x hx
    have hxL := hSL hx.2
    have hm := hh (show (⟨x,hxL⟩ : c.Pstar) ∈
      D.subgroupOf c.Pstar ⊓ (c.sylow : Subgroup c.Pstar) from
      ⟨hx.1,by rw [←hs]; exact hx.2⟩)
    rw [hk] at hm
    exact hm
  have hh := linear_borel_supplement_image π hπ c.sylow
    (D.subgroupOf c.Pstar) hDn hGn hesc
  change ((D ⊓ S).subgroupOf c.Pstar).map π = _
  change (D.subgroupOf c.Pstar ⊓ S.subgroupOf c.Pstar).map π = _
  rw [hs]
  exact hh

/-- A full Sylow image acts transitively on the other literal graph neighbors
at a linearly marked local quotient. -/
theorem graph_linear_root_transitive
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    {v t : Vertex (family P)} (hvt : (graph (family P)).Adj v t)
    (c : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) t))
    (π : c.Pstar →* SL(2,k)) (hπ : Function.Surjective π)
    (hk : π.ker = (Q (family P) v).subgroupOf c.Pstar)
    (D : Subgroup G)
    (himage : (D.subgroupOf c.Pstar).map π = (c.sylow : Subgroup c.Pstar).map π)
    {a b : Vertex (family P)} (ha : (graph (family P)).Adj v a)
    (hb : (graph (family P)).Adj v b) (hat : a ≠ t) (hbt : b ≠ t) :
    ∃ g ∈ D, g • a = b := by
  let := finite_endpoints h
  let : Finite c.Pstar := Finite.of_injective (inclusion c.Pstar_le) (inclusion_injective _)
  let T := c.sylow.mapSurjective hπ
  have hcore : (Q (family P) v).subgroupOf c.Pstar = pCore 2 c.Pstar := by
    have he : Q (family P) v = c.Pstar.pCoreIn 2 := c.same_core.symm
    rw [he]
    exact comap_map_eq_self_of_injective c.Pstar.subtype_injective _
  have hT : (T : Subgroup SL(2,k)).comap π = c.sylow :=
    comap_map_eq_self (by rw [hk,hcore]; exact pCore_isPGroup.le_sylow_of_normal c.sylow)
  obtain ⟨z,hz,htrans⟩ := sylow_affine_transitive T
  have hstab : (MulAction.stabilizer SL(2,k) z).comap π =
      MulAction.stabilizer c.Pstar t := by
    rw [←hz]
    change (normalizer ((T : Subgroup SL(2,k)) : Set SL(2,k))).comap π = _
    rw [comap_normalizer_eq_of_surjective _ hπ,hT,Sylow.coe_coe,←source_star_borel c]
    ext x
    exact and_iff_right (c.Pstar_le x.property)
  have reach (a : Vertex (family P)) (ha : (graph (family P)).Adj v a) :
      ∃ l : c.Pstar, (l : G) • t = a := by
    obtain ⟨g,hg,hgt⟩ := locally_transitive (family P) hvt ha
    obtain ⟨l,hl,r,hr,hg'⟩ := local_star_factor c g hg
    exact ⟨⟨l,hl⟩,by simpa only [hg',mul_smul,show r • t = t from hr.2] using hgt⟩
  obtain ⟨l,hl⟩ := reach a ha
  obtain ⟨r,hr⟩ := reach b hb
  obtain ⟨g,hg,hgr⟩ := Theory.GroupAction.MatchedPointOrbit.transitive_away_from_base π
    (D.subgroupOf c.Pstar) t z hstab
    (by rw [himage]; exact htrans) l r
    (by change (l : G) • t ≠ t; rwa [hl])
    (by change (r : G) • t ≠ t; rwa [hr])
  refine ⟨g,hg,?_⟩
  change (g : G) • ((l : G) • t) = (r : G) • t at hgr
  rwa [hl,hr] at hgr

/-- The linear case in (7.5)(5): the path supplement and a two-subgroup
escaping the vertex core force right regularity of the very same path. -/
theorem graph_linear_path_rightRegular
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {n : ℕ} {x : Vertex (family P)} (p : BasedWalk (graph (family P)) (n+1) x)
    (c : LocalRankOneData (stabilizer (family P) p.endpoint)
      (stabilizer (family P) p.endpoint ⊓ stabilizer (family P) p.penultimate))
    (ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) p.endpoint))
    (π : c.Pstar →* SL(2,k)) (hπ : Function.Surjective π)
    (hk : π.ker = (Q (family P) p.endpoint).subgroupOf c.Pstar)
    (hgen : pathStabilizer (family P) p ⊔
        (stabilizer (family P) p.endpoint ⊓ stabilizer (family P) p.penultimate).pCoreIn 2 =
      stabilizer (family P) p.endpoint ⊓ stabilizer (family P) p.penultimate)
    (A : Subgroup G) (hpA : IsPGroup 2 A)
    (hAp : A ≤ pathStabilizer (family P) p) (hAQ : ¬ A ≤ Q (family P) p.endpoint) :
    RightRegular (A := G) p := by
  let := finite_endpoints h
  let E := stabilizer (family P) p.endpoint ⊓ stabilizer (family P) p.penultimate
  let : Finite E := Finite.of_injective
    (inclusion (show E ≤ stabilizer (family P) p.endpoint from inf_le_left)) (inclusion_injective _)
  have hem : p.endpoint ∈ p.vertices := by
    simpa only [BasedWalk.support_toWalk] using p.toWalk.end_mem_support
  have hpm : p.penultimate ∈ p.vertices := by
    have hh := (p.take n (Nat.le_succ n)).toWalk.end_mem_support
    rw [BasedWalk.support_toWalk,BasedWalk.endpoint_take_penultimate,BasedWalk.vertices_take] at hh
    exact List.mem_of_mem_take hh
  have hDE : pathStabilizer (family P) p ≤ E := pathStabilizer_le_edge (family P) p hem hpm
  have hAS : A ≤ E.pCoreIn 2 := pGroup_le_core_of_core_sylow E A (hAp.trans hDE) hpA
    (source_edge_core_sylow h hB p.adj_penultimate_endpoint.symm)
  have hesc : ¬ pathStabilizer (family P) p ⊓ E.pCoreIn 2 ≤ Q (family P) p.endpoint :=
    fun hh => hAQ ((le_inf hAp hAS).trans hh)
  have himg := graph_linear_supplement_root_image h hB p.adj_penultimate_endpoint.symm c ho
    π hπ hk (pathStabilizer (family P) p) hDE hgen hesc
  intro a b ha hb
  obtain ⟨g,hg,he⟩ := graph_linear_root_transitive h p.adj_penultimate_endpoint.symm c
    π hπ hk _ himg ha.1 hb.1 ha.2 hb.2
  exact ⟨g,hg.1,he⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting

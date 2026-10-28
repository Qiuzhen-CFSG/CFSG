module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSourceLowerBound

/-!
# The upper source length and nine-path oddness from the base-edge inputs

Transport the original center inclusion, commutator and nonzero branch to
any normalized nine-path, then use conjugation and reversal to cover
both vertex orbits. Restriction gives oddness at every longer length. The earlier distance-three result and actual
three-path transitivity supply all four critical placements. Thus (12.7)
no longer requires path-specific center or critical-pair hypotheses.

An odd path fixer cannot act transitively on the positive even set of
forward neighbors. Apply this to the selected source nine-path to bound
s by nine. The same original full-Borel complement used for the lower
bound is retained in the construction.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.7)--(12.9), printed pp.184--187. The base quotient markings and genuine
earlier center, Sylow and commutator inputs remain explicit.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups Pointwise
open BenderSuzuki.MatrixGroups
open Theory.GroupAction.CubicTree SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
private theorem source_path_not_right_regular_of_odd
    (h : HypothesisF11 L S) {r : ℕ} {a : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) (r+1) a)
    (ho : Odd (Nat.card (pathStabilizer (reducedFamily L S) p))) :
    ¬ RightRegular (A := G₀ L S) p := by
  classical
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite ((graph F).neighborSet p.endpoint) :=
    Theory.GroupTheory.AmalgamGraph.finite_neighbors F p.endpoint
  have hval := card_neighbors_of_indices F
    (fun j => ((F (!j)).subgroupOf (F j)).index) (fun _ => rfl) p.endpoint
  obtain ⟨d,hd⟩ := reduced_rankOne_branching h p.endpoint.type
  have hge := source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) p.endpoint.type
  change 3 ≤ ((F (!p.endpoint.type)).subgroupOf (F p.endpoint.type)).index at hge
  change ((F (!p.endpoint.type)).subgroupOf (F p.endpoint.type)).index - 1 = 2^d at hd
  have hdpos : 0 < d := by
    by_contra hn
    have hd0 : d = 0 := by omega
    rw [hd0,pow_zero] at hd
    omega
  let E : {z : Vertex F // Forward p z} ≃
      {z : (graph F).neighborSet p.endpoint //
        z ≠ ⟨p.penultimate,p.adj_penultimate_endpoint.symm⟩} := {
    toFun z := ⟨⟨z,z.property.1⟩,fun he => z.property.2 (congrArg Subtype.val he)⟩
    invFun z := ⟨z.val,z.val.property,fun he => z.property (Subtype.ext he)⟩
    left_inv z := rfl
    right_inv z := rfl }
  let := Fintype.ofFinite ((graph F).neighborSet p.endpoint)
  have hecard : Nat.card {z : Vertex F // Forward p z} = 2^d := by
    rw [Nat.card_congr E,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
      ←Nat.card_eq_fintype_card,hval]
    simpa only [Fintype.card_unique] using hd
  let D : Set (Vertex F) := {z | Forward p z}
  obtain ⟨z,hz⟩ : D.Nonempty := Set.nonempty_of_ncard_ne_zero (by
    rw [←Nat.card_coe_set_eq]
    change Nat.card {z : Vertex F // Forward p z} ≠ 0
    rw [hecard]
    positivity)
  have hact : GraphAction (graph F) (G₀ L S) :=
    ⟨fun g _ _ ha => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj ha⟩
  intro hr
  have he : MulAction.orbit (pathStabilizer F p) z = D := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g,rfl⟩
      exact forward_smul_of_fixes hact p g g.property hz
    · intro w hw
      obtain ⟨g,hg,hgw⟩ := hr z w hz hw
      exact ⟨⟨g,hg⟩,hgw⟩
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (pathStabilizer F p) z)
  rw [Nat.card_prod,he] at hc
  have hDeven : Even (Nat.card D) := by
    change Even (Nat.card {z : Vertex F // Forward p z})
    rw [hecard]
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
    rw [pow_succ]
    exact ⟨2^j,by omega⟩
  exact (Nat.not_even_iff_odd.mpr ho) (hc ▸ hDeven.mul_right _)

set_option backward.isDefEq.respectTransparency false in
/-- Nine-path oddness with every path-specific earlier-source premise discharged. -/
theorem source_suzuki_normalized_nine_path_odd
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {σ : Vertex (reducedFamily L S)}
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {x₀ : Vertex (reducedFamily L S)}
    (hx₀ : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x₀)
    (hx₀n : x₀ ≠ base (reducedFamily L S) (!i))
    (hbranch : ⁅V (reducedFamily L S) x₀ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i)) :
    Odd (Nat.card (pathStabilizer (reducedFamily L S) p)) ∧
      Odd (Nat.card ((pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype)) := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let m := base F i
  let y := base F (!i)
  let x : Vertex F := p.1
  let z : Vertex F := p.2.2.2.1
  let w : Vertex F := p.2.2.2.2.1
  change (p.2.1 : Vertex F) = m at hm
  change (p.2.2.1 : Vertex F) = y at hy
  have hxm : (graph F).Adj x m := by
    rw [←hm]
    exact p.2.1.property
  have hyz : (graph F).Adj y z := by
    rw [←hy]
    exact p.2.2.2.1.property
  have hzw : (graph F).Adj z w := p.2.2.2.2.1.property
  have hwy : w ≠ y := by simpa only [hy] using hp.2.2.2.1
  have hmy : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨a,ha,hay⟩ := star_locally_transitive h i hmy hxm.symm
  have ham : a • m = m := star_le_stabilizer i ha
  have hzx : Z F x ≤ Z F m := by
    have hh := map_mono (f := (MulAut.conj a).toMonoidHom) hzy
    change (Z F y).map (MulAut.conj a).toMonoidHom ≤ (Z F m).map (MulAut.conj a).toMonoidHom at hh
    rwa [←Z_translate F,←Z_translate F,hay,ham] at hh
  have hcommx : ⁅V F x 1,Q F x⁆ ≤ Z F x := by
    have hh := congrArg (fun H : Subgroup (G₀ L S) => H.map (MulAut.conj a).toMonoidHom) hcommy
    change (⁅V F y 1,Q F y⁆ : Subgroup (G₀ L S)).map (MulAut.conj a).toMonoidHom =
      (Z F y).map (MulAut.conj a).toMonoidHom at hh
    rw [map_commutator,←V_translate F,←Q_translate F,←Z_translate F,hay] at hh
    exact hh.le
  have hbranchw : ⁅V F w 1 ⊓ Q F y,V F y 1⁆ ≠ ⊥ := by
    obtain ⟨g,hg,hgz⟩ := star_locally_transitive h (!i) hyz hmy.symm
    have hgy : g • y = y := star_le_stabilizer (!i) hg
    have hmgw : (graph F).Adj m (g • w) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hzw
      change (graph F).Adj (g • z) (g • w) at hh
      rwa [hgz] at hh
    have hgwne : g • w ≠ y := fun he => hwy ((MulAction.injective g) (he.trans hgy.symm))
    obtain ⟨u,hu,huw⟩ := linear_common_sylow_transitive h i e T hT hmgw hx₀ hgwne hx₀n
    have huy : u • y = y :=
      (sup_le (Q_le_stabilizer F y)
        (((source_Z_Q_U (reduced_triple h) m).2.trans
          (ballKernel_one_le_edge F hmy)).trans inf_le_right)) hu
    have hty : (u*g) • y = y := by rw [mul_smul,hgy,huy]
    have htw : (u*g) • w = x₀ := by rw [mul_smul,huw]
    intro he
    have hh := congrArg (fun H : Subgroup (G₀ L S) =>
      H.map (MulAut.conj (u*g)).toMonoidHom) he
    rw [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj (u*g)).injective,
      ←V_translate F,←Q_translate F,←V_translate F,hty,htw,Subgroup.map_bot] at hh
    exact hbranch hh
  have hb : 2 < b F := by
    change 2 < b (reducedFamily L S)
    omega
  have hc := source_mixed_nine_path_initial_critical h i hb3 hn e eSuz T hT Ry hRy hzy
    p hp hm hy
  obtain ⟨hc6,hc2,hc8⟩ := source_mixed_nine_path_critical_pairs h i hb hn e eSuz
    T hT Ry hRy p hp hy hc
  obtain ⟨R,hR⟩ := source_common_sylow_neighbors h i T hT x hxm.symm
  exact source_suzuki_nine_path_odd h i hb p hp hm hy T R hT hR e hz hcard hcardy
    hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc
    hmin hnat hc6 hc2 hc8 hbranchw

private theorem pathStabilizer_map_conjugate
    {F : Bool → Subgroup G} {r : ℕ} {a b : Vertex F}
    (p : BasedWalk (graph F) r a) (q : BasedWalk (graph F) r b) (g : G)
    (hv : q.vertices = p.vertices.map (g • ·)) :
    (pathStabilizer F p).map (MulAut.conj g).toMonoidHom = pathStabilizer F q := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩ z hz
    rw [hv] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    change (g * u * g⁻¹) • (g • w) = g • w
    simp only [mul_smul,inv_smul_smul,hu w hw]
  · intro hx
    refine ⟨g⁻¹ * x * g,?_,?_⟩
    · intro z hz
      have he := hx (g • z) (by rw [hv]; exact List.mem_map.mpr ⟨z,hz,rfl⟩)
      simpa only [mul_smul,inv_smul_smul] using congrArg (g⁻¹ • ·) he
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      simp only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- DGS (12.7) for every nonbacktracking nine-path in either vertex orbit,
including its literal image in the original completion. -/
theorem source_suzuki_every_nine_path_odd
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {σ : Vertex (reducedFamily L S)}
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {x₀ : Vertex (reducedFamily L S)}
    (hx₀ : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x₀)
    (hx₀n : x₀ ≠ base (reducedFamily L S) (!i))
    (hbranch : ⁅V (reducedFamily L S) x₀ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking) :
    Odd (Nat.card (pathStabilizer (reducedFamily L S) p)) ∧
      Odd (Nat.card ((pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype)) := by
  let F := reducedFamily L S
  have first {v : Vertex F} (t : BasedWalk (graph F) 9 v)
      (ht : t.Nonbacktracking) (hvi : v.type = i) :
      Odd (Nat.card (pathStabilizer F t)) := by
    let m : Vertex F := t.2.1
    let y : Vertex F := t.2.2.1
    have h02 : v.type = m.type :=
      (Bool.eq_not_iff.mpr t.1.property.1).trans
        (Bool.eq_not_iff.mpr t.2.1.property.1.symm).symm
    have hmi : m.type = i := h02.symm.trans hvi
    have hmy : (graph F).Adj m y := t.2.2.1.property
    have hyi : y.type = !i := Bool.eq_not_iff.mpr (hmi ▸ hmy.1.symm)
    obtain ⟨g,hgm,hgy⟩ := incident_common_translate F hmy.2
    rw [hmi] at hgm
    rw [hyi] at hgy
    have hact : GraphAction (graph F) (G₀ L S) :=
      ⟨fun g _ _ ha => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj ha⟩
    let q := t.map (hact.hom g⁻¹)
    have hq : q.Nonbacktracking := (hact.nonbacktracking_map_iff g⁻¹ t).mpr ht
    have hqm : (q.2.1 : Vertex F) = base F i := by
      change g⁻¹ • m = base F i
      rw [←hgm,inv_smul_smul]
    have hqy : (q.2.2.1 : Vertex F) = base F (!i) := by
      change g⁻¹ • y = base F (!i)
      rw [←hgy,inv_smul_smul]
    have ho := source_suzuki_normalized_nine_path_odd h i hb3 T hT e hz hcard hcardy
      hzy hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hx₀ hx₀n hbranch
      q hq hqm hqy
    have hc := congrArg (fun H : Subgroup (G₀ L S) => Nat.card H)
      (pathStabilizer_map_conjugate t q g⁻¹ (BasedWalk.vertices_map _ _))
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective] at hc
    exact hc ▸ ho.1
  have ho : Odd (Nat.card (pathStabilizer F p)) := by
    by_cases hvi : v₀.type = i
    · exact first p hp hvi
    have hne : v₀.type ≠ p.endpoint.type := by
      intro he
      have hh := (even_walk_iff F p.toWalk).mpr he
      rw [BasedWalk.length_toWalk] at hh
      exact (by decide : ¬Even (9 : ℕ)) hh
    have hei : p.endpoint.type = i := by
      have h0 : v₀.type = !i := Bool.eq_not_iff.mpr hvi
      have he : p.endpoint.type = !v₀.type := Bool.eq_not_iff.mpr (Ne.symm hne)
      simpa only [h0,Bool.not_not] using he
    have hr := first (reverse p) (nonbacktracking_reverse p hp) hei
    have he : pathStabilizer F (reverse p) = pathStabilizer F p := by
      ext x
      change (∀ z ∈ (reverse p).vertices, x • z = z) ↔ ∀ z ∈ p.vertices, x • z = z
      simp only [vertices_reverse,List.mem_reverse]
    rwa [he] at hr
  refine ⟨ho,?_⟩
  rw [card_map_of_injective (G₀ L S).subtype_injective]
  exact ho

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the initial nine-path gives odd original fixers at every longer length. -/
theorem source_suzuki_long_path_odd
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {σ : Vertex (reducedFamily L S)}
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {x₀ : Vertex (reducedFamily L S)}
    (hx₀ : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x₀)
    (hx₀n : x₀ ≠ base (reducedFamily L S) (!i))
    (hbranch : ⁅V (reducedFamily L S) x₀ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    {r : ℕ} {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) r v₀) (hp : p.Nonbacktracking)
    (hr : 9 ≤ r) :
    Odd (Nat.card (pathStabilizer (reducedFamily L S) p)) ∧
      Odd (Nat.card ((pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype)) := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite (pathStabilizer F (p.take 9 hr)) := Finite.of_injective
    (inclusion (pathStabilizer_le F (p.take 9 hr))) (inclusion_injective _)
  have ho := source_suzuki_every_nine_path_odd h i hb3 T hT e hz hcard hcardy
      hzy hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hx₀ hx₀n hbranch
    (p.take 9 hr) (BasedWalk.nonbacktracking_take hr p hp)
  have hle : pathStabilizer F p ≤ pathStabilizer F (p.take 9 hr) := by
    intro g hg z hz
    rw [BasedWalk.vertices_take] at hz
    exact hg z (List.mem_of_mem_take hz)
  have hodd : Odd (Nat.card (pathStabilizer F p)) :=
    Odd.of_dvd_nat ho.1 (card_dvd_of_le hle)
  refine ⟨hodd,?_⟩
  rw [card_map_of_injective (G₀ L S).subtype_injective]
  exact hodd

set_option backward.isDefEq.respectTransparency false in
/-- The source first nonregular length is at most nine, using an actually selected path. -/
theorem source_suzuki_sourceS_le_nine
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {σ : Vertex (reducedFamily L S)}
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {x₀ : Vertex (reducedFamily L S)}
    (hx₀ : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x₀)
    (hx₀n : x₀ ≠ base (reducedFamily L S) (!i))
    (hbranch : ⁅V (reducedFamily L S) x₀ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
 :
    sourceS (P := fun j => (P₀ L S j).subgroupOf (G₀ L S)) ≤ 9 := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  obtain ⟨ℓ,_,j,δ,_,_,_,C,hoddC,_,_,_,_,v₀,p,hp,hm,hy,hfixC,_,hK⟩ :=
    source_mixed_minimal_path_fixed_nine_path h i hn e eSuz Ry hRy
  have ho := source_suzuki_normalized_nine_path_odd h i hb3 T hT e hz hcard hcardy
    hzy hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hx₀ hx₀n hbranch
    p hp hm hy
  by_contra hs
  exact source_path_not_right_regular_of_odd h p ho.1
    (sourceS_short_regular (reduced_triple h) (reduced_vertex_sylow h) p (by omega) hp).2

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer

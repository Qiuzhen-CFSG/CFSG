module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Suborbits
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Frame

/-!
# Completing the J₂ source suborbit calculation from representatives

Aschbacher, *Sporadic Groups* (1994), 47.5, p.263, constructs three
order-three subgroup pairs, with joins A₄, SL₂(3), and A₅. Their pointwise
stabilizers have orders 60, 16, and 20 in the order-2160 normalizer.
Orbit-stabilizer gives 36, 135, and 108 conjugates. The global order
604800 forces 280 vertices, so these three orbits and the base point
exhaust the vertex set. Distinct actual join types separate the orbits.

This module proves that completion step, including transport of the
actual stabilizer equivalences and Sylow subgroup to every vertex.
`ThreePairRepresentatives` is the outstanding local construction, not
an assertion of 47.5 from `Seed`. Its construction from the earlier
47.1–47.3 conclusions remains required by the source assembly owner.

For 47.6(5), p.264, setwise edge conjugation preserves whether a third
vertex lies in the endpoint join, separating the two triangle types.
The A₅ pointwise fixer fixes every vertex inside that join individually.
These facts do not assert transitivity on either triangle type.
-/

@[expose] public section

open Subgroup MulAction
open scoped BigOperators
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
variable {G : Type*} [Group G] [Finite G]

noncomputable def joinConjEquiv (D : Seed G) (g : G) (A B : D.Vertex) :
    (A.val ⊔ B.val : Subgroup G) ≃* ((g • A).val ⊔ (g • B).val : Subgroup G) :=
  ((A.val ⊔ B.val).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr (by rw [Subgroup.map_sup, D.smul_val, D.smul_val]))

theorem sl2Join_smul_iff (D : Seed G) (g : G) (A B : D.Vertex) :
    sl2Join D (g • A) (g • B) ↔ sl2Join D A B := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(joinConjEquiv D g A B).trans e⟩
  · rintro ⟨e⟩
    exact ⟨(joinConjEquiv D g A B).symm.trans e⟩

theorem a5Join_smul_iff (D : Seed G) (g : G) (A B : D.Vertex) :
    a5Join D (g • A) (g • B) ↔ a5Join D A B := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(joinConjEquiv D g A B).trans e⟩
  · rintro ⟨e⟩
    exact ⟨(joinConjEquiv D g A B).symm.trans e⟩

theorem normalizer_fixes_base (D : Seed G) (g : normalizer (D.X : Set G)) :
    (g : G) • D.base = D.base := by
  apply mem_stabilizer_iff.mp
  rw [D.stabilizer_eq_normalizer]
  exact g.property

theorem orbitLabel_normalizer_smul (D : Seed G)
    (g : normalizer (D.X : Set G)) (V : D.Vertex) :
    orbitLabel D ((g : G) • V) = orbitLabel D V := by
  classical
  have hbase := normalizer_fixes_base D g
  have he : (g : G) • V = D.base ↔ V = D.base := by
    conv_lhs => rw [← hbase]
    exact (MulAction.injective (β := D.Vertex) (g : G)).eq_iff
  have ha : D.graph.Adj D.base ((g : G) • V) ↔ D.graph.Adj D.base V := by
    conv_lhs => rw [← hbase]
    constructor
    · intro h
      simpa using D.preserves (g : G)⁻¹ h
    · exact D.preserves (g : G)
  have hs : sl2Join D D.base ((g : G) • V) ↔ sl2Join D D.base V := by
    conv_lhs => rw [← hbase]
    exact sl2Join_smul_iff D g D.base V
  simp only [orbitLabel, he, ha, hs]

theorem orbitLabel_of_sl2Join (D : Seed G) {V : D.Vertex}
    (h : sl2Join D D.base V) : orbitLabel D V = 2 := by
  classical
  have hc := card_join_of_sl2Join D h
  have hn : V ≠ D.base := by
    intro he
    rw [he, sup_idem, D.vertex_card] at hc
    omega
  have ha : ¬ D.graph.Adj D.base V := by
    intro he
    have := card_join_of_adj D he
    omega
  simp [orbitLabel, hn, ha, h]

theorem orbitLabel_of_a5Join (D : Seed G) {V : D.Vertex}
    (h : a5Join D D.base V) : orbitLabel D V = 3 := by
  classical
  have hc := card_join_of_a5Join D h
  have hn : V ≠ D.base := by
    intro he
    rw [he, sup_idem, D.vertex_card] at hc
    omega
  have ha : ¬ D.graph.Adj D.base V := by
    intro he
    have := card_join_of_adj D he
    omega
  have hs : ¬ sl2Join D D.base V := by
    intro he
    have := card_join_of_sl2Join D he
    omega
  simp [orbitLabel, hn, ha, hs]

private theorem orbit_card_mul_stabilizer {H Ω : Type*} [Group H] [MulAction H Ω]
    (v : Ω) : Nat.card (orbit H v) * Nat.card (stabilizer H v) = Nat.card H := by
  rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup H v)]

theorem vertex_card_of_source_orders (D : Seed G)
    (hG : Nat.card G = 604800) (hM : Nat.card (normalizer (D.X : Set G)) = 2160) :
    Nat.card D.Vertex = 280 := by
  have he : orbit G D.base = Set.univ := by
    ext V
    simp only [Set.mem_univ, iff_true]
    exact D.transitive V
  have hc := orbit_card_mul_stabilizer (H := G) D.base
  rw [he, Nat.card_congr (Equiv.Set.univ _), D.stabilizer_eq_normalizer, hG] at hc
  change Nat.card D.Vertex * Nat.card (normalizer (D.X : Set G)) = 604800 at hc
  rw [hM] at hc
  omega

/-- The intrinsic stabilizer in the literal base normalizer is the ambient
pointwise edge fixer, with its actual inclusion into G. -/
noncomputable def normalizerStabilizerEquiv (D : Seed G) (V : D.Vertex) :
    stabilizer (normalizer (D.X : Set G)) V ≃*
      Theory.GroupTheory.GraphUniquenessSystem.edgeFixer G D.base V := by
  let F := Theory.GroupTheory.GraphUniquenessSystem.edgeFixer G D.base V
  have hF : F ≤ normalizer (D.X : Set G) := by
    change F ≤ normalizer (D.base.val : Set G)
    rw [← D.stabilizer_eq_normalizer D.base]
    exact inf_le_left
  have he : stabilizer (normalizer (D.X : Set G)) V =
      F.subgroupOf (normalizer (D.X : Set G)) := by
    ext g
    change (g : G) • V = V ↔
      (g : G) ∈ stabilizer G D.base ∧ (g : G) ∈ stabilizer G V
    simp only [mem_stabilizer_iff, normalizer_fixes_base D g, true_and]
  exact (MulEquiv.subgroupCongr he).trans (subgroupOfEquivOfLe hF)

private theorem label_two_join (D : Seed G) {V : D.Vertex}
    (h : orbitLabel D V = 2) : sl2Join D D.base V := by
  classical
  unfold orbitLabel at h
  split_ifs at h <;> simp_all

private theorem fourOrbitSaturation (D : Seed G) (v : Fin 4 → D.Vertex)
    (hv : ∀ i, orbitLabel D (v i) = i)
    (hc : ∀ i, Nat.card (orbit (normalizer (D.X : Set G)) (v i)) = subdegrees i)
    (hcard : Nat.card D.Vertex = 280) :
    ∀ V : D.Vertex, ∃ k : normalizer (D.X : Set G),
      (k : G) • v (orbitLabel D V) = V := by
  let f : (Σ i : Fin 4, orbit (normalizer (D.X : Set G)) (v i)) → D.Vertex :=
    fun a => a.2.val
  have hl (i : Fin 4) (a : orbit (normalizer (D.X : Set G)) (v i)) :
      orbitLabel D a.val = i := by
    obtain ⟨g, hg⟩ := a.property
    rw [← hg]
    exact (orbitLabel_normalizer_smul D g (v i)).trans (hv i)
  have hf : Function.Injective f := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    have hij : i = j := (hl i a).symm.trans ((congrArg (orbitLabel D) hab).trans (hl j b))
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext hab)
  have hsurj := (hf.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_sigma]
    simp_rw [hc]
    decide +kernel)).2
  intro V
  obtain ⟨⟨i, a⟩, ha⟩ := hsurj V
  have hi : orbitLabel D V = i := ha ▸ hl i a
  rw [hi, ← ha]
  exact a.property

/-- Completing 47.5 from three local representative calculations. No orbit
cover or subdegree is a hypothesis: orbit-stabilizer and the group order
force the three representatives and the base point to exhaust the vertices. -/
theorem fourSuborbits_of_representative_stabilizer_orders (D : Seed G)
    (hG : Nat.card G = 604800) (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (Y S A : D.Vertex) (hY : D.graph.Adj D.base Y)
    (hS : sl2Join D D.base S) (hA : a5Join D D.base A)
    (cY : Nat.card (stabilizer (normalizer (D.X : Set G)) Y) = 60)
    (cS : Nat.card (stabilizer (normalizer (D.X : Set G)) S) = 16)
    (cA : Nat.card (stabilizer (normalizer (D.X : Set G)) A) = 20) :
    FourSuborbits D := by
  let v : Fin 4 → D.Vertex := ![D.base, Y, S, A]
  have hv : ∀ i, orbitLabel D (v i) = i := by
    intro i
    fin_cases i
    · exact orbitLabel_base D
    · exact orbitLabel_of_adj D hY
    · exact orbitLabel_of_sl2Join D hS
    · exact orbitLabel_of_a5Join D hA
  have hc : ∀ i, Nat.card (orbit (normalizer (D.X : Set G)) (v i)) = subdegrees i := by
    intro i
    have hh := orbit_card_mul_stabilizer (H := normalizer (D.X : Set G)) (v i)
    rw [hM] at hh
    fin_cases i
    · have hb : stabilizer (normalizer (D.X : Set G)) D.base = ⊤ := by
        ext g
        simp only [mem_stabilizer_iff, Subgroup.mem_top, iff_true]
        exact normalizer_fixes_base D g
      change Nat.card (orbit (normalizer (D.X : Set G)) D.base) *
        Nat.card (stabilizer (normalizer (D.X : Set G)) D.base) = 2160 at hh
      rw [hb, card_top, hM] at hh
      change Nat.card (orbit (normalizer (D.X : Set G)) D.base) = 1
      omega
    · change Nat.card (orbit (normalizer (D.X : Set G)) Y) *
        Nat.card (stabilizer (normalizer (D.X : Set G)) Y) = 2160 at hh
      rw [cY] at hh
      change Nat.card (orbit (normalizer (D.X : Set G)) Y) = 36
      omega
    · change Nat.card (orbit (normalizer (D.X : Set G)) S) *
        Nat.card (stabilizer (normalizer (D.X : Set G)) S) = 2160 at hh
      rw [cS] at hh
      change Nat.card (orbit (normalizer (D.X : Set G)) S) = 135
      omega
    · change Nat.card (orbit (normalizer (D.X : Set G)) A) *
        Nat.card (stabilizer (normalizer (D.X : Set G)) A) = 2160 at hh
      rw [cA] at hh
      change Nat.card (orbit (normalizer (D.X : Set G)) A) = 108
      omega
  have hs := fourOrbitSaturation D v hv hc (vertex_card_of_source_orders D hG hM)
  have hbase (V : D.Vertex) : D.base = V ∨ D.graph.Adj D.base V ∨
      sl2Join D D.base V ∨ a5Join D D.base V := by
    obtain ⟨k, hk⟩ := hs V
    generalize hi : orbitLabel D V = i at hk
    fin_cases i
    · left
      change (k : G) • D.base = V at hk
      rwa [normalizer_fixes_base] at hk
    · exact Or.inr (Or.inl ((orbitLabel_eq_one_iff D V).mp hi))
    · exact Or.inr (Or.inr (Or.inl (label_two_join D hi)))
    · right; right; right
      have h := (a5Join_smul_iff D (k : G) D.base A).mpr hA
      rwa [normalizer_fixes_base, show (k : G) • A = V from hk] at h
  refine ⟨?_, ?_, ?_⟩
  · intro U V
    obtain ⟨g, rfl⟩ := D.transitive U
    rcases hbase (g⁻¹ • V) with he | he | he | he
    · left
      exact (congrArg (fun W : D.Vertex => g • W) he).trans (smul_inv_smul g V)
    · right; left
      simpa only [smul_inv_smul] using D.preserves g he
    · right; right; left
      simpa only [smul_inv_smul] using (sl2Join_smul_iff D g D.base (g⁻¹ • V)).mpr he
    · right; right; right
      simpa only [smul_inv_smul] using (a5Join_smul_iff D g D.base (g⁻¹ • V)).mpr he
  · intro U V h
    obtain ⟨g, hg⟩ := hs U
    obtain ⟨k, hk⟩ := hs V
    refine ⟨k * g⁻¹, ?_⟩
    rw [← hg, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_smul, h, hk]
  · intro i
    have he : {V : D.Vertex | orbitLabel D V = i} =
        orbit (normalizer (D.X : Set G)) (v i) := by
      ext V
      constructor
      · intro h
        obtain ⟨k, hk⟩ := hs V
        exact ⟨k, h ▸ hk⟩
      · rintro ⟨k, rfl⟩
        exact (orbitLabel_normalizer_smul D k (v i)).trans (hv i)
    change Nat.card ({V : D.Vertex | orbitLabel D V = i}) = subdegrees i
    rw [he]
    exact hc i

open Theory.GroupTheory.GraphUniquenessSystem

/-- Local witnesses required by the representative construction in 47.5.
These do not assume any suborbit size or a cover of the vertex set. -/
structure ThreePairRepresentatives (D : Seed G) where
  edge : D.Vertex
  edge_adjacent : D.graph.Adj D.base edge
  edge_fixer : Nonempty (edgeFixer G D.base edge ≃* alternatingGroup (Fin 5))
  sl : D.Vertex
  sl_join : sl2Join D D.base sl
  sl_sylow : ∃ P : Sylow 2 (normalizer (D.X : Set G)),
    (P : Subgroup (normalizer (D.X : Set G))) =
      stabilizer (normalizer (D.X : Set G)) sl
  five : D.Vertex
  five_join : a5Join D D.base five
  five_fixer : Nonempty (edgeFixer G D.base five ≃*
    (Multiplicative (ZMod 2) × DihedralGroup 5))

namespace ThreePairRepresentatives
variable {D : Seed G} (R : ThreePairRepresentatives D)
include R

/-- Source representative stabilizers determine the published four suborbits. -/
theorem fourSuborbits (hG : Nat.card G = 604800)
    (hM : Nat.card (normalizer (D.X : Set G)) = 2160) : FourSuborbits D := by
  apply fourSuborbits_of_representative_stabilizer_orders D hG hM
    R.edge R.sl R.five R.edge_adjacent R.sl_join R.five_join
  · rw [Nat.card_congr (normalizerStabilizerEquiv D R.edge).toEquiv,
      Nat.card_congr R.edge_fixer.some.toEquiv, nat_card_alternatingGroup]
    norm_num
  · obtain ⟨P, hP⟩ := R.sl_sylow
    rw [← hP, P.card_eq_multiplicity, hM]
    decide +kernel
  · rw [Nat.card_congr (normalizerStabilizerEquiv D R.five).toEquiv,
      Nat.card_congr R.five_fixer.some.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, DihedralGroup.card]

/-- All edge fixers have the actual A₅ type of the representative. -/
theorem edgeFixer_equiv (hG : Nat.card G = 604800)
    (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    {V : D.Vertex} (hV : D.graph.Adj D.base V) :
    Nonempty (edgeFixer G D.base V ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨k, hk⟩ := (R.fourSuborbits hG hM).transitive R.edge V
    ((orbitLabel_of_adj D R.edge_adjacent).trans (orbitLabel_of_adj D hV).symm)
  exact ⟨(normalizerStabilizerEquiv D V).symm.trans
    ((stabilizerEquivStabilizer (g := k) hk.symm).symm.trans
      ((normalizerStabilizerEquiv D R.edge).trans R.edge_fixer.some))⟩

/-- Every SL₂(3) pair has an actual Sylow two stabilizer in N_G(X). -/
theorem sl_stabilizer_sylow (hG : Nat.card G = 604800)
    (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    {V : D.Vertex} (hV : sl2Join D D.base V) :
    ∃ P : Sylow 2 (normalizer (D.X : Set G)),
      (P : Subgroup (normalizer (D.X : Set G))) =
        stabilizer (normalizer (D.X : Set G)) V := by
  obtain ⟨k, hk⟩ := (R.fourSuborbits hG hM).transitive R.sl V
    ((orbitLabel_of_sl2Join D R.sl_join).trans (orbitLabel_of_sl2Join D hV).symm)
  obtain ⟨P, hP⟩ := R.sl_sylow
  have hc : Nat.card (stabilizer (normalizer (D.X : Set G)) V) =
      2 ^ (Nat.card (normalizer (D.X : Set G))).factorization 2 := by
    rw [← Nat.card_congr (stabilizerEquivStabilizer (g := k) hk.symm).toEquiv,
      ← hP, P.card_eq_multiplicity]
  exact ⟨Sylow.ofCard _ hc, rfl⟩

/-- The A₅-join suborbit has pointwise stabilizer C₂ × D₁₀. -/
theorem five_edgeFixer_equiv (hG : Nat.card G = 604800)
    (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    {V : D.Vertex} (hV : a5Join D D.base V) :
    Nonempty (edgeFixer G D.base V ≃* (Multiplicative (ZMod 2) × DihedralGroup 5)) := by
  obtain ⟨k, hk⟩ := (R.fourSuborbits hG hM).transitive R.five V
    ((orbitLabel_of_a5Join D R.five_join).trans (orbitLabel_of_a5Join D hV).symm)
  exact ⟨(normalizerStabilizerEquiv D V).symm.trans
    ((stabilizerEquivStabilizer (g := k) hk.symm).symm.trans
      ((normalizerStabilizerEquiv D R.five).trans R.five_fixer.some))⟩

end ThreePairRepresentatives

/-- Setwise edge conjugation preserves the subgroup generated by its endpoints. -/
theorem edgeStabilizer_preserves_join (D : Seed G) (A B : D.Vertex)
    (g : edgeStabilizer G A B) :
    (A.val ⊔ B.val).map (MulAut.conj (g : G)).toMonoidHom = A.val ⊔ B.val := by
  rw [Subgroup.map_sup, ← D.smul_val, ← D.smul_val]
  rcases g.property with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb]
  · rw [ha, hb, sup_comm]

/-- The two triangle types cannot be fused by the setwise edge stabilizer. -/
theorem edgeStabilizer_smul_le_join_iff (D : Seed G) (A B V : D.Vertex)
    (g : edgeStabilizer G A B) :
    ((g : G) • V).val ≤ A.val ⊔ B.val ↔ V.val ≤ A.val ⊔ B.val := by
  rw [D.smul_val]
  conv_lhs => rw [← edgeStabilizer_preserves_join D A B g]
  exact map_le_map_iff_of_injective (f := (MulAut.conj (g : G)).toMonoidHom)
    (MulAut.conj (g : G)).injective

theorem triangle_types_not_conjugate (D : Seed G) (A B T₁ T₂ : D.Vertex)
    (h₁ : T₁.val ≤ A.val ⊔ B.val) (h₂ : ¬ T₂.val ≤ A.val ⊔ B.val) :
    ¬ ∃ g : edgeStabilizer G A B, (g : G) • T₁ = T₂ := by
  rintro ⟨g, hg⟩
  apply h₂
  rw [← hg]
  exact (edgeStabilizer_smul_le_join_iff D A B T₁ g).mpr h₁

/-- The two triangle representatives supplied by the local A₅ calculation
are in distinct ambient setwise edge-stabilizer orbits: the first lies
inside the A₄ edge join, and the second generates A₅ with the endpoints. -/
theorem triangle_types_not_conjugate_of_a5_triple (D : Seed G)
    (A B T₁ T₂ : D.Vertex) (hAB : D.graph.Adj A B)
    (h₁ : T₁.val ≤ A.val ⊔ B.val)
    (h₂ : Nonempty (↥((A.val ⊔ B.val) ⊔ T₂.val) ≃* alternatingGroup (Fin 5))) :
    ¬ ∃ g : edgeStabilizer G A B, (g : G) • T₁ = T₂ := by
  apply triangle_types_not_conjugate D A B T₁ T₂ h₁
  intro hle
  have hc := Nat.card_congr h₂.some.toEquiv
  rw [sup_eq_left.mpr hle, card_join_of_adj D hAB, nat_card_alternatingGroup] at hc
  norm_num at hc

/-- An A₅ pointwise edge fixer fixes every vertex contained in the endpoint
join individually. In particular its two internal third vertices cannot
form one orbit under that pointwise fixer. -/
theorem edgeFixer_fixes_vertex_in_join (D : Seed G) (A B V : D.Vertex)
    (hF : Nonempty (edgeFixer G A B ≃* alternatingGroup (Fin 5)))
    (hV : V.val ≤ A.val ⊔ B.val) (g : edgeFixer G A B) :
    (g : G) • V = V := by
  apply mem_stabilizer_iff.mp
  rw [D.stabilizer_eq_normalizer]
  apply centralizer_le_normalizer _
  have hg : (g : G) ∈ centralizer ((A.val ⊔ B.val : Subgroup G) : Set G) := by
    rw [← edgeFixer_eq_centralizer_join_of_alternatingFive D A B hF]
    exact g.property
  exact centralizer_le hV hg

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal

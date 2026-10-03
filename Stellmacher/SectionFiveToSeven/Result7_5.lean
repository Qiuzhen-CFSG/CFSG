module

public import Stellmacher.SectionFiveToSeven.Result7_4
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Stellmacher’s Lemma 7.5

This module proves the commuting-endpoint case of the critical-path argument.
Lemma 7.3 at the final edge cannot take its centralizer branch: Sylow
conjugacy would put a conjugate of `Z_a` in `Q_{a′}`, and invariance of
`Q_{a′}` would contradict criticality. Thus `Z_{a′}` is the omega-one
center of its stabilizer. Edge transitivity then puts `a′` in the orbit of
`a+1`; the other endpoint alignment would combine centrality with Lemma
7.4(c) and force `S = Q_a`. Equivariance of stabilizers, Sylow-center
joins, and neighborhoods transports the omega-one-center equality, while the
two coset families give the odd parity of the critical distance.  The accepted
endpoint alignment is also exported as a narrow corollary for the conjugation
argument in Lemma 7.6. The stabilizer invariance of the center subgroup and
the neighbor-center join is exported for the same subsequent argument;
center equivariance supports the endpoint comparison in Lemma 7.7.
The exact stabilizer and adjacency covariance proofs are also exported for
the backward-neighbor construction and critical-pair shifts in (8.2).
Neighbor-center join covariance is exported as `v_act` to transport elementary
abelianness between the aligned endpoints in the second (9.3) extraction.

For the residual assertion, `Q_a ∩ C_G(E_a)` is normal in the Sylow
2-subgroup `S`. A nontrivial such subgroup would meet `Z(S)` nontrivially;
because `E_a S = G_a`, this gives a nontrivial element of `Z(G_a)`,
contrary to Lemma 7.3(d). When the distance exceeds one, it is at least
three. Any two neighbors of a vertex are then at distance below the critical
distance, so their center subgroups centralize one another. Their closure is
therefore elementary abelian; Lemma 7.4(a,b) and invariance of `V_d` give
the two quadratic actions.

Source: `refs/latex/stellmacher-n-group.tex`, Lemma (7.5), corresponding to
Journal of Algebra 190 (1997), pp. 34–35.
-/

open scoped Pointwise IsMulCommutative

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u v

public structure LemmaSevenFiveConclusion
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ) : Prop where
  odd_distance : Odd cp.length
  next_center : z Γ cp.firstStep = omegaOneCenter S ∧
    z Γ cp.firstStep = omegaOneCenter (stabilizer Γ cp.firstStep)
  centralizer_residual :
    q Γ cp.a ⊓ Subgroup.centralizer (e Γ cp.a : Set G) = ⊥
  start_center_trivial : Subgroup.center (stabilizer Γ cp.a) = ⊥
  longer_case :
    1 < cp.length →
      IsElementaryAbelian 2 (v Γ cp.firstStep) ∧
      IsQuadraticOn (v Γ cp.firstStep) (v Γ cp.a') ∧
      IsQuadraticOn (v Γ cp.a') (v Γ cp.firstStep)


private theorem omega₁_map_equiv_75
    {A B : Type u} [Group A] [Group B] (f : A ≃* B) :
    (omega₁ (G := A) (p := 2)).map f.toMonoidHom =
      omega₁ (G := B) (p := 2) := by
  let X : Set A := {x | x ^ (2 ^ 1) = 1}
  let Y : Set B := {y | y ^ (2 ^ 1) = 1}
  have hXY : f '' X = Y := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ^ (2 ^ 1) = 1 := hx
      simpa [Y] using congrArg f.toMonoidHom hx'
    · intro hy
      refine ⟨f.symm y, ?_, by simp⟩
      have hy' : y ^ (2 ^ 1) = 1 := hy
      simpa [X] using congrArg f.symm.toMonoidHom hy'
  change (Subgroup.closure X).map f.toMonoidHom = Subgroup.closure Y
  rw [MonoidHom.map_closure]
  exact congrArg Subgroup.closure hXY

private theorem omegaOneCenter_map_equiv_75
    {G G' : Type u} [Group G] [Group G'] (f : G ≃* G') (A : Subgroup G) :
    omegaOneCenter (A.map f.toMonoidHom) =
      (omegaOneCenter A).map f.toMonoidHom := by
  let fA : A ≃* A.map f.toMonoidHom :=
    A.equivMapOfInjective f.toMonoidHom f.injective
  let fZ : Subgroup.center A ≃* Subgroup.center (A.map f.toMonoidHom) :=
    Subgroup.centerCongr fA
  have hOmega := omega₁_map_equiv_75 fZ
  symm
  unfold omegaOneCenter
  rw [← hOmega]
  simp only [Subgroup.map_map]
  apply congrArg (fun g : Subgroup.center A →* G' ↦
    (omega₁ (G := Subgroup.center A) (p := 2)).map g)
  ext x
  rfl

private noncomputable def sylowOmegaJoin_75
    {G : Type u} [Group G] (P : Subgroup G) : Subgroup G :=
  sSup {Z : Subgroup G | ∃ T : Sylow 2 P,
    Z = omegaOneCenter ((T : Subgroup P).map P.subtype)}

private theorem sylowAmbient_map_equiv_75
    {G G' : Type u} [Group G] [Finite G] [Group G'] (f : G ≃* G')
    (P : Subgroup G) (T : Sylow 2 P) :
    let fP : P ≃* P.map f.toMonoidHom :=
      P.equivMapOfInjective f.toMonoidHom f.injective
    let hfP : Function.Surjective fP.toMonoidHom := fP.surjective
    let T' : Sylow 2 (P.map f.toMonoidHom) :=
      T.mapSurjective (f := fP.toMonoidHom) hfP
    ((T' : Subgroup (P.map f.toMonoidHom)).map
        (P.map f.toMonoidHom).subtype) =
      (((T : Subgroup P).map P.subtype).map f.toMonoidHom) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  dsimp only
  change (((T : Subgroup P).map _).map _) = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem sylowOmegaJoin_map_equiv_75
    {G G' : Type u} [Group G] [Finite G] [Group G'] (f : G ≃* G')
    (P : Subgroup G) :
    sylowOmegaJoin_75 (P.map f.toMonoidHom) =
      (sylowOmegaJoin_75 P).map f.toMonoidHom := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · unfold sylowOmegaJoin_75
    rw [sSup_eq_iSup]
    refine iSup_le fun W ↦ ?_
    refine iSup_le fun hW ↦ ?_
    rcases hW with ⟨T', rfl⟩
    let fP : P ≃* P.map f.toMonoidHom :=
      P.equivMapOfInjective f.toMonoidHom f.injective
    let hfP : Function.Surjective fP.toMonoidHom := fP.surjective
    obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective
      (f := fP.toMonoidHom) hfP 2 T'
    rw [← hT, sylowAmbient_map_equiv_75,
      omegaOneCenter_map_equiv_75]
    exact Subgroup.map_mono (le_sSup ⟨T, rfl⟩)
  · unfold sylowOmegaJoin_75
    rw [sSup_eq_iSup, Subgroup.map_iSup]
    refine iSup_le fun W ↦ ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hW ↦ ?_
    rcases hW with ⟨T, rfl⟩
    let fP : P ≃* P.map f.toMonoidHom :=
      P.equivMapOfInjective f.toMonoidHom f.injective
    let hfP : Function.Surjective fP.toMonoidHom := fP.surjective
    let T' : Sylow 2 (P.map f.toMonoidHom) :=
      T.mapSurjective (f := fP.toMonoidHom) hfP
    rw [← omegaOneCenter_map_equiv_75, ← sylowAmbient_map_equiv_75]
    exact le_sSup ⟨T', rfl⟩

private theorem mem_stabilizer_iff_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    {g : G} {d : Gamma.Vertex} :
    g ∈ stabilizer Gamma d ↔ Gamma.act g d = d := by
  have hdef : (stabilizer Gamma d : Set G) =
      {x | Gamma.act x d = d} := Gamma.stabilizer_def d
  exact Set.ext_iff.mp hdef g

private theorem stabilizer_act_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) (d : Gamma.Vertex) :
    stabilizer Gamma (Gamma.act g d) =
      conjugateBy (stabilizer Gamma d) g⁻¹ := by
  ext x
  rw [mem_stabilizer_iff_75, conjugateBy, Subgroup.mem_map_equiv,
    mem_stabilizer_iff_75]
  simp only [MulAut.conj_symm_apply, inv_inv]
  constructor
  · intro hx
    calc
      Gamma.act (g * x * g⁻¹) d =
          Gamma.act g⁻¹ (Gamma.act (g * x) d) := Gamma.act_mul _ _ _
      _ = Gamma.act g⁻¹ (Gamma.act x (Gamma.act g d)) := by
        rw [Gamma.act_mul]
      _ = Gamma.act g⁻¹ (Gamma.act g d) := by rw [hx]
      _ = Gamma.act (g * g⁻¹) d := (Gamma.act_mul _ _ _).symm
      _ = d := by rw [mul_inv_cancel, Gamma.act_one]
  · intro hx
    calc
      Gamma.act x (Gamma.act g d) = Gamma.act (g * x) d :=
        (Gamma.act_mul _ _ _).symm
      _ = Gamma.act g (Gamma.act (g * x * g⁻¹) d) := by
        rw [← Gamma.act_mul]
        simp [mul_assoc]
      _ = Gamma.act g d := by rw [hx]

private theorem z_act_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) (d : Gamma.Vertex) :
    z Gamma (Gamma.act g d) =
      (z Gamma d).map (MulAut.conj g⁻¹).toMonoidHom := by
  simp only [z, Gamma.zAt_def]
  change sylowOmegaJoin_75 (stabilizer Gamma (Gamma.act g d)) =
    (sylowOmegaJoin_75 (stabilizer Gamma d)).map
      (MulAut.conj g⁻¹).toMonoidHom
  rw [stabilizer_act_75]
  exact sylowOmegaJoin_map_equiv_75 (MulAut.conj g⁻¹)
    (stabilizer Gamma d)

private theorem coset₁_eq_of_mem_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    {g k : G} (hk : k ∈ MulOpposite.op g • (P1 : Set G)) :
    Gamma.coset₁ g = Gamma.coset₁ k := by
  rw [Gamma.coset₁_eq_iff]
  rcases Set.mem_smul_set.mp hk with ⟨p, hp, rfl⟩
  change MulOpposite.op g • (P1 : Set G) =
    MulOpposite.op (p * g) • (P1 : Set G)
  rw [show MulOpposite.op (p * g) =
      MulOpposite.op g * MulOpposite.op p by rfl,
    mul_smul, op_smul_coe_set hp]

private theorem coset₂_eq_of_mem_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    {g k : G} (hk : k ∈ MulOpposite.op g • (P2 : Set G)) :
    Gamma.coset₂ g = Gamma.coset₂ k := by
  rw [Gamma.coset₂_eq_iff]
  rcases Set.mem_smul_set.mp hk with ⟨p, hp, rfl⟩
  change MulOpposite.op g • (P2 : Set G) =
    MulOpposite.op (p * g) • (P2 : Set G)
  rw [show MulOpposite.op (p * g) =
      MulOpposite.op g * MulOpposite.op p by rfl,
    mul_smul, op_smul_coe_set hp]

private theorem edge_common_rep_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    {d l : Gamma.Vertex} (hdl : Gamma.adjacent d l) :
    ∃ k : G,
      (d = Gamma.coset₁ k ∧ l = Gamma.coset₂ k) ∨
      (d = Gamma.coset₂ k ∧ l = Gamma.coset₁ k) := by
  rcases Gamma.coset₁_surjective d with ⟨g, hd | hd⟩ <;>
    rcases Gamma.coset₁_surjective l with ⟨h, hl | hl⟩
  · exact (Gamma.no_adj_coset₁_coset₁ g h (hd ▸ hl ▸ hdl)).elim
  · have hinter := (Gamma.adj_cosets g h).mp (hd ▸ hl ▸ hdl)
    rcases Set.nonempty_iff_ne_empty.mpr hinter with ⟨k, hkg, hkh⟩
    exact ⟨k, Or.inl ⟨hd.trans (coset₁_eq_of_mem_75 Gamma hkg),
      hl.trans (coset₂_eq_of_mem_75 Gamma hkh)⟩⟩
  · have hinter := (Gamma.adj_cosets h g).mp
      (Gamma.adjacent_symm (hd ▸ hl ▸ hdl))
    rcases Set.nonempty_iff_ne_empty.mpr hinter with ⟨k, hkh, hkg⟩
    exact ⟨k, Or.inr ⟨hd.trans (coset₂_eq_of_mem_75 Gamma hkg),
      hl.trans (coset₁_eq_of_mem_75 Gamma hkh)⟩⟩
  · exact (Gamma.no_adj_coset₂_coset₂ g h (hd ▸ hl ▸ hdl)).elim

private theorem adjacent_act_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) {d l : Gamma.Vertex} (hdl : Gamma.adjacent d l) :
    Gamma.adjacent (Gamma.act g d) (Gamma.act g l) := by
  rcases edge_common_rep_75 Gamma hdl with ⟨k, hk | hk⟩
  · rw [hk.1, hk.2, Gamma.act_coset₁, Gamma.act_coset₂,
      Gamma.adj_cosets]
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨k * g,
      Set.mem_smul_set.mpr ⟨1, P1.one_mem, by simp⟩,
      Set.mem_smul_set.mpr ⟨1, P2.one_mem, by simp⟩⟩
  · apply Gamma.adjacent_symm
    rw [hk.1, hk.2, Gamma.act_coset₂, Gamma.act_coset₁,
      Gamma.adj_cosets]
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨k * g,
      Set.mem_smul_set.mpr ⟨1, P1.one_mem, by simp⟩,
      Set.mem_smul_set.mpr ⟨1, P2.one_mem, by simp⟩⟩

private theorem adjacent_act_iff_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) {d l : Gamma.Vertex} :
    Gamma.adjacent (Gamma.act g d) (Gamma.act g l) ↔
      Gamma.adjacent d l := by
  constructor
  · intro h
    have h' := adjacent_act_75 Gamma g⁻¹ h
    have hd : Gamma.act g⁻¹ (Gamma.act g d) = d := by
      calc
        Gamma.act g⁻¹ (Gamma.act g d) =
            Gamma.act (g * g⁻¹) d := (Gamma.act_mul _ _ _).symm
        _ = Gamma.act 1 d := by rw [mul_inv_cancel]
        _ = d := Gamma.act_one d
    have hl : Gamma.act g⁻¹ (Gamma.act g l) = l := by
      calc
        Gamma.act g⁻¹ (Gamma.act g l) =
            Gamma.act (g * g⁻¹) l := (Gamma.act_mul _ _ _).symm
        _ = Gamma.act 1 l := by rw [mul_inv_cancel]
        _ = l := Gamma.act_one l
    rwa [hd, hl] at h'
  · exact adjacent_act_75 Gamma g

private theorem mem_neighborhood_iff_adjacent_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    {d l : Gamma.Vertex} :
    l ∈ neighborhood Gamma d ↔ Gamma.adjacent d l := by
  rw [neighborhood, Gamma.neighbors_def]
  change Gamma.distance l d = 1 ↔ Gamma.adjacent d l
  rw [Gamma.distance_symm]
  constructor
  · intro hdist
    rcases Gamma.distance_path d l with ⟨f, hstart, hend, hpath⟩
    have hpos : 0 < Gamma.distance d l := hdist ▸ Nat.zero_lt_one
    have hedge := hpath ⟨0, hpos⟩
    have hi : (⟨0, hpos⟩ : Fin (Gamma.distance d l)).succ =
        ⟨Gamma.distance d l, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp [hdist]
    rw [hi, hend] at hedge
    simpa [hstart] using hedge
  · intro hdl
    let f : Fin 2 → Gamma.Vertex := ![d, l]
    have hpath : ∀ i : Fin 1,
        Gamma.adjacent (f i.castSucc) (f i.succ) := by
      intro i
      fin_cases i
      exact hdl
    have hle : Gamma.distance d l ≤ 1 := by
      simpa [f] using Gamma.distance_le_of_path 1 f hpath
    have hne : Gamma.distance d l ≠ 0 := by
      intro hzero
      have hEq := (Gamma.distance_zero_iff d l).mp hzero
      subst l
      rcases Gamma.coset₁_surjective d with ⟨k, hk | hk⟩
      · exact Gamma.no_adj_coset₁_coset₁ k k (hk ▸ hdl)
      · exact Gamma.no_adj_coset₂_coset₂ k k (hk ▸ hdl)
    omega

private theorem neighborhood_act_iff_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) {d l : Gamma.Vertex} :
    Gamma.act g l ∈ neighborhood Gamma (Gamma.act g d) ↔
      l ∈ neighborhood Gamma d := by
  rw [mem_neighborhood_iff_adjacent_75,
    mem_neighborhood_iff_adjacent_75, adjacent_act_iff_75]

private theorem v_act_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) (d : Gamma.Vertex) :
    v Gamma (Gamma.act g d) =
      (v Gamma d).map (MulAut.conj g⁻¹).toMonoidHom := by
  apply le_antisymm
  · rw [v, Gamma.vAt_def]
    refine sSup_le fun Z hZ ↦ ?_
    rcases hZ with ⟨l, hl, rfl⟩
    let l₀ := Gamma.act g⁻¹ l
    have hl₀ : l₀ ∈ neighborhood Gamma d := by
      have hmem := (neighborhood_act_iff_75 Gamma g⁻¹
        (d := Gamma.act g d) (l := l)).2 hl
      have hcancel : Gamma.act g⁻¹ (Gamma.act g d) = d := by
        calc
          Gamma.act g⁻¹ (Gamma.act g d) =
              Gamma.act (g * g⁻¹) d := (Gamma.act_mul _ _ _).symm
          _ = Gamma.act 1 d := by rw [mul_inv_cancel]
          _ = d := Gamma.act_one d
      rwa [hcancel] at hmem
    have hlact : Gamma.act g l₀ = l := by
      calc
        Gamma.act g l₀ = Gamma.act g (Gamma.act g⁻¹ l) := rfl
        _ = Gamma.act (g⁻¹ * g) l := (Gamma.act_mul _ _ _).symm
        _ = Gamma.act 1 l := by rw [inv_mul_cancel]
        _ = l := Gamma.act_one l
    rw [← hlact]
    have hzle : z Gamma l₀ ≤ v Gamma d := by
      rw [v, Gamma.vAt_def]
      exact le_sSup ⟨l₀, hl₀, rfl⟩
    exact (le_of_eq (z_act_75 Gamma g l₀)).trans
      (Subgroup.map_mono hzle)
  · rw [v, Gamma.vAt_def, sSup_eq_iSup, Subgroup.map_iSup]
    refine iSup_le fun Z ↦ ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hZ ↦ ?_
    rcases hZ with ⟨l, hl, rfl⟩
    change (z Gamma l).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Gamma.vAt (Gamma.act g d)
    rw [← z_act_75]
    have hzle : z Gamma (Gamma.act g l) ≤
        v Gamma (Gamma.act g d) := by
      rw [v, Gamma.vAt_def]
      exact le_sSup ⟨Gamma.act g l,
        (neighborhood_act_iff_75 Gamma g).2 hl, rfl⟩
    exact hzle

private theorem stabilizer_le_normalizer_z_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (d : Gamma.Vertex) :
    stabilizer Gamma d ≤ Subgroup.normalizer (z Gamma d : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hfix : Gamma.act g⁻¹ d = d := by
    have hgfix := (mem_stabilizer_iff_75 Gamma).1 hg
    calc
      Gamma.act g⁻¹ d = Gamma.act g⁻¹ (Gamma.act g d) := by rw [hgfix]
      _ = Gamma.act (g * g⁻¹) d := (Gamma.act_mul _ _ _).symm
      _ = d := by simp [Gamma.act_one]
  simpa [hfix] using (z_act_75 Gamma g⁻¹ d).symm

private theorem stabilizer_le_normalizer_q_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (d : Gamma.Vertex) :
    stabilizer Gamma d ≤ Subgroup.normalizer (q Gamma d : Set G) := by
  rw [q, Gamma.twoCoreAt_def]
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 (stabilizer Gamma d)))).mp
  rw [← Subgroup.comap_subtype,
    Subgroup.comap_map_eq_self_of_injective
      (stabilizer Gamma d).subtype_injective]
  exact (inferInstance : (pCore 2 (stabilizer Gamma d)).Normal)

private theorem twoResidualSubgroup_normal_75
    {G : Type u} [Group G] (P : Subgroup G) :
    (twoResidualSubgroup P).Normal := by
  unfold twoResidualSubgroup
  rw [sInf_eq_iInf]
  exact Subgroup.normal_iInf_normal (fun N ↦
    Subgroup.normal_iInf_normal (fun hN ↦ hN.1))

private theorem stabilizer_le_normalizer_e_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (d : Gamma.Vertex) :
    stabilizer Gamma d ≤ Subgroup.normalizer (e Gamma d : Set G) := by
  rw [CosetGraphContext.e, Gamma.twoResidualAt_def, twoResidualIn,
    twoResidualAmbient]
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (twoResidualSubgroup (stabilizer Gamma d)))).mp
  rw [subgroupOf_map_subtype_eq]
  exact twoResidualSubgroup_normal_75 (stabilizer Gamma d)

private theorem stabilizer_le_normalizer_v_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (d : Gamma.Vertex) :
    stabilizer Gamma d ≤ Subgroup.normalizer (v Gamma d : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hfix : Gamma.act g⁻¹ d = d := by
    have hgfix := (mem_stabilizer_iff_75 Gamma).1 hg
    calc
      Gamma.act g⁻¹ d = Gamma.act g⁻¹ (Gamma.act g d) := by rw [hgfix]
      _ = Gamma.act (g * g⁻¹) d := (Gamma.act_mul _ _ _).symm
      _ = d := by simp [Gamma.act_one]
  simpa [hfix] using (v_act_75 Gamma g⁻¹ d).symm

private theorem omegaOneCenter_isElementaryAbelian_75
    {G : Type u} [Group G] (A : Subgroup G) :
    IsElementaryAbelian 2 (omegaOneCenter A) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinner : IsElementaryAbelian 2
      (omega₁ (G := Subgroup.center A) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative (p := 2)
      (Subgroup.center A)
  have hcenter : IsElementaryAbelian 2
      ((omega₁ (G := Subgroup.center A) (p := 2)).map
        (Subgroup.center A).subtype) :=
    IsElementaryAbelian.map (p := 2)
      (A := omega₁ (G := Subgroup.center A) (p := 2))
      (Subgroup.center A).subtype
  exact IsElementaryAbelian.map (p := 2)
    (A := (omega₁ (G := Subgroup.center A) (p := 2)).map
      (Subgroup.center A).subtype) A.subtype

private theorem omegaOneCenter_le_centerAmbient_75
    {G : Type u} [Group G] (A : Subgroup G) :
    omegaOneCenter A ≤ (Subgroup.center A).map A.subtype := by
  unfold omegaOneCenter
  exact Subgroup.map_mono (Subgroup.map_subtype_le _)

private theorem centerAmbient_le_centralizer_75
    {G : Type u} [Group G] (A : Subgroup G) :
    (Subgroup.center A).map A.subtype ≤
      Subgroup.centralizer (A : Set G) := by
  intro x hx
  obtain ⟨xc, hxc, rfl⟩ := hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let ya : A := ⟨y, hy⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ya)

private theorem z_isPGroup_of_neighbor_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} {Gamma : CosetGraphContext G S P1 P2}
    (h73 : LemmaSevenThreeConclusion Gamma)
    {d l : Gamma.Vertex} (hl : l ∈ neighborhood Gamma d) :
    IsPGroup 2 (z Gamma d) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 (omegaOneCenter (q Gamma d)) :=
    omegaOneCenter_isElementaryAbelian_75 (q Gamma d)
  have hp : IsPGroup 2 (omegaOneCenter (q Gamma d)) :=
    IsElementaryAbelian.isPGroup 2 (omegaOneCenter (q Gamma d))
  have hle := h73.center_core d l hl
  exact (hp.to_subgroup ((z Gamma d).subgroupOf
    (omegaOneCenter (q Gamma d)))).of_equiv
      (Subgroup.subgroupOfEquivOfLe hle)

private theorem sylowAmbient_smul_75
    {G : Type u} [Group G] (P : Subgroup G)
    (T : Sylow 2 P) (g : P) :
    (((g • T : Sylow 2 P) : Subgroup P).map P.subtype) =
      (((T : Subgroup P).map P.subtype).map
        (MulAut.conj (g : G)).toMonoidHom) := by
  change (((T : Subgroup P).map
      (MulAut.conj g).toMonoidHom).map P.subtype) = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem exists_conjugate_le_sylow_75
    {G : Type u} [Group G] [Finite G]
    {A W P : Subgroup G} (hAP : A ≤ P) (hAp : IsPGroup 2 A)
    (hWP : IsSylowTwoIn W P) :
    ∃ g : P, A.map (MulAut.conj (g : G)).toMonoidHom ≤ W := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let AP : Subgroup P := A.subgroupOf P
  have hAPp : IsPGroup 2 AP :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAP).symm
  obtain ⟨U, hAU⟩ := hAPp.exists_le_sylow
  obtain ⟨_, T, hTmap⟩ := hWP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P U T
  refine ⟨g, ?_⟩
  have hmap :
      (((U : Subgroup P).map P.subtype).map
        (MulAut.conj (g : G)).toMonoidHom) = W := by
    rw [← sylowAmbient_smul_75, hg, hTmap]
  rw [← hmap]
  exact Subgroup.map_mono <| by
    intro x hx
    let xp : P := ⟨x, hAP hx⟩
    have hxp : xp ∈ AP := hx
    exact Subgroup.mem_map_of_mem P.subtype (hAU hxp)

private theorem le_of_map_conj_le_of_normalizes_75
    {G : Type u} [Group G] {A Q P : Subgroup G} (g : P)
    (hmap : A.map (MulAut.conj (g : G)).toMonoidHom ≤ Q)
    (hnorm : P ≤ Subgroup.normalizer (Q : Set G)) : A ≤ Q := by
  intro x hx
  have hxmap : (g : G) * x * (g : G)⁻¹ ∈ Q := by
    apply hmap
    exact Subgroup.mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom hx
  have hginv : (g : G)⁻¹ ∈ P := P.inv_mem g.property
  have hback := (Subgroup.mem_set_normalizer_iff.mp
    (hnorm hginv) ((g : G) * x * (g : G)⁻¹)).1 hxmap
  simpa [mul_assoc] using hback

private theorem isSylowTwoIn_inf_right_75
    {G : Type u} [Group G] [Finite G]
    {S P K : Subgroup G}
    (hSP : IsSylowTwoIn S P) (hSK : S ≤ K) :
    IsSylowTwoIn S (P ⊓ K) := by
  classical
  obtain ⟨hSleP, T, hTmap⟩ := hSP
  let I : Subgroup G := P ⊓ K
  let J : Subgroup P := I.subgroupOf P
  have hTJ : (T : Subgroup P) ≤ J := by
    intro t ht
    have htS : (t : G) ∈ S := by
      rw [← hTmap]
      exact Subgroup.mem_map_of_mem P.subtype ht
    exact ⟨hSleP htS, hSK htS⟩
  let TJ : Sylow 2 J := T.subtype hTJ
  let eJI : J ≃* I :=
    { toFun := fun x ↦ ⟨(x : G), x.property⟩
      invFun := fun x ↦ ⟨⟨(x : G), x.property.1⟩, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  let TI : Sylow 2 I :=
    TJ.mapSurjective (f := eJI.toMonoidHom) eJI.surjective
  refine ⟨le_inf hSleP hSK, TI, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hx
    change i ∈ (TJ : Subgroup J).map eJI.toMonoidHom at hi
    obtain ⟨j, hj, hji⟩ := hi
    have hjT : (j : P) ∈ T := hj
    rw [← hTmap]
    have : (i : G) = (j : G) := congrArg Subtype.val hji.symm
    exact ⟨(j : P), hjT, this.symm⟩
  · intro hx
    rw [← hTmap] at hx
    obtain ⟨t, ht, htx⟩ := hx
    have htS : (t : G) ∈ S := by
      rw [← hTmap]
      exact Subgroup.mem_map_of_mem P.subtype ht
    let j : J := ⟨t, hTJ ht⟩
    let i : I := eJI j
    refine ⟨i, ?_, ?_⟩
    · change i ∈ (TJ : Subgroup J).map eJI.toMonoidHom
      exact Subgroup.mem_map_of_mem eJI.toMonoidHom ht
    · exact htx

private theorem edge_sylow_data_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    IsSylowTwoIn S (stabilizer Gamma cp.a) ∧
      IsSylowTwoIn S (stabilizer Gamma cp.firstStep) := by
  rcases cp.edge_stabilizers_are_P with hedge | hedge
  · rw [hedge.1, hedge.2]
    exact ⟨h.P1_mem.1.2.1, h.P2_mem.1.2.1⟩
  · rw [hedge.1, hedge.2]
    exact ⟨h.P2_mem.1.2.1, h.P1_mem.1.2.1⟩

private theorem twoCoreIn_le_sylow_75
    {G : Type u} [Group G] [Finite G]
    {W P : Subgroup G} (hWP : IsSylowTwoIn W P) :
    twoCoreIn P ≤ W := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, T, hTmap⟩ := hWP
  calc
    twoCoreIn P = (pCore 2 P).map P.subtype := rfl
    _ ≤ (T : Subgroup P).map P.subtype := Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := P)).le_sylow_of_normal T)
    _ = W := hTmap

private theorem twoResidualSubgroup_eq_hktPResidual_75
    {G : Type u} [Group G] [Finite G] (P : Subgroup G) :
    twoResidualSubgroup P = BenderSuzuki.External.hktPResidual 2 P := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRnormal : (BenderSuzuki.External.hktPResidual 2 P).Normal :=
    BenderSuzuki.External.hktPResidual_normal
  let _ : (BenderSuzuki.External.hktPResidual 2 P).Normal := hRnormal
  apply le_antisymm
  · rw [twoResidualSubgroup]
    apply sInf_le
    refine ⟨hRnormal, ?_⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp
      (BenderSuzuki.External.hktPResidual_quotient_isPGroup
        (q := 2) (Q := P))
    exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  · intro x hx
    rw [twoResidualSubgroup, Subgroup.mem_sInf]
    intro N hN
    let _ : N.Normal := hN.1
    apply BenderSuzuki.External.hktPResidual_le N hN.1 ?_ hx
    rw [IsPGroup.iff_card]
    obtain ⟨n, hn⟩ := hN.2
    exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩

private theorem twoResidualAmbient_sup_sylow_75
    {G : Type u} [Group G] [Finite G]
    {W P : Subgroup G} (hWP : IsSylowTwoIn W P) :
    twoResidualAmbient P ⊔ W = P := by
  classical
  obtain ⟨_, T, hTmap⟩ := hWP
  let R : Subgroup P := BenderSuzuki.External.hktPResidual 2 P
  have hRnormal : R.Normal :=
    BenderSuzuki.External.hktPResidual_normal
  let _ : R.Normal := hRnormal
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRTtop : R ⊔ (T : Subgroup P) = ⊤ := by
    let qR : P →* P ⧸ R := QuotientGroup.mk' R
    have hquotR : IsPGroup 2 (P ⧸ R) :=
      BenderSuzuki.External.hktPResidual_quotient_isPGroup
    let Tbar : Sylow 2 (P ⧸ R) :=
      T.mapSurjective (QuotientGroup.mk'_surjective R)
    have hTbarTop : (Tbar : Subgroup (P ⧸ R)) = ⊤ := by
      symm
      exact Tbar.is_maximal' (hquotR.to_subgroup ⊤) le_top
    have hmapT : (T : Subgroup P).map qR = ⊤ := by
      simpa [Tbar, qR] using hTbarTop
    rw [sup_comm]
    calc
      (T : Subgroup P) ⊔ R = (T : Subgroup P) ⊔ qR.ker := by
        rw [QuotientGroup.ker_mk']
      _ = ((T : Subgroup P).map qR).comap qR :=
        (Subgroup.comap_map_eq qR (T : Subgroup P)).symm
      _ = ⊤ := by rw [hmapT]; simp
  have hmapTop : ((R ⊔ (T : Subgroup P)).map P.subtype) = P := by
    rw [hRTtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [Subgroup.map_sup, hTmap] at hmapTop
  change (twoResidualSubgroup P).map P.subtype ⊔ W = P
  rw [twoResidualSubgroup_eq_hktPResidual_75]
  exact hmapTop

private theorem endpoint_q_ne_S_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    q Gamma cp.a ≠ S ∧ q Gamma cp.firstStep ≠ S := by
  rcases cp.edge_stabilizers_are_P with hedge | hedge
  · constructor
    · intro heq
      apply h.P1_mem.1.2.2.2
      rw [q, Gamma.twoCoreAt_def] at heq
      change twoCoreIn (stabilizer Gamma cp.a) = S at heq
      rw [hedge.1] at heq
      exact heq.symm
    · intro heq
      apply h.P2_mem.1.2.2.2
      rw [q, Gamma.twoCoreAt_def] at heq
      change twoCoreIn (stabilizer Gamma cp.firstStep) = S at heq
      rw [hedge.2] at heq
      exact heq.symm
  · constructor
    · intro heq
      apply h.P2_mem.1.2.2.2
      rw [q, Gamma.twoCoreAt_def] at heq
      change twoCoreIn (stabilizer Gamma cp.a) = S at heq
      rw [hedge.1] at heq
      exact heq.symm
    · intro heq
      apply h.P1_mem.1.2.2.2
      rw [q, Gamma.twoCoreAt_def] at heq
      change twoCoreIn (stabilizer Gamma cp.firstStep) = S at heq
      rw [hedge.2] at heq
      exact heq.symm

private theorem last_edge_adjacent_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    Gamma.adjacent
      (cp.path ⟨cp.length - 1, by omega⟩) cp.a' := by
  let k : Fin cp.length :=
    ⟨cp.length - 1, Nat.sub_lt cp.length_pos Nat.zero_lt_one⟩
  have hkSucc : k.succ =
      ⟨cp.length, Nat.lt_succ_self _⟩ := by
    apply Fin.ext
    simp [k]
    have := cp.length_pos
    omega
  have hp := cp.path_adj k
  rw [hkSucc, cp.path_end] at hp
  simpa [k] using hp

private theorem endpoint_center_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hcomm : ⁅z Gamma cp.a, z Gamma cp.a'⁆ = ⊥) :
    let penult : Gamma.Vertex := cp.path ⟨cp.length - 1, by omega⟩
    let T : Sylow 2 ↥(stabilizer Gamma cp.a' ⊓ stabilizer Gamma penult) :=
      default
    z Gamma cp.a' = omegaOneCenter (stabilizer Gamma cp.a') ∧
      z Gamma cp.a' = omegaOneCenter
        (sylowTwoAmbient
          (stabilizer Gamma cp.a' ⊓ stabilizer Gamma penult) T) := by
  classical
  let h73 := lemma_seven_three h Gamma
  let h74 := lemma_seven_four h Gamma cp
  let penult : Gamma.Vertex := cp.path ⟨cp.length - 1, by omega⟩
  have hpenult : penult ∈ neighborhood Gamma cp.a' :=
    (mem_neighborhood_iff_adjacent_75 Gamma).2
      (Gamma.adjacent_symm (by
        simpa [penult] using last_edge_adjacent_75 Gamma cp))
  let T : Sylow 2 ↥(stabilizer Gamma cp.a' ⊓ stabilizer Gamma penult) :=
    default
  let W : Subgroup G := sylowTwoAmbient
    (stabilizer Gamma cp.a' ⊓ stabilizer Gamma penult) T
  have hWP : IsSylowTwoIn W (stabilizer Gamma cp.a') :=
    (h73.sylow_and_core cp.a' penult hpenult T).1
  have halt := h73.centralizer_alternative cp.a' penult hpenult T
  rcases halt with halt | halt
  · exfalso
    have hfirst : cp.firstStep ∈ neighborhood Gamma cp.a :=
      (mem_neighborhood_iff_adjacent_75 Gamma).2 cp.firstStep_adj
    have hZaP : IsPGroup 2 (z Gamma cp.a) :=
      z_isPGroup_of_neighbor_75 h73 hfirst
    have hZa_le_end : z Gamma cp.a ≤ stabilizer Gamma cp.a' :=
      h74.first_containment.1.trans h74.first_containment.2
    obtain ⟨g, hgW⟩ := exists_conjugate_le_sylow_75
      hZa_le_end hZaP hWP
    have hZaC : z Gamma cp.a ≤
        Subgroup.centralizer (z Gamma cp.a' : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hnormC : stabilizer Gamma cp.a' ≤
        Subgroup.normalizer
          (Subgroup.centralizer (z Gamma cp.a' : Set G) : Set G) := by
      exact (stabilizer_le_normalizer_z_75 Gamma cp.a').trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.centralizer_le_normalizer
            (z Gamma cp.a' : Set G))).mp inferInstance)
    have hmapC :
        (z Gamma cp.a).map (MulAut.conj (g : G)).toMonoidHom ≤
          Subgroup.centralizer (z Gamma cp.a' : Set G) := by
      calc
        (z Gamma cp.a).map (MulAut.conj (g : G)).toMonoidHom ≤
            (Subgroup.centralizer (z Gamma cp.a' : Set G)).map
              (MulAut.conj (g : G)).toMonoidHom :=
          Subgroup.map_mono hZaC
        _ = Subgroup.centralizer (z Gamma cp.a' : Set G) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormC g.property)
    have hmapQ :
        (z Gamma cp.a).map (MulAut.conj (g : G)).toMonoidHom ≤
          q Gamma cp.a' := by
      rw [← halt]
      exact le_inf hgW hmapC
    have hZaQ : z Gamma cp.a ≤ q Gamma cp.a' :=
      le_of_map_conj_le_of_normalizes_75 g hmapQ
        (stabilizer_le_normalizer_q_75 Gamma cp.a')
    exact cp.critical.2 hZaQ
  · exact halt

private theorem center_eq_of_act_eq_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Gamma : CosetGraphContext G S P1 P2)
    {d l : Gamma.Vertex} (g : G) (hact : Gamma.act g d = l)
    (hl : z Gamma l = omegaOneCenter (stabilizer Gamma l)) :
    z Gamma d = omegaOneCenter (stabilizer Gamma d) := by
  let f : G ≃* G := MulAut.conj g⁻¹
  apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
  calc
    (z Gamma d).map f.toMonoidHom = z Gamma l := by
      rw [← hact]
      exact (z_act_75 Gamma g d).symm
    _ = omegaOneCenter (stabilizer Gamma l) := hl
    _ = omegaOneCenter ((stabilizer Gamma d).map f.toMonoidHom) := by
      rw [← hact, stabilizer_act_75]
      rfl
    _ = (omegaOneCenter (stabilizer Gamma d)).map f.toMonoidHom :=
      omegaOneCenter_map_equiv_75 f (stabilizer Gamma d)

private theorem orbit_and_next_center_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hcomm : ⁅z Gamma cp.a, z Gamma cp.a'⁆ = ⊥) :
    (∃ g : G,
      Gamma.act g cp.a =
        cp.path ⟨cp.length - 1, by omega⟩ ∧
      Gamma.act g cp.firstStep = cp.a') ∧
      z Gamma cp.firstStep = omegaOneCenter S ∧
      z Gamma cp.firstStep = omegaOneCenter
        (stabilizer Gamma cp.firstStep) := by
  classical
  let h71 := lemma_seven_one h Gamma
  let h73 := lemma_seven_three h Gamma
  let h74 := lemma_seven_four h Gamma cp
  have hend := endpoint_center_75 h Gamma cp hcomm
  let penult : Gamma.Vertex := cp.path ⟨cp.length - 1, by omega⟩
  have hlast : Gamma.adjacent penult cp.a' := by
    simpa [penult] using last_edge_adjacent_75 Gamma cp
  obtain ⟨g, hg | hg⟩ :=
    h71.edge_not_vertex_transitive.1 cp.firstStep_adj hlast
  · have hgroup : z Gamma cp.firstStep =
        omegaOneCenter (stabilizer Gamma cp.firstStep) :=
      center_eq_of_act_eq_75 Gamma g hg.2 hend.1
    refine ⟨⟨g, hg.1, hg.2⟩, ?_, hgroup⟩
    have hfirst_mem : cp.a ∈ neighborhood Gamma cp.firstStep :=
      (mem_neighborhood_iff_adjacent_75 Gamma).2
        (Gamma.adjacent_symm cp.firstStep_adj)
    have hSedge : IsSylowTwoIn S
        (stabilizer Gamma cp.firstStep ⊓ stabilizer Gamma cp.a) :=
      isSylowTwoIn_inf_right_75 (edge_sylow_data_75 h Gamma cp).2
        ((edge_sylow_data_75 h Gamma cp).1.1)
    obtain ⟨_, T, hTmap⟩ := hSedge
    change sylowTwoAmbient
      (stabilizer Gamma cp.firstStep ⊓ stabilizer Gamma cp.a) T = S at hTmap
    have halt := h73.centralizer_alternative
      cp.firstStep cp.a hfirst_mem T
    rcases halt with halt | halt
    · exfalso
      have hScentral : S ≤
          Subgroup.centralizer (z Gamma cp.firstStep : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hycentral : y ∈
            Subgroup.centralizer
              (stabilizer Gamma cp.firstStep : Set G) := by
          apply (omegaOneCenter_le_centerAmbient_75 _ |>.trans
            (centerAmbient_le_centralizer_75 _))
          rwa [← hgroup]
        exact (Subgroup.mem_centralizer_iff.mp hycentral x
          ((edge_sylow_data_75 h Gamma cp).2.1 hx)).symm
      have hSq : S = q Gamma cp.firstStep := by
        rw [← halt, hTmap, inf_eq_left.mpr hScentral]
      exact (endpoint_q_ne_S_75 h Gamma cp).2 hSq.symm
    · simpa [hTmap] using halt.2
  · exfalso
    have hgroup : z Gamma cp.a =
        omegaOneCenter (stabilizer Gamma cp.a) :=
      center_eq_of_act_eq_75 Gamma g hg.1 hend.1
    have hScentral : S ≤
        Subgroup.centralizer (z Gamma cp.a : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hycentral : y ∈
          Subgroup.centralizer (stabilizer Gamma cp.a : Set G) := by
        apply (omegaOneCenter_le_centerAmbient_75 _ |>.trans
          (centerAmbient_le_centralizer_75 _))
        rwa [← hgroup]
      exact (Subgroup.mem_centralizer_iff.mp hycentral x
        ((edge_sylow_data_75 h Gamma cp).1.1 hx)).symm
    have hSq : S = q Gamma cp.a := by
      rw [← h74.edge_centralizer, inf_eq_left.mpr hScentral]
    exact (endpoint_q_ne_S_75 h Gamma cp).1 hSq.symm

private def IsTypeOne_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (d : Gamma.Vertex) : Prop := ∃ g : G, d = Gamma.coset₁ g

private theorem coset₁_ne_coset₂_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g k : G) : Gamma.coset₁ g ≠ Gamma.coset₂ k := by
  intro heq
  have hedge : Gamma.adjacent (Gamma.coset₁ g) (Gamma.coset₂ g) := by
    rw [Gamma.adj_cosets]
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨g,
      Set.mem_smul_set.mpr ⟨1, P1.one_mem, by simp⟩,
      Set.mem_smul_set.mpr ⟨1, P2.one_mem, by simp⟩⟩
  exact Gamma.no_adj_coset₂_coset₂ k g (heq ▸ hedge)

private theorem isTypeOne_act_iff_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) (d : Gamma.Vertex) :
    IsTypeOne_75 Gamma (Gamma.act g d) ↔ IsTypeOne_75 Gamma d := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k * g⁻¹, ?_⟩
    calc
      d = Gamma.act g⁻¹ (Gamma.act g d) := by
        rw [← Gamma.act_mul, mul_inv_cancel, Gamma.act_one]
      _ = Gamma.act g⁻¹ (Gamma.coset₁ k) := by rw [hk]
      _ = Gamma.coset₁ (k * g⁻¹) := Gamma.act_coset₁ _ _
  · rintro ⟨k, rfl⟩
    exact ⟨k * g, Gamma.act_coset₁ g k⟩

private theorem isTypeOne_adjacent_iff_not_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    {d l : Gamma.Vertex} (hdl : Gamma.adjacent d l) :
    IsTypeOne_75 Gamma d ↔ ¬ IsTypeOne_75 Gamma l := by
  rcases edge_common_rep_75 Gamma hdl with ⟨k, hk | hk⟩
  · constructor
    · intro _ hl
      rcases hl with ⟨r, hr⟩
      exact coset₁_ne_coset₂_75 Gamma r k (hr.symm.trans hk.2)
    · intro _
      exact ⟨k, hk.1⟩
  · constructor
    · rintro ⟨r, hr⟩
      exact (coset₁_ne_coset₂_75 Gamma r k
        (hr.symm.trans hk.1)).elim
    · intro hnot
      exfalso
      apply hnot
      exact ⟨k, hk.2⟩

private noncomputable def vertexColor_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (d : Gamma.Vertex) : Bool :=
  by
    classical
    exact if IsTypeOne_75 Gamma d then true else false

private theorem vertexColor_act_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) (d : Gamma.Vertex) :
    vertexColor_75 Gamma (Gamma.act g d) = vertexColor_75 Gamma d := by
  classical
  by_cases hd : IsTypeOne_75 Gamma d
  · have hgd := (isTypeOne_act_iff_75 Gamma g d).2 hd
    rw [vertexColor_75, if_pos hgd, vertexColor_75, if_pos hd]
  · have hgd : ¬ IsTypeOne_75 Gamma (Gamma.act g d) := by
      exact fun h ↦ hd ((isTypeOne_act_iff_75 Gamma g d).1 h)
    rw [vertexColor_75, if_neg hgd, vertexColor_75, if_neg hd]

private theorem vertexColor_adjacent_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    {d l : Gamma.Vertex} (hdl : Gamma.adjacent d l) :
    vertexColor_75 Gamma l = !(vertexColor_75 Gamma d) := by
  classical
  have hiff := isTypeOne_adjacent_iff_not_75 Gamma hdl
  by_cases hd : IsTypeOne_75 Gamma d
  · have hl : ¬ IsTypeOne_75 Gamma l := hiff.mp hd
    rw [vertexColor_75, if_neg hl, vertexColor_75, if_pos hd]
    rfl
  · have hl : IsTypeOne_75 Gamma l := by
      by_contra hnl
      exact hd (hiff.mpr hnl)
    rw [vertexColor_75, if_pos hl, vertexColor_75, if_neg hd]
    rfl

private theorem path_vertexColor_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (n : ℕ) (f : Fin (n + 1) → Gamma.Vertex)
    (hadj : ∀ i : Fin n, Gamma.adjacent (f i.castSucc) (f i.succ))
    (i : ℕ) (hi : i ≤ n) :
    vertexColor_75 Gamma (f ⟨i, hi.trans_lt (Nat.lt_succ_self _)⟩) =
      if i.bodd then !(vertexColor_75 Gamma (f 0))
      else vertexColor_75 Gamma (f 0) := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hin : i < n := by omega
      let k : Fin n := ⟨i, hin⟩
      have hedge : Gamma.adjacent
          (f ⟨i, by omega⟩) (f ⟨i + 1, by omega⟩) := by
        convert hadj k using 1 <;> congr 1
      rw [vertexColor_adjacent_75 Gamma hedge,
        ih (Nat.le_of_lt hin), Nat.bodd_succ]
      cases i.bodd <;> cases vertexColor_75 Gamma (f 0) <;> rfl

private theorem odd_distance_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hcomm : ⁅z Gamma cp.a, z Gamma cp.a'⁆ = ⊥) :
    Odd cp.length := by
  classical
  obtain ⟨⟨g, _, hg⟩, _⟩ := orbit_and_next_center_75 h Gamma cp hcomm
  have horbitColor : vertexColor_75 Gamma cp.a' =
      vertexColor_75 Gamma cp.firstStep := by
    rw [← hg, vertexColor_act_75]
  have hedgeColor : vertexColor_75 Gamma cp.firstStep =
      !(vertexColor_75 Gamma cp.a) :=
    vertexColor_adjacent_75 Gamma cp.firstStep_adj
  have hopposite : vertexColor_75 Gamma cp.a' =
      !(vertexColor_75 Gamma cp.a) := horbitColor.trans hedgeColor
  have hpath := path_vertexColor_75 Gamma cp.length cp.path cp.path_adj
    cp.length le_rfl
  rw [cp.path_end, cp.path_start] at hpath
  rcases Nat.even_or_odd cp.length with heven | hodd
  · have hbodd : cp.length.bodd = false := by
      rcases heven with ⟨k, hk⟩
      rw [hk]
      simp [Nat.bodd_add]
    rw [hbodd] at hpath
    simp only [Bool.false_eq_true, ↓reduceIte] at hpath
    rw [hopposite] at hpath
    cases vertexColor_75 Gamma cp.a <;> simp at hpath
  · exact hodd

private theorem start_center_trivial_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hcomm : ⁅z Gamma cp.a, z Gamma cp.a'⁆ = ⊥) :
    Subgroup.center (stabilizer Gamma cp.a) = ⊥ := by
  have hnext := (orbit_and_next_center_75 h Gamma cp hcomm).2.2
  exact (lemma_seven_three h Gamma).center_neighbor_trivial
    cp.firstStep cp.a
    ((mem_neighborhood_iff_adjacent_75 Gamma).2
      (Gamma.adjacent_symm cp.firstStep_adj)) hnext

private theorem centralizer_residual_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hcomm : ⁅z Gamma cp.a, z Gamma cp.a'⁆ = ⊥) :
    q Gamma cp.a ⊓ Subgroup.centralizer (e Gamma cp.a : Set G) = ⊥ := by
  classical
  let P : Subgroup G := stabilizer Gamma cp.a
  let C : Subgroup G :=
    q Gamma cp.a ⊓ Subgroup.centralizer (e Gamma cp.a : Set G)
  have hSP : IsSylowTwoIn S P := edge_sylow_data_75 h Gamma cp |>.1
  have hqS : q Gamma cp.a ≤ S := by
    rw [q, Gamma.twoCoreAt_def]
    exact twoCoreIn_le_sylow_75 hSP
  have hCS : C ≤ S := inf_le_left.trans hqS
  have hSNormQ : S ≤ Subgroup.normalizer (q Gamma cp.a : Set G) :=
    hSP.1.trans (stabilizer_le_normalizer_q_75 Gamma cp.a)
  have hSNormCentralizer : S ≤ Subgroup.normalizer
      (Subgroup.centralizer (e Gamma cp.a : Set G) : Set G) := by
    exact hSP.1.trans ((stabilizer_le_normalizer_e_75 Gamma cp.a).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer
          (e Gamma cp.a : Set G))).mp inferInstance))
  have hSNormC : S ≤ Subgroup.normalizer (C : Set G) := by
    exact (le_inf hSNormQ hSNormCentralizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  change C = ⊥
  by_contra hCne
  let CS : Subgroup S := C.subgroupOf S
  have hCSnormal : CS.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCS).2 hSNormC
  let _ : CS.Normal := hCSnormal
  have hCSp : IsPGroup 2 S := by
    obtain ⟨_, T, hTmap⟩ := hSP
    rw [← hTmap]
    exact T.isPGroup'.map P.subtype
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 S) := ⟨hCSp⟩
  have hCSne : CS ≠ ⊥ := by
    intro hbot
    apply hCne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    let xs : S := ⟨x, hCS hx⟩
    have hxs : xs ∈ CS := hx
    rw [hbot] at hxs
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxs)
  let _ : Nontrivial CS := (Subgroup.nontrivial_iff_ne_bot CS).2 hCSne
  obtain ⟨x, hxne, hxcenterS⟩ :=
    exists_nontrivial_center_mem_normal (G := S) (N := CS) (p := 2)
  let xG : G := (x : S)
  have hxC : xG ∈ C := x.property
  have hxCentralE : xG ∈
      Subgroup.centralizer (e Gamma cp.a : Set G) := hxC.2
  have hEcentralX : e Gamma cp.a ≤
      Subgroup.centralizer ({xG} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (Subgroup.mem_centralizer_iff.mp hxCentralE y hy).symm
  have hScentralX : S ≤ Subgroup.centralizer ({xG} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    have hcommS := Subgroup.mem_center_iff.mp hxcenterS ⟨y, hy⟩
    exact (congrArg Subtype.val hcommS).symm
  have hPcentralX : P ≤ Subgroup.centralizer ({xG} : Set G) := by
    rw [← twoResidualAmbient_sup_sylow_75 hSP]
    have hEcentralX' : twoResidualAmbient P ≤
        Subgroup.centralizer ({xG} : Set G) := by
      intro y hy
      apply hEcentralX
      rw [CosetGraphContext.e, Gamma.twoResidualAt_def, twoResidualIn]
      exact hy
    exact sup_le hEcentralX' hScentralX
  have hxS : xG ∈ S := hqS hxC.1
  have hxP : xG ∈ P := hSP.1 hxS
  have hxcenterP : (⟨xG, hxP⟩ : P) ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy := Subgroup.mem_centralizer_iff.mp
      (hPcentralX y.property) xG (Set.mem_singleton xG)
    exact Subtype.ext hy.symm
  have hcenter := start_center_trivial_75 h Gamma cp hcomm
  change Subgroup.center P = ⊥ at hcenter
  rw [hcenter] at hxcenterP
  have hxPone : (⟨xG, hxP⟩ : P) = 1 := Subgroup.mem_bot.mp hxcenterP
  apply hxne
  apply Subtype.ext
  apply Subtype.ext
  simpa only [Subgroup.coe_one] using congrArg Subtype.val hxPone

private theorem critical_minimality_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    {d l : Gamma.Vertex} (hdist : Gamma.distance d l < cp.length) :
    z Gamma d ≤ q Gamma l := by
  by_contra hnot
  have hmem : Gamma.distance d l ∈
      {n : ℕ | ∃ x y : Gamma.Vertex,
        Gamma.distance x y = n ∧ ¬ Gamma.zAt x ≤ Gamma.twoCoreAt y} :=
    ⟨d, l, rfl, by simpa [z, q] using hnot⟩
  have hle : cp.length ≤ Gamma.distance d l := by
    calc
      cp.length = sInf {n : ℕ | ∃ x y : Gamma.Vertex,
          Gamma.distance x y = n ∧
            ¬ Gamma.zAt x ≤ Gamma.twoCoreAt y} := by
        rw [← cp.endpoint_distance]
        exact cp.critical.1
      _ ≤ Gamma.distance d l := Nat.sInf_le hmem
  omega

private theorem neighbor_distance_le_two_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Gamma : CosetGraphContext G S P1 P2)
    {d l m : Gamma.Vertex}
    (hl : l ∈ neighborhood Gamma d) (hm : m ∈ neighborhood Gamma d) :
    Gamma.distance l m ≤ 2 := by
  let f : Fin 3 → Gamma.Vertex := ![l, d, m]
  have hadj : ∀ i : Fin 2,
      Gamma.adjacent (f i.castSucc) (f i.succ) := by
    intro i
    fin_cases i
    · exact Gamma.adjacent_symm
        ((mem_neighborhood_iff_adjacent_75 Gamma).1 hl)
    · exact (mem_neighborhood_iff_adjacent_75 Gamma).1 hm
  simpa [f] using Gamma.distance_le_of_path 2 f hadj

private theorem neighbor_centers_le_centralizer_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hlen : 2 < cp.length) {d l m : Gamma.Vertex}
    (hl : l ∈ neighborhood Gamma d) (hm : m ∈ neighborhood Gamma d) :
    z Gamma l ≤ Subgroup.centralizer (z Gamma m : Set G) := by
  let h73 := lemma_seven_three h Gamma
  have hzq : z Gamma l ≤ q Gamma m :=
    critical_minimality_75 Gamma cp
      ((neighbor_distance_le_two_75 Gamma hl hm).trans_lt hlen)
  have hdm : d ∈ neighborhood Gamma m :=
    (mem_neighborhood_iff_adjacent_75 Gamma).2
      (Gamma.adjacent_symm
        ((mem_neighborhood_iff_adjacent_75 Gamma).1 hm))
  have hzmcenter : z Gamma m ≤
      (Subgroup.center (q Gamma m)).map (q Gamma m).subtype :=
    (h73.center_core m d hdm).trans
      (omegaOneCenter_le_centerAmbient_75 (q Gamma m))
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨yc, hyc, hycy⟩ := hzmcenter hy
  let xq : q Gamma m := ⟨x, hzq hx⟩
  have hxy := Subgroup.mem_center_iff.mp hyc xq
  change y * x = x * y
  rw [← hycy]
  exact (congrArg Subtype.val hxy).symm

private def neighborCenterElements_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (d : Gamma.Vertex) : Set G :=
  {x | ∃ l ∈ neighborhood Gamma d, x ∈ z Gamma l}

private theorem v_eq_closure_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Gamma : CosetGraphContext G S P1 P2) (d : Gamma.Vertex) :
    v Gamma d = Subgroup.closure (neighborCenterElements_75 Gamma d) := by
  apply le_antisymm
  · rw [v, Gamma.vAt_def]
    refine sSup_le fun Z hZ ↦ ?_
    rcases hZ with ⟨l, hl, rfl⟩
    intro x hx
    exact Subgroup.subset_closure ⟨l, hl, hx⟩
  · rw [v, Gamma.vAt_def]
    apply (Subgroup.closure_le _).2
    rintro x ⟨l, hl, hx⟩
    have hz : z Gamma l ≤
        sSup {Z : Subgroup G | ∃ m ∈ neighborhood Gamma d,
          Z = z Gamma m} :=
      le_sSup ⟨l, hl, rfl⟩
    exact hz hx

private theorem v_isElementaryAbelian_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hlen : 2 < cp.length) (d : Gamma.Vertex) :
    IsElementaryAbelian 2 (v Gamma d) := by
  classical
  let K : Set G := neighborCenterElements_75 Gamma d
  have hcommK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
    rintro x ⟨l, hl, hx⟩ y ⟨m, hm, hy⟩
    exact (Subgroup.mem_centralizer_iff.mp
      (neighbor_centers_le_centralizer_75 h Gamma cp hlen hl hm hx) y hy).symm
  have hmul : IsMulCommutative (v Gamma d) := by
    rw [v_eq_closure_75]
    exact Subgroup.isMulCommutative_closure hcommK
  let _ : IsMulCommutative (v Gamma d) := hmul
  refine ⟨?_⟩
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  have hxcl : (x : G) ∈ Subgroup.closure K := by
    rw [← v_eq_closure_75]
    exact x.property
  exact Subgroup.closure_induction
    (k := K) (p := fun y _ ↦ y ^ 2 = 1) (x := (x : G))
    (by
      rintro y ⟨l, hl, hy⟩
      let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let _ : IsElementaryAbelian 2 (omegaOneCenter (q Gamma l)) :=
        omegaOneCenter_isElementaryAbelian_75 (q Gamma l)
      have hdl : d ∈ neighborhood Gamma l :=
        (mem_neighborhood_iff_adjacent_75 Gamma).2
          (Gamma.adjacent_symm
            ((mem_neighborhood_iff_adjacent_75 Gamma).1 hl))
      exact elemPow_eq_one_of_isElementaryAbelian y
        ((lemma_seven_three h Gamma).center_core l d hdl hy))
    (by simp)
    (by
      intro y z hy hz hypow hzpow
      have hyz : Commute y z := by
        change y * z = z * y
        simpa using congrArg Subtype.val
          (mul_comm (⟨y, by rwa [v_eq_closure_75]⟩ : v Gamma d)
            (⟨z, by rwa [v_eq_closure_75]⟩ : v Gamma d))
      calc
        (y * z) ^ 2 = y ^ 2 * z ^ 2 := hyz.mul_pow 2
        _ = 1 := by simp [hypow, hzpow])
    (by
      intro y _ hypow
      simpa [inv_pow] using congrArg Inv.inv hypow)
    hxcl

private theorem v_quadratic_pair_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hlen : 2 < cp.length) :
    IsQuadraticOn (v Gamma cp.firstStep) (v Gamma cp.a') ∧
      IsQuadraticOn (v Gamma cp.a') (v Gamma cp.firstStep) := by
  let h74 := lemma_seven_four h Gamma cp
  let hfirstEA := v_isElementaryAbelian_75 h Gamma cp hlen cp.firstStep
  let hendEA := v_isElementaryAbelian_75 h Gamma cp hlen cp.a'
  let _ : IsElementaryAbelian 2 (v Gamma cp.firstStep) := hfirstEA
  let _ : IsElementaryAbelian 2 (v Gamma cp.a') := hendEA
  have hfirstNormEnd : v Gamma cp.firstStep ≤
      Subgroup.normalizer (v Gamma cp.a' : Set G) :=
    h74.first_containment.2.trans
      (stabilizer_le_normalizer_v_75 Gamma cp.a')
  have hendNormFirst : v Gamma cp.a' ≤
      Subgroup.normalizer (v Gamma cp.firstStep : Set G) :=
    h74.reverse_containment.2.trans
      (stabilizer_le_normalizer_v_75 Gamma cp.firstStep)
  have hfirstAb : ⁅v Gamma cp.firstStep, v Gamma cp.firstStep⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val
      (mul_comm (⟨y, hy⟩ : v Gamma cp.firstStep)
        (⟨x, hx⟩ : v Gamma cp.firstStep))
  have hendAb : ⁅v Gamma cp.a', v Gamma cp.a'⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val
      (mul_comm (⟨y, hy⟩ : v Gamma cp.a')
        (⟨x, hx⟩ : v Gamma cp.a'))
  constructor
  · unfold IsQuadraticOn
    rw [eq_bot_iff]
    have hinner : ⁅v Gamma cp.a', v Gamma cp.firstStep⁆ ≤
        v Gamma cp.firstStep := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp hendNormFirst
    exact (Subgroup.commutator_mono hinner le_rfl).trans
      (le_of_eq hfirstAb)
  · unfold IsQuadraticOn
    rw [eq_bot_iff]
    have hinner : ⁅v Gamma cp.firstStep, v Gamma cp.a'⁆ ≤
        v Gamma cp.a' := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp hfirstNormEnd
    exact (Subgroup.commutator_mono hinner le_rfl).trans
      (le_of_eq hendAb)

private theorem longer_case_75
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hcomm : ⁅z Gamma cp.a, z Gamma cp.a'⁆ = ⊥)
    (hlen : 1 < cp.length) :
    IsElementaryAbelian 2 (v Gamma cp.firstStep) ∧
      IsQuadraticOn (v Gamma cp.firstStep) (v Gamma cp.a') ∧
      IsQuadraticOn (v Gamma cp.a') (v Gamma cp.firstStep) := by
  have hodd := odd_distance_75 h Gamma cp hcomm
  have hthree : 2 < cp.length := by
    rcases hodd with ⟨k, hk⟩
    omega
  exact ⟨v_isElementaryAbelian_75 h Gamma cp hthree cp.firstStep,
    v_quadratic_pair_75 h Gamma cp hthree⟩

/-- Commuting critical endpoint centers force the terminal center to be
central in its vertex stabilizer, as used in (7.7)(c). -/
public theorem lemma_seven_five_endpoint_center
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hcomm : ⁅z Gamma cp.a, z Gamma cp.a'⁆ = ⊥) :
    z Gamma cp.a' = omegaOneCenter (stabilizer Gamma cp.a') :=
  (endpoint_center_75 h Gamma cp hcomm).1

/-- Vertex stabilizers transport under the graph action by conjugation. -/
public theorem stabilizer_act
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) (d : Gamma.Vertex) :
    stabilizer Gamma (Gamma.act g d) =
      conjugateBy (stabilizer Gamma d) g⁻¹ :=
  stabilizer_act_75 Gamma g d

/-- The graph action preserves adjacency. -/
public theorem adjacent_act
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) {d l : Gamma.Vertex} (hdl : Gamma.adjacent d l) :
    Gamma.adjacent (Gamma.act g d) (Gamma.act g l) :=
  adjacent_act_75 Gamma g hdl

/-- The vertex center transports under the graph action by conjugation. -/
public theorem z_act
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) (d : Gamma.Vertex) :
    z Gamma (Gamma.act g d) =
      (z Gamma d).map (MulAut.conj g⁻¹).toMonoidHom :=
  z_act_75 Gamma g d

/-- The neighbor-center join transports under the graph action by conjugation. -/
public theorem v_act
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) (d : Gamma.Vertex) :
    v Gamma (Gamma.act g d) =
      (v Gamma d).map (MulAut.conj g⁻¹).toMonoidHom :=
  v_act_75 Gamma g d

/-- The Sylow-center join at a vertex is invariant under its stabilizer. -/
public theorem stabilizer_le_normalizer_z
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (d : Gamma.Vertex) :
    stabilizer Gamma d ≤ Subgroup.normalizer (z Gamma d : Set G) :=
  stabilizer_le_normalizer_z_75 Gamma d

/-- The join of neighbor centers is invariant under the vertex stabilizer. -/
public theorem stabilizer_le_normalizer_v
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (d : Gamma.Vertex) :
    stabilizer Gamma d ≤ Subgroup.normalizer (v Gamma d : Set G) :=
  stabilizer_le_normalizer_v_75 Gamma d

/-- In the commuting-endpoint case, edge transitivity carries the initial edge
to the terminal edge without swapping its endpoints.  This is the orbit fact
used in Stellmacher (7.6). -/
public theorem lemma_seven_five_endpoint_alignment
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hcomm : ⁅z Gamma cp.a, z Gamma cp.a'⁆ = ⊥) :
    ∃ g : G,
      Gamma.act g cp.a =
        cp.path ⟨cp.length - 1, by omega⟩ ∧
      Gamma.act g cp.firstStep = cp.a' :=
  (orbit_and_next_center_75 h Gamma cp hcomm).1

/-- **Stellmacher (7.5).** Consequences of commuting endpoint centers along
a critical path. -/
public theorem lemma_seven_five
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hcomm : ⁅z Gamma cp.a, z Gamma cp.a'⁆ = ⊥) :
    LemmaSevenFiveConclusion Gamma cp := by
  have hnext := orbit_and_next_center_75 h Gamma cp hcomm
  exact
    { odd_distance := odd_distance_75 h Gamma cp hcomm
      next_center := hnext.2
      centralizer_residual := centralizer_residual_75 h Gamma cp hcomm
      start_center_trivial := start_center_trivial_75 h Gamma cp hcomm
      longer_case := longer_case_75 h Gamma cp hcomm }

end Stellmacher.SectionsFiveToSeven

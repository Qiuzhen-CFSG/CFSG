module

public import Stellmacher.PushingUp.IncidentEdgeCore

/-!
# The two-core across a length-two path

This module proves the distance-two edge-core identity used in Stellmacher,
*Pushing up*, Arch. Math. 46 (1986), proof of (2.3), journal p.12.  If
`a ~ d ~ u`, the two endpoints are distinct M-orbit vertices, and `S` is the
given Sylow 2-subgroup, then the 2-core of `G_u ∩ G_a` is the 2-core of the
incident edge stabilizer `G_a ∩ G_d`.

The geometric step is the Bass--Serre unique-midpoint property.  After moving
`a ~ d` to the base edge, local transitivity writes `u` using an element of
the holomorph-side factor.  Distinctness makes that element lie outside the
amalgamated subgroup.  The PushoutI normal form, applied to an explicit
reduced word of length three or four, then shows
`G_a ∩ G_u ≤ G_d`.  The accepted incident-edge calculation identifies
`O₂(G_a ∩ G_d)` with the whole edge stabilizer, while (1.3)(b) makes it
fix every neighbor of `d`.  These two containments identify the endpoint
intersection with that edge core, whose own 2-core is itself.

All normal-form, midpoint, and subgroup-lattice helpers remain private; the
sole public result is the exact graph-local identity needed by (2.3).
-/

namespace Monoid.PushoutI

open Monoid CoprodI Subgroup

universe u v

private theorem mem_other_range_of_mem_range_and_conjugate_mem
    {I : Type u} {G : I → Type v} {H : Type v}
    [∀ i, Group (G i)] [Group H]
    {phi : ∀ i, H →* G i}
    (hphi : ∀ i, Function.Injective (phi i))
    {i j : I} (hij : i ≠ j)
    {y : G j} (hy : y ∉ (phi j).range)
    {x : PushoutI phi}
    (hx : x ∈ (of i).range)
    (hconj : of j y * x * (of j y)⁻¹ ∈ (of i).range) :
    x ∈ (of j).range := by
  classical
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, hn⟩ := hconj
  by_contra hmj
  have hm : m ∉ (phi i).range := by
    rintro ⟨h, rfl⟩
    apply hmj
    rw [of_apply_eq_base]
    exact MonoidHom.mem_range.mpr ⟨phi j h, by rw [of_apply_eq_base]⟩
  have hy1 : y ≠ 1 := by
    intro hyone
    apply hy
    exact ⟨1, by simp [hyone]⟩
  have hm1 : m ≠ 1 := by
    intro hmone
    apply hm
    exact ⟨1, by simp [hmone]⟩
  have hji : j ≠ i := hij.symm
  by_cases hnbase : n ∈ (phi i).range
  · let w : Word G :=
      ⟨[⟨j, y⟩, ⟨i, m⟩, ⟨j, y⁻¹⟩], by simp [hy1, hm1], by simp [hij, hji]⟩
    have hw : Reduced phi w := by
      simp only [w, Reduced, List.mem_cons, forall_eq_or_imp,
        not_false_eq_true, hy, hm, List.mem_nil_iff, false_imp_iff,
        imp_true_iff, and_true, inv_mem_iff]
    have hempty := hw.eq_empty_of_mem_range hphi (by
      obtain ⟨h, rfl⟩ := hnbase
      refine MonoidHom.mem_range.mpr ⟨h, ?_⟩
      simp only [w, Word.prod, List.map_cons, List.prod_cons, List.prod_nil,
        List.map_nil, map_mul, ofCoprodI_of, map_inv, mul_one]
      simpa only [of_apply_eq_base, mul_assoc] using hn)
    simp [w, Word.empty] at hempty
  · let w : Word G :=
      ⟨[⟨j, y⟩, ⟨i, m⟩, ⟨j, y⁻¹⟩, ⟨i, n⁻¹⟩],
        by
          have hn1 : n ≠ 1 := by
            intro hnone
            apply hnbase
            exact ⟨1, by simp [hnone]⟩
          simp [hy1, hm1, hn1],
        by simp [hij, hji]⟩
    have hw : Reduced phi w := by
      simp only [w, Reduced, List.mem_cons, forall_eq_or_imp,
        not_false_eq_true, hy, hm, hnbase, List.mem_nil_iff, false_imp_iff,
        imp_true_iff, and_true, inv_mem_iff]
    have hempty := hw.eq_empty_of_mem_range hphi (by
      refine MonoidHom.mem_range.mpr ⟨1, ?_⟩
      simp only [w, Word.prod, List.map_cons, List.prod_cons, List.prod_nil,
        List.map_nil, map_mul, ofCoprodI_of, map_inv, mul_one, map_one]
      calc
        1 = of i n * (of i n)⁻¹ := (mul_inv_cancel _).symm
        _ = of j y * (of i m * ((of j y)⁻¹ * (of i n)⁻¹)) := by
          rw [hn]
          simp only [mul_assoc])
    simp [w, Word.empty] at hempty

end Monoid.PushoutI

namespace Stellmacher.PushingUp

open AmalgamGraph

universe u

variable {M : Type u} [Group M]

private theorem exists_action_base_edge [Finite M]
    (S : Subgroup M) (a d : Vertex S)
    (ha : InMVertexOrbit S a) (had : Adjacent S a d) :
    ∃ g : FreeAmalgam S,
      a = act S g (mVertex S 1) ∧ d = act S g (hVertex S 1) := by
  obtain ⟨x, hax⟩ := ha
  have hae : Adjacent S a (act S x (hVertex S 1)) := by
    rw [hax]
    exact (adjacent_act_iff S x (mVertex S 1) (hVertex S 1)).2
      (base_adjacent S)
  obtain ⟨y, hya, hyd⟩ :=
    stabilizer_transitive_neighbors S a hae had
  refine ⟨x * y, ?_, ?_⟩
  · rw [act_mul, ← hax]
    exact hya.symm
  · rw [act_mul]
    exact hyd.symm

private theorem base_stabilizer_inf_le_midpoint [Finite M]
    (S : Subgroup M) (u : Vertex S)
    (hdu : Adjacent S (hVertex S 1) u)
    (hua : u ≠ mVertex S 1) :
    stabilizer S (mVertex S 1) ⊓ stabilizer S u ≤
      stabilizer S (hVertex S 1) := by
  obtain ⟨y, hyH, hyu⟩ := stabilizer_transitive_neighbors S
    (hVertex S 1) (adjacent_symm S (base_adjacent S)) hdu
  rw [stabilizer_h_base] at hyH
  obtain ⟨yh, hyh⟩ := hyH
  have hyfactor : yh ∉ (diagram S Side.h).range := by
    rintro ⟨s, hs⟩
    have hyS : y ∈ Sbar S := by
      refine ⟨s, ?_⟩
      calc
        embedS S s = embedH S (SemidirectProduct.inl s) :=
          (DFunLike.congr_fun (embedH_comp_inl S) s).symm
        _ = embedH S yh := congrArg (embedH S) hs
        _ = y := hyh
    have hyM : y ∈ stabilizer S (mVertex S 1) := by
      rw [stabilizer_m_base]
      have hSleM : Sbar S ≤ Mbar S := by
        rw [← Mbar_inf_Hbar]
        exact inf_le_left
      exact hSleM hyS
    apply hua
    rw [← hyu]
    exact hyM
  intro x hx
  have hxM : x ∈ Mbar S := by
    rw [← stabilizer_m_base]
    exact hx.1
  have hconjM : embedH S yh * x * (embedH S yh)⁻¹ ∈ Mbar S := by
    rw [hyh]
    rw [← stabilizer_m_base]
    change act S (y * x * y⁻¹) (mVertex S 1) = mVertex S 1
    calc
      act S (y * x * y⁻¹) (mVertex S 1) =
          act S y⁻¹ (act S x (act S y (mVertex S 1))) := by
            simp only [act_mul, mul_assoc]
      _ = act S y⁻¹ (act S y (mVertex S 1)) := by
        rw [hyu]
        exact congrArg (act S y⁻¹) hx.2
      _ = mVertex S 1 := by rw [← act_mul]; simp
  rw [stabilizer_h_base]
  exact Monoid.PushoutI.mem_other_range_of_mem_range_and_conjugate_mem
    (diagram_injective S) (by decide : Side.m ≠ Side.h)
    hyfactor hxM hconjM

private theorem stabilizer_inf_le_midpoint [Finite M]
    (S : Subgroup M) (a d u : Vertex S)
    (ha : InMVertexOrbit S a)
    (had : Adjacent S a d) (hdu : Adjacent S d u)
    (hua : u ≠ a) :
    stabilizer S a ⊓ stabilizer S u ≤ stabilizer S d := by
  obtain ⟨g, rfl, rfl⟩ := exists_action_base_edge S a d ha had
  let u₀ := act S g⁻¹ u
  have hdu₀ : Adjacent S (hVertex S 1) u₀ := by
    have h := (adjacent_act_iff S g⁻¹ _ _).2 hdu
    simpa [u₀, ← act_mul] using h
  have hu₀a : u₀ ≠ mVertex S 1 := by
    intro hEq
    apply hua
    have h := congrArg (act S g) hEq
    simpa [u₀, ← act_mul] using h
  intro x hx
  let x₀ : FreeAmalgam S := g * x * g⁻¹
  have hx₀a : x₀ ∈ stabilizer S (mVertex S 1) := by
    change act S x₀ (mVertex S 1) = mVertex S 1
    calc
      act S x₀ (mVertex S 1) =
          act S g⁻¹ (act S x (act S g (mVertex S 1))) := by
            simp only [x₀, act_mul, mul_assoc]
      _ = act S g⁻¹ (act S g (mVertex S 1)) :=
        congrArg (act S g⁻¹) hx.1
      _ = mVertex S 1 := by rw [← act_mul]; simp
  have hx₀u : x₀ ∈ stabilizer S u₀ := by
    change act S x₀ u₀ = u₀
    calc
      act S x₀ u₀ = act S g⁻¹ (act S x (act S g u₀)) := by
        simp only [x₀, act_mul, mul_assoc]
      _ = act S g⁻¹ (act S x u) := by
        congr 2
        dsimp only [u₀]
        rw [← act_mul]
        simp
      _ = act S g⁻¹ u := congrArg (act S g⁻¹) hx.2
      _ = u₀ := rfl
  have hx₀d : x₀ ∈ stabilizer S (hVertex S 1) :=
    base_stabilizer_inf_le_midpoint S u₀ hdu₀ hu₀a ⟨hx₀a, hx₀u⟩
  change act S x (act S g (hVertex S 1)) = act S g (hVertex S 1)
  have h := congrArg (act S g) hx₀d
  simpa [x₀, ← act_mul, mul_assoc] using h

private theorem twoCoreAmbient_eq_self_of_isPGroup
    {G : Type*} [Group G] (H : Subgroup G) (hHp : IsPGroup 2 H) :
    twoCoreAmbient H = H := by
  have htopP : IsPGroup 2 (⊤ : Subgroup H) := hHp.to_subgroup ⊤
  have hcoreTop : pCore 2 H = ⊤ := by
    apply top_unique
    exact le_sSup ⟨inferInstance, htopP⟩
  unfold twoCoreAmbient
  rw [hcoreTop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem edgeTwoCore_isPGroup
    {G : Type*} [Group G] (A B : Subgroup G) :
    IsPGroup 2 (twoCoreAmbient (A ⊓ B)) := by
  unfold twoCoreAmbient
  exact (pCore_isPGroup (p := 2) (G := ↥(A ⊓ B))).map
    (A ⊓ B : Subgroup G).subtype

private theorem edgeTwoCore_distanceTwo_of_local
    (S : Subgroup M) (a d u : Vertex S)
    (_had : Adjacent S a d) (hdu : Adjacent S d u)
    (hEdge : edgeTwoCore S a d = stabilizer S a ⊓ stabilizer S d)
    (hKernel : edgeTwoCore S a d ≤ neighborhoodKernel S d)
    (hmid : stabilizer S a ⊓ stabilizer S u ≤ stabilizer S d) :
    edgeTwoCore S u a = edgeTwoCore S a d := by
  have hEleU : edgeTwoCore S a d ≤ stabilizer S u := by
    intro x hx
    exact (hKernel hx).2 u hdu
  have hEeq : stabilizer S u ⊓ stabilizer S a = edgeTwoCore S a d := by
    apply le_antisymm
    · rw [hEdge]
      exact le_inf inf_le_right (by
        rw [inf_comm]
        exact hmid)
    · exact le_inf hEleU (by rw [hEdge]; exact inf_le_left)
  unfold edgeTwoCore
  rw [hEeq]
  exact twoCoreAmbient_eq_self_of_isPGroup _
    (edgeTwoCore_isPGroup (stabilizer S a) (stabilizer S d))

/-- Across a length-two path with distinct M-side endpoints, the two-core of
the endpoint-stabilizer intersection is the incident edge two-core. -/
public theorem edgeTwoCore_distanceTwo [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (a d u : Vertex S) (ha : InMVertexOrbit S a)
    (hu : InMVertexOrbit S u) (had : Adjacent S a d)
    (hdu : Adjacent S d u) (hau : a ≠ u) :
    edgeTwoCore S u a = edgeTwoCore S a d := by
  have _hu : InMVertexOrbit S u := hu
  have hEdge : edgeTwoCore S a d =
      stabilizer S a ⊓ stabilizer S d :=
    incident_edgeTwoCore_eq_edgeStabilizer S T hTS a d ha had
  have hKernel : edgeTwoCore S a d ≤ neighborhoodKernel S d :=
    (localKernel_at_mEdge S T hTS a d ha had).2.2.2
  have hmid : stabilizer S a ⊓ stabilizer S u ≤ stabilizer S d :=
    stabilizer_inf_le_midpoint S a d u ha had hdu hau.symm
  exact edgeTwoCore_distanceTwo_of_local S a d u had hdu hEdge hKernel hmid

end Stellmacher.PushingUp

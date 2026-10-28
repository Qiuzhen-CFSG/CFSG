module

public import Stellmacher.SectionOne.LemmaOneFiveRelativeM

/-!
# The minimal action ratio for a relative oneA actor

For `A ∈ oneA S`, the defining bound `m(A) ≤ 1` and the relative form of
Stellmacher (1.5)(e) give `m(A)=1`. Every subgroup of `A` is elementary
abelian and satisfies the same lower bound. Passing from `A ≤ G` to
`A.subgroupOf E`, where `A ≤ E ≤ G`, preserves both group cardinalities
and fixed-point subgroups on the original module `V`. The public
`m_map_subtype` identity also supports the ratio-two relative action in
(9.1).

The theorem transports the equality and minimum to this restricted actor.
It supplies the numerical hypotheses for applying the restricted (1.6) to
`E=[O₂′(G),A]A` in the proof of Stellmacher (1.7), journal p. 19;
see `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionOne

universe u

/-- Restricting an actor through a subgroup preserves its fixed-point measure. -/
public theorem m_map_subtype
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (E : Subgroup G) (Y : Subgroup E) :
    m (G := G) (V := V) (Y.map E.subtype) = m (G := E) (V := V) Y := by
  have hfixed : FixedPoints.subgroup (Y.map E.subtype) V = FixedPoints.subgroup Y V := by
    ext v
    rw [FixedPoints.mem_subgroup, FixedPoints.mem_subgroup]
    constructor
    · intro hv y
      exact hv ⟨((y : E) : G), Subgroup.mem_map_of_mem E.subtype y.property⟩
    · intro hv y
      obtain ⟨z, hz, hzy⟩ := y.property
      have h := hv ⟨z, hz⟩
      change (z : G) • v = v at h
      change (y : G) • v = v
      have hzy' : (z : G) = (y : G) := hzy
      rw [← hzy']
      exact h
  unfold m
  rw [hfixed, Subgroup.card_map_of_injective E.subtype_injective]

private theorem elementaryAbelian_of_le
    {G : Type u} [Group G] {A Y : Subgroup G}
    (hA : IsElementaryAbelian 2 A) (hYA : Y ≤ A) :
    IsElementaryAbelian 2 Y := by
  let _ : IsElementaryAbelian 2 A := hA
  refine {
    toIsMulCommutative := ⟨⟨?_⟩⟩
    exponent_dvd_p := ?_ }
  · intro x y
    apply Subtype.ext
    exact congrArg (fun a : A => (a : G)) (IsMulCommutative.is_comm.comm
      (⟨(x : G), hYA x.property⟩ : A) (⟨(y : G), hYA y.property⟩ : A))
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro y
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (y : G) (hYA y.property)

public theorem oneA_relative_m_eq_one_and_min
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (A E : Subgroup G)
    (hA : oneA (G := G) (V := V) (S : Subgroup G) A) (hAE : A ≤ E) :
    m (G := E) (V := V) (A.subgroupOf E) = 1 ∧
      ∀ Y : Subgroup E, Y ≤ A.subgroupOf E → Y ≠ ⊥ →
        m (G := E) (V := V) (A.subgroupOf E) ≤ m (G := E) (V := V) Y := by
  have hmA : m (G := G) (V := V) A = 1 :=
    le_antisymm hA.2.2 (lemma_one_five_m_ge_one_relative h S A hA.1 hA.2.1)
  have hmAE : m (G := E) (V := V) (A.subgroupOf E) = 1 := by
    rw [← m_map_subtype E (A.subgroupOf E), Subgroup.map_subgroupOf_eq_of_le hAE]
    exact hmA
  refine ⟨hmAE, ?_⟩
  intro Y hYA _
  rw [hmAE, ← m_map_subtype E Y]
  have hYmapA : Y.map E.subtype ≤ A := by
    rintro y ⟨z, hz, rfl⟩
    exact hYA hz
  exact lemma_one_five_m_ge_one_relative h S (Y.map E.subtype)
    (hYmapA.trans hA.1) (elementaryAbelian_of_le hA.2.1 hYmapA)

end Stellmacher.SectionOne


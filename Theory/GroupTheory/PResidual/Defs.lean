module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Prime residuals

The p-residual Oᵖ(G) is the intersection of the normal subgroups with
p-group quotient. Thus G = Oᵖ(G) means precisely that G has no nontrivial
p-group quotient. This formulation does not choose a generating family.

Source: the standard residual notation used in Aschbacher–Smith, C.1.7.
-/

@[expose] public section

/-- The p-residual Oᵖ(G). -/
def pResidual (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  sInf {N : Subgroup G | ∃ hN : N.Normal, @IsPGroup p (G ⧸ N)
    (@QuotientGroup.Quotient.group G _ N hN)}

/-- Having no proper normal subgroup with p-group quotient. -/
def IsPPerfect (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (N : Subgroup G) (hN : N.Normal), @IsPGroup p (G ⧸ N)
    (@QuotientGroup.Quotient.group G _ N hN) → N = ⊤

theorem pResidual_eq_top_iff (p : ℕ) (G : Type*) [Group G] :
    pResidual p G = ⊤ ↔ IsPPerfect p G := by
  constructor
  · intro h N hN hp
    apply top_unique
    rw [← h]
    exact sInf_le ⟨hN, hp⟩
  · intro h
    apply top_unique
    apply le_sInf
    rintro N ⟨hN, hp⟩
    rw [h N hN hp]

/-- Surjective images of p-perfect groups remain p-perfect. -/
theorem IsPPerfect.of_surjective {p : ℕ} {G H : Type*} [Group G] [Group H]
    (h : IsPPerfect p G) (f : G →* H) (hf : Function.Surjective f) :
    IsPPerfect p H := by
  intro N hN hp
  let := hN
  let q := (QuotientGroup.mk' N).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective N).comp hf
  have hk : IsPGroup p (G ⧸ q.ker) :=
    hp.of_equiv (QuotientGroup.quotientKerEquivOfSurjective q hq).symm
  have hker := h q.ker inferInstance hk
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  apply (QuotientGroup.eq_one_iff (f x)).mp
  exact MonoidHom.mem_ker.mp (show x ∈ q.ker by rw [hker]; trivial)

end

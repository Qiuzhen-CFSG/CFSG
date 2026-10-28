module
public import Theory.GroupAction.ThirteenOrbitArithmetic
public import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Uniqueness of the975-point orbit

In a2304-point invariant set with a fixed point, two distinct975-point
orbits would leave353 points. The native thirteen-overgroup alternatives
exclude this residual cardinality. This is the exact arithmetic used in
source J.5.5(5), with socle exclusion supplied separately on the actual action.
-/

public noncomputable section
namespace MulAction
variable {K Ω:Type*} [Group K] [MulAction K Ω] [Finite Ω]

theorem unique_orbit_975_of_thirteen_alternatives (S:Set Ω) (a:Ω)
    (hS:∀k:K,∀x∈S,k•x∈S) (hsize:Nat.card S=2304) (ha:a∈S)
    (hfix:∀k:K,k•a=a)
    (horbit:∀x∈S,x≠a→13∣Nat.card (orbit K x) ∨ Nat.card (orbit K x)=300 ∨
      Nat.card (orbit K x)=600 ∨ Nat.card (orbit K x)=1200)
    (b c:Ω) (hb:b∈S) (hc:c∈S)
    (hbc:Nat.card (orbit K b)=975) (hcc:Nat.card (orbit K c)=975) :
    orbit K b=orbit K c := by
  have hoa:orbit K a=({a}:Set Ω):=by
    ext z
    constructor
    · rintro ⟨k,rfl⟩;exact hfix k
    · rintro rfl;exact mem_orbit_self _
  have hnot (z:Ω) (hz:Nat.card (orbit K z)=975):a∉orbit K z:=by
    intro hm
    have he:orbit K a=orbit K z:=orbit_eq_iff.mpr hm
    have hh:=Nat.card_congr (Equiv.setCongr he)
    rw [hoa,hz] at hh
    simp at hh
  rcases orbit.eq_or_disjoint (G:=K) b c with he|hd
  · exact he
  exfalso
  let T:Set Ω:={a}∪orbit K b∪orbit K c
  have hT:T⊆S:=by
    rintro z ((rfl|⟨k,rfl⟩)|⟨k,rfl⟩)
    · exact ha
    · exact hS k b hb
    · exact hS k c hc
  have ht:T.ncard=1951:=by
    have had:Disjoint ({a}:Set Ω) (orbit K b):=Set.disjoint_singleton_left.mpr (hnot b hbc)
    have hcd:Disjoint (({a}:Set Ω)∪orbit K b) (orbit K c):=
      disjoint_sup_left.mpr ⟨Set.disjoint_singleton_left.mpr (hnot c hcc),hd⟩
    rw [Set.ncard_union_eq hcd,Set.ncard_union_eq had]
    rw [Set.ncard_singleton]
    change 1+Nat.card (orbit K b)+Nat.card (orbit K c)=1951
    omega
  let R:=S\T
  have hr:R.ncard=353:=by
    rw [Set.ncard_sdiff hT,ht]
    change Nat.card S-1951=353
    omega
  have hTin (k:K) (z:Ω) (hz:z∈T):k•z∈T:=by
    rcases hz with (rfl|⟨l,rfl⟩)|⟨l,rfl⟩
    · exact Or.inl (Or.inl (hfix k))
    · exact Or.inl (Or.inr ⟨k*l,(mul_smul k l b)⟩)
    · exact Or.inr ⟨k*l,(mul_smul k l c)⟩
  have hR:∀k:K,∀z∈R,k•z∈R:=by
    intro k z hz
    refine ⟨hS k z hz.1,?_⟩
    intro ht
    have he:=hTin k⁻¹ (k•z) ht
    rw [inv_smul_smul] at he
    exact hz.2 he
  exact invariant_card_ne_353 R hR (fun z hz=>horbit z hz.1 (fun he=>
    hz.2 (Or.inl (Or.inl he)))) hr
end MulAction

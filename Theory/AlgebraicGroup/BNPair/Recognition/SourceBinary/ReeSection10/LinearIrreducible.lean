module
public import Theory.Representation.SL2.FullFixedIndex
public import Theory.Representation.SL2.MinimalBinaryDegree
public import Theory.SpecificGroups.PSL2.SemilinearCoverage.Normalization

/-!
# Irreducibility of the linear section in minimum degree

A faithful binary SL₂(2ⁿ) action in degree 2n is irreducible. For n>1,
the full fixed-index bound kills invariant vectors and the irreducible
minimum-degree bound fills the whole space. For n=1, a proper invariant
line and its quotient would both be fixed. Every actor would then square
to one, contradicting the nontrivial cubic matrix. This explicitly retains
the solvable group SL₂(2).

V1Natural applies the result to the literal characteristic section on p.222.
Source: Fong--Seitz I (5D) and II p.222, before the natural basis (10.6).
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10

private theorem binary_line_trivial {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hd : Module.finrank (ZMod 2) V ≤ 1) : ρ = 1 := by
  ext g v
  by_cases hv : v = 0
  · simp [hv]
  have hd1 : Module.finrank (ZMod 2) V = 1 := by
    have hpos : 0 < Module.finrank (ZMod 2) V :=
      Module.finrank_pos_iff.mpr (⟨⟨v,0,hv⟩⟩ : Nontrivial V)
    omega
  obtain ⟨a,ha⟩ := (finrank_eq_one_iff_of_nonzero' (K := ZMod 2) v hv).mp hd1 (ρ g v)
  have ha0 : a ≠ 0 := by
    intro hz
    have he : ρ g v = 0 := by rw [←ha,hz,zero_smul]
    have hh := congrArg (ρ g⁻¹) he
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,map_zero] at hh
    exact hv hh
  have ha1 : a = 1 := Fin.eq_one_of_ne_zero a ha0
  rw [←ha,ha1,one_smul]
  rfl

/-- A nontrivial cubic action in binary dimension two is irreducible. -/
theorem binary_two_irreducible_of_cubic {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hd : Module.finrank (ZMod 2) V = 2)
    (r : G) (hr : r^3 = 1) (hmove : ρ r ≠ 1) : ρ.IsIrreducible := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank (ZMod 2) V by omega)
  refine ⟨fun W => ?_⟩
  by_contra! hw
  have hb : W.toSubmodule ≠ ⊥ := fun h => hw.1 (Subrepresentation.toSubmodule_injective h)
  have ht : W.toSubmodule ≠ ⊤ := fun h => hw.2 (Subrepresentation.toSubmodule_injective h)
  have hp : 0 < Module.finrank (ZMod 2) W.toSubmodule :=
    Nat.pos_of_ne_zero (fun hz => hb (Submodule.finrank_eq_zero.mp hz))
  have hlt := Submodule.finrank_lt ht
  have hsum := Submodule.finrank_quotient_add_finrank W.toSubmodule
  have hW := binary_line_trivial W.toRepresentation (by omega)
  have hQ := binary_line_trivial W.quotientRepresentation (by omega)
  have hfix (v : V) (hv : v ∈ W) : ρ r v = v :=
    congrArg Subtype.val (DFunLike.congr_fun (DFunLike.congr_fun hW r) (⟨v,hv⟩ : W))
  have hdiff (v : V) : ρ r v - v ∈ W := by
    apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
    change W.toSubmodule.mkQ (ρ r v - v) = 0
    rw [map_sub,←W.quotientRepresentation_mk]
    exact sub_eq_zero.mpr
      (DFunLike.congr_fun (DFunLike.congr_fun hQ r) (W.toSubmodule.mkQ v))
  have hsquare : (ρ r)^2 = 1 := by
    ext v
    have hh := hfix (ρ r v-v) (hdiff v)
    simp only [map_sub] at hh
    change ρ r (ρ r v) = v
    have hadd (w : V) : w+w=0 := by
      simpa only [two_smul,zero_smul] using (show (2 : ZMod 2) • w = 0 by rw [show (2 : ZMod 2) = 0 from rfl,zero_smul])
    have hneg (w : V) : -w=w := neg_eq_of_add_eq_zero_right (hadd w)
    rw [sub_eq_iff_eq_add] at hh
    rw [hh,sub_eq_add_neg,hneg]
    rw [add_right_comm,hadd,zero_add]
  have hcube : (ρ r)^3 = 1 := by rw [←map_pow,hr,map_one]
  rw [show (3 : ℕ)=2+1 from rfl,pow_succ,hsquare,one_mul] at hcube
  exact hmove hcube

/-- Faithful SL₂ actions of order q² are irreducible; the binary case uses
its cubic mover and the positive case uses the proved minimum degree. -/
theorem linear_minimal_irreducible {F V : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,F) V) (hf : Function.Injective ρ)
    (n : ℕ) (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hd : Module.finrank (ZMod 2) V = 2*n) : ρ.IsIrreducible := by
  let r := Theory.PSL2.SemilinearCoverage.weyl F * Theory.PSL2.SemilinearCoverage.uni (1 : F)
  have hr : r^3=1 := by
    apply Subtype.ext
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [r,pow_succ,Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]
  have hr1 : r ≠ 1 := by
    intro he
    have hh := congrArg (fun g : SL(2,F) => g.val 1 0) he
    simp [r,Matrix.mul_apply,Fin.sum_univ_two] at hh
  have hm : ρ r ≠ 1 := fun he => hr1 (hf (he.trans ρ.map_one.symm))
  by_cases hn1 : n=1
  · exact binary_two_irreducible_of_cubic ρ (by simpa [hn1] using hd) r hr hm
  · have hlow := Representation.SL2.fixedCodim_top_lower ρ ⟨r,hm⟩ (by omega) hF
    have hdim := Representation.BinaryOffender.fixedCodim_add_finrank ρ ⊤
    have hfix : ρ.invariants = ⊥ := by
      have hh : Representation.BinaryOffender.fixedSpace ρ ⊤ = ⊥ :=
        Submodule.finrank_eq_zero.mp (by omega)
      apply bot_unique
      intro v hv
      apply hh.le
      intro g
      exact hv g.val
    let : Nontrivial V := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank (ZMod 2) V by omega)
    exact Representation.SL2.irreducible_of_fixed_free_minimal_binary_degree ρ hfix
      (by omega) hF hd.le
end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10

module

public import Theory.GroupTheory.DirectProduct.DihedralFactorExtraction
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# A maximal dihedral splitting and its characteristic remainder

A finite group admits a largest number of direct factors D₈. Its remaining
factor has no further D₈ factor, so its derived subgroup is characteristic
after adjoining any number of dihedral factors. If every characteristic
subgroup contained in the original remainder is trivial, this final
remainder is abelian.

These are the finite-decomposition steps in Goldschmidt, Automorphisms of
Trivalent Graphs (1980), (2.14), printed p.385. The only factor comparison
used is the explicit coordinate extraction in the preceding module.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.DihedralFactorExtraction

private abbrev D := DihedralGroup 4

/-- Adjoin the first dihedral coordinate to a finite dihedral power. -/
def dihedralPowerSuccEquiv (n : ℕ) :
    DihedralGroup 4 × (Fin n → DihedralGroup 4) ≃* (Fin (n+1) → DihedralGroup 4) :=
  { Fin.consEquiv (fun _ : Fin (n+1) => DihedralGroup 4) with
    map_mul' := by
      intro a b
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl }

/-- Split off as many dihedral factors as possible, retaining the complement
as a subgroup of the original finite group. -/
theorem exists_maximal_splitting (B : Type*) [Group B] [Finite B] :
    ∃ n : ℕ, ∃ R : Subgroup B,
      Nonempty (B ≃* (Fin n → DihedralGroup 4) × R) ∧ ¬ HasFactor R := by
  classical
  let P (n : ℕ) : Prop := ∃ R : Subgroup B, Nonempty (B ≃* (Fin n → D) × R)
  have hzero : P 0 := by
    refine ⟨⊤,⟨?_⟩⟩
    exact (topEquiv : (⊤ : Subgroup B) ≃* B).symm.trans
      (MulEquiv.uniqueProd : (Fin 0 → D) × (⊤ : Subgroup B) ≃* (⊤ : Subgroup B)).symm
  have hbound {n : ℕ} (hn : P n) : n ≤ Nat.card B := by
    obtain ⟨R,⟨e⟩⟩ := hn
    have hc : Nat.card B = 8 ^ n * Nat.card R := by
      rw [Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_fun,Nat.card_fin,
        DihedralGroup.nat_card]
    have hp : 8 ^ n ≤ Nat.card B := by
      rw [hc]
      exact Nat.le_mul_of_pos_right _ Nat.card_pos
    exact (Nat.lt_pow_self (by decide : 1 < 8)).le.trans hp
  let n := Nat.findGreatest P (Nat.card B)
  obtain ⟨R,⟨e⟩⟩ := Nat.findGreatest_spec (Nat.zero_le (Nat.card B)) hzero
  refine ⟨n,R,⟨e⟩,?_⟩
  rintro ⟨K,⟨s⟩⟩
  let K' := K.map R.subtype
  let k : K ≃* K' := K.equivMapOfInjective R.subtype R.subtype_injective
  let q : B ≃* (Fin (n+1) → D) × K' :=
    e.trans ((MulEquiv.prodCongr (MulEquiv.refl _) (s.trans
      (MulEquiv.prodCongr (MulEquiv.refl D) k))).trans
      (MulEquiv.prodAssoc.symm.trans
        ((MulEquiv.prodCongr MulEquiv.prodComm (MulEquiv.refl K')).trans
          (MulEquiv.prodCongr (dihedralPowerSuccEquiv n) (MulEquiv.refl K')))))
  have hnext : P (n+1) := ⟨K',⟨q⟩⟩
  exact Nat.not_succ_le_self n (Nat.le_findGreatest (hbound hnext) hnext)

/-- With an extra dihedral factor, the absence of a characteristic subgroup
inside the other factor forces the final remainder in its maximal splitting
to be abelian. In S₄ × B, such a characteristic subgroup is normal because
the Sylow subgroup normalizes it and the normal A₄ factor centralizes it. -/
theorem exists_abelian_remainder (B : Type*) [Group B] [Finite B]
    (hchar : ∀ K : Subgroup (DihedralGroup 4 × B), K.Characteristic →
      K ≤ (⊥ : Subgroup (DihedralGroup 4)).prod ⊤ → K = ⊥) :
    ∃ n : ℕ, ∃ R : Subgroup B,
      Nonempty (B ≃* (Fin n → DihedralGroup 4) × R) ∧ IsMulCommutative R := by
  classical
  obtain ⟨n,R,⟨e⟩,hR⟩ := exists_maximal_splitting B
  let f : D × B ≃* (Fin (n+1) → D) × R :=
    (MulEquiv.prodCongr (MulEquiv.refl D) e).trans
      (MulEquiv.prodAssoc.symm.trans
        (MulEquiv.prodCongr (dihedralPowerSuccEquiv n) (MulEquiv.refl R)))
  let C := (⊥ : Subgroup (Fin (n+1) → D)).prod (commutator R)
  let K := C.comap f.toMonoidHom
  have hC : C.Characteristic := characteristic_derived_remainder (n+1) R hR
  have hK : K.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    have hx' := characteristic_iff_le_comap.mp hC (MulAut.congr f a) hx
    change f.toMonoidHom (a x) ∈ C
    simpa [MulAut.congr] using hx'
  have hKB : K ≤ (⊥ : Subgroup D).prod ⊤ := by
    intro x hx
    refine ⟨?_,mem_top _⟩
    have hh : (f x).1 = 1 := hx.1
    exact congrFun hh 0
  have hbot := hchar K hK hKB
  have hderived : commutator R = ⊥ := by
    apply bot_unique
    intro r hr
    have hx : f.symm (1,r) ∈ K := by
      change f (f.symm (1,r)) ∈ C
      rw [f.apply_symm_apply]
      exact ⟨one_mem _,hr⟩
    have he : f.symm (1,r) = 1 := hbot.le hx
    have he' := congrArg f he
    rw [f.apply_symm_apply,map_one] at he'
    exact congrArg Prod.snd he'
  exact ⟨n,R,⟨e⟩,(commutator_eq_bot_iff R).mp hderived⟩

end Theory.GroupTheory.DihedralFactorExtraction

module

public import Theory.Representation.BinaryRadicalFlag.Normalizer
public import Theory.LinearAlgebra.RegularLinearAction

/-!
# Positive-rank flags for binary radical normalizers

A complete flag has one-dimensional layers. Over F₂ every invertible
map of such a layer is the identity, so the flag stabilizer equals its
two-group layer kernel. Consequently a radical normalizer which is not
a two-group has a proper flag with at most dim(V) - 2 members.

This is the positive semisimple rank step used in Aschbacher--Smith,
C.2.7(3)(h), printed pp.145--147. The proof applies to every faithful
finite binary representation and uses no choice of triangular basis.
-/

public section
open Subgroup
namespace Representation.BinaryRadical
variable {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem displacement_mem_of_layer_dim_one
    (S T : Submodule (ZMod 2) V) (hST : S ≤ T)
    (hd : Module.finrank (ZMod 2) T ≤ Module.finrank (ZMod 2) S + 1)
    (g : V ≃ₗ[ZMod 2] V)
    (hS : ∀ v, g v ∈ S ↔ v ∈ S) (hT : ∀ v, g v ∈ T ↔ v ∈ T)
    {v : V} (hv : v ∈ T) : g v - v ∈ S := by
  have hm : T.map g.toLinearMap = T := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (hT y).mpr hy
    · intro hx
      exact ⟨g.symm x,(hT _).mp (by simpa using hx),g.apply_symm_apply x⟩
  let e := g.ofSubmodules T T hm
  let A := S.comap T.subtype
  have hA : A.map e.toLinearMap = A := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (hS y).mpr hy
    · intro hx
      refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
      apply (hS _).mp
      change (e (e.symm x) : V) ∈ S
      rw [e.apply_symm_apply]
      exact hx
  have hdim : Module.finrank (ZMod 2) (T ⧸ A) ≤ 1 := by
    have he : Module.finrank (ZMod 2) A = Module.finrank (ZMod 2) S :=
      (Submodule.comapSubtypeEquivOfLe hST).finrank_eq
    have hh := A.finrank_quotient_add_finrank
    omega
  have hq := LinearGroup.eq_one_of_binary_finrank_le_one hdim
    (Submodule.Quotient.equiv A A e hA)
  have heq := LinearEquiv.congr_fun hq (A.mkQ ⟨v,hv⟩)
  exact (Submodule.Quotient.eq A).mp heq

variable [Nontrivial V] (ρ : Representation (ZMod 2) G V)

/-- A complete flag stabilizer in a faithful binary action is a two-group. -/
theorem fullFlag_isPGroup (hρ : Function.Injective ρ)
    {k : ℕ} (W : Fin (k+1) → Submodule (ZMod 2) V)
    (hs : StrictMono W) (hzero : W 0 = ⊥) (hlast : W (Fin.last k) = ⊤)
    (hk : k = Module.finrank (ZMod 2) V) :
    IsPGroup 2 (flagStabilizer ρ W) := by
  let f : Fin (k+1) → Fin (k+1) := fun i =>
    ⟨Module.finrank (ZMod 2) (W i),by
      have hh := Submodule.finrank_le (W i)
      omega⟩
  have hf : StrictMono f := by
    intro i j hij
    exact Submodule.finrank_lt_finrank_of_lt (hs hij)
  have hdim (i : Fin (k+1)) : Module.finrank (ZMod 2) (W i) = i.val :=
    congrArg Fin.val (hf.apply_eq (x := i))
  apply (flagKernel_isPGroup ρ hρ W hzero hlast).to_le
  intro g hg
  refine ⟨hg,?_⟩
  intro i v hv
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V (ρ.asGroupHom g)
  apply displacement_mem_of_layer_dim_one (W i.castSucc) (W i.succ)
    (hs.monotone (Fin.castSucc_le_succ i)) ?_ e
    ((mem_flagStabilizer ρ W).mp hg i.castSucc)
    ((mem_flagStabilizer ρ W).mp hg i.succ) hv
  rw [hdim,hdim]
  exact le_rfl


variable [Finite G]
/-- A radical normalizer which is not a two-group has a binary flag with
positive semisimple rank. -/
theorem exists_positiveRank_flag_normalizer (hρ : Function.Injective ρ)
    (U : Subgroup G) (hU : U.IsPRadical 2)
    (hn : ¬ IsPGroup 2 (normalizer (U : Set G))) :
    ∃ (k : ℕ) (W : Fin k → Submodule (ZMod 2) V),
      0 < k ∧ k ≤ Module.finrank (ZMod 2) V - 2 ∧ StrictMono W ∧
      (∀ i, W i ≠ ⊥ ∧ W i ≠ ⊤) ∧
      normalizer (U : Set G) = ⨅ i, stabilizer ρ (W i) := by
  obtain ⟨k,W,hk,hbound,hs,hzero,hlast,heq⟩ := exists_fullFlag_normalizer ρ hρ U hU
  have hlt : k < Module.finrank (ZMod 2) V := by
    apply lt_of_le_of_ne hbound
    intro he
    apply hn
    rw [heq]
    exact fullFlag_isPGroup ρ hρ W hs hzero hlast he
  let f : Fin (k-1) → Fin (k+1) := fun i => ⟨i.val+1,by omega⟩
  have hf : StrictMono f := by intro i j hij; change i.val+1<j.val+1; exact Nat.add_lt_add_right hij 1
  refine ⟨k-1,W ∘ f,by omega,by omega,hs.comp hf,?_,?_⟩
  · intro i
    have ha : (0 : Fin (k+1)) < f i := by change (0 : ℕ) < i.val + 1; omega
    have hb : f i < Fin.last k := by change i.val+1<k; have := i.isLt; omega
    exact ⟨by simpa only [Function.comp_apply,hzero] using (hs ha).ne.symm,
      by simpa only [Function.comp_apply,hlast] using (hs hb).ne⟩
  · rw [heq]
    apply le_antisymm
    · intro g hg
      simp only [Subgroup.mem_iInf]
      intro i
      exact (mem_flagStabilizer ρ W).mp hg (f i)
    · intro g hg
      simp only [Subgroup.mem_iInf] at hg
      apply (mem_flagStabilizer ρ W).mpr
      intro i v
      by_cases hi : i=0
      · subst i
        rw [hzero]
        simp only [Submodule.mem_bot]
        constructor
        · intro hv
          have hh := congrArg (ρ g⁻¹) hv
          simpa only [map_zero,←Module.End.mul_apply,←map_mul,inv_mul_cancel,
            map_one,Module.End.one_apply] using hh
        · rintro rfl; exact map_zero _
      by_cases hi' : i=Fin.last k
      · subst i
        simp only [hlast,Submodule.mem_top]
      · let j : Fin (k-1) := ⟨i.val-1,by
          have ht := i.isLt
          have hz : i.val ≠ 0 := by intro hz; exact hi (Fin.ext hz)
          have hl : i.val ≠ k := by intro hl; exact hi' (Fin.ext hl)
          omega⟩
        have hji : f j = i := by
          apply Fin.ext
          have hz : i.val ≠ 0 := by intro hz; exact hi (Fin.ext hz)
          change i.val-1+1=i.val
          omega
        simpa only [Function.comp_apply,hji] using hg j v

end Representation.BinaryRadical

module
public import Glauberman.BaumannResidualLayer

/-!
# Fixed-index bounds completing the all-abelian Baumann Sylow argument

In a normal elementary layer D, fixed points of the Baumann subgroup are
exactly D intersect Ω₁Z(J(P)), with J defined by all maximum-order abelian
subgroups. For two opposite Baumann conjugates, their common fixed points
are the full central part of D when the whole two-core centralizes D.

An upper bound r for one fixed index and a lower bound r² for the global
fixed index force equality in the intersection-index inequality. The two
fixed subgroups therefore span D. Applying the abelian supplement argument
to the normal layer Ω₁Z(J(P))D puts the whole core in Baumann, proving that
Baumann equals P. This does not assume either fixed-index bound.

Source: the Baumann step of MS93 (5.1), printed p.913; compare the
opposite-fixed-space argument in Stellmacher (1997), (2.3), p.20. The actual
replacement application is CriticalReduction.RootProductResidualLayer,
with r the cardinality of the original nonbinary field.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

private theorem sup_eq_of_relative_indices
    (D A C : Subgroup G) [IsMulCommutative D]
    (hAD : A ≤ D) (hCD : C ≤ D)
    (hi : (A ⊓ C).relIndex D = A.relIndex D * C.relIndex D) :
    A ⊔ C = D := by
  let A₀ := A.subgroupOf D
  let C₀ := C.subgroupOf D
  let : A₀.Normal := normal_of_isMulCommutative A₀
  have hi' : (A₀ ⊓ C₀).index = A₀.index * C₀.index := by
    change (A.subgroupOf D ⊓ C.subgroupOf D).index = _
    exact hi
  have hmul := relIndex_inf_mul_relIndex A₀ C₀ ⊤
  simp only [inf_top_eq,relIndex_top_right] at hmul
  have hAc : A₀.relIndex C₀ = A₀.index := Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := C₀))) (hmul.trans hi')
  have hjoin := relIndex_mul_index (show A₀ ≤ A₀ ⊔ C₀ from le_sup_left)
  rw [relIndex_sup_left,hAc] at hjoin
  have htop : A₀ ⊔ C₀ = ⊤ := index_eq_one.mp
    (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := A₀))) (by simpa using hjoin))
  have hh := congrArg (Subgroup.map D.subtype) htop
  rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hAD,map_subgroupOf_eq_of_le hCD,
    ←MonoidHom.range_eq_map,range_subtype] at hh

/-- In a normal elementary layer, Baumann-fixed points are precisely its
intersection with the full all-abelian Thompson central omega. -/
theorem elementary_fixed_baumann (S : Sylow 2 G) (D : Subgroup G)
    [D.Normal] [IsElementaryAbelian 2 D] :
    D ⊓ centralizer (baumannSubgroup (S : Subgroup G) : Set G) =
      D ⊓ omegaCenterIn (thompsonSubgroup (S : Subgroup G)) := by
  have hD : D ≤ (S : Subgroup G) := (IsElementaryAbelian.isPGroup 2 D).le_sylow_of_normal S
  have hh := smallMover_fixed_le_thompson_omega D (S : Subgroup G)
    (baumannSubgroup (S : Subgroup G)) hD (thompson_le_baumann _)
  apply le_antisymm (le_inf inf_le_left hh)
  intro z hz
  exact ⟨hz.1,fun b hb => (hb.2 z hz.2).symm⟩

/-- Matching single and double fixed-index bounds supply the opposite spanning
premise in the Baumann Sylow argument. The entire central fixed part of D
is retained in the global index. -/
theorem baumann_eq_sylow_of_fixed_index_bounds
    (S : Sylow 2 G) (D : Subgroup G) [D.Normal] [IsElementaryAbelian 2 D]
    [IsElementaryAbelian 2
      (omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊔ D : Subgroup G)]
    [(omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊔ D : Subgroup G).Normal]
    (hgen : normalClosure (baumannSubgroup (S : Subgroup G) : Set G) = ⊤)
    (hsupp : baumannSubgroup (S : Subgroup G) ⊔ pCore 2 G = (S : Subgroup G))
    (hcore : D ≤ centralizer (pCore 2 G : Set G))
    (x : G)
    (hopp : (baumannSubgroup (S : Subgroup G) ⊔
      (baumannSubgroup (S : Subgroup G)).map (MulAut.conj x).toMonoidHom) ⊔ pCore 2 G = ⊤)
    (r : ℕ) (hi : (centralizer (baumannSubgroup (S : Subgroup G) : Set G)).relIndex D ≤ r)
    (hiG : r ^ 2 ≤ (center G).relIndex D) :
    pCore 2 G ≤ centralizer
      (omegaCenterIn (thompsonSubgroup (S : Subgroup G)) : Set G) ∧
    baumannSubgroup (S : Subgroup G) = (S : Subgroup G) := by
  let B := baumannSubgroup (S : Subgroup G)
  let Z := omegaCenterIn (thompsonSubgroup (S : Subgroup G))
  let e := (MulAut.conj x).toMonoidHom
  let A := D ⊓ centralizer (B : Set G)
  have hDm : D.map e = D := Normal.map_conj_eq _ x
  have hAm : A.map e = D ⊓ centralizer (B.map e : Set G) := by
    rw [←map_inf_centralizer_of_injective e (MulAut.conj x).injective,hDm]
  have hAD : A ≤ D := inf_le_left
  have hAxD : A.map e ≤ D := hDm ▸ map_mono hAD
  have hinter : A ⊓ A.map e = D ⊓ center G := by
    rw [hAm]
    apply le_antisymm
    · intro z hz
      refine ⟨hz.1.1,mem_center_iff.mpr ?_⟩
      have hc : (⊤ : Subgroup G) ≤ centralizer ({z} : Set G) := by
        rw [←hopp]
        apply sup_le (sup_le ?_ ?_) ?_
        · intro b hb y hy
          rcases Set.mem_singleton_iff.mp hy with rfl
          exact (hz.1.2 b hb).symm
        · intro b hb y hy
          rcases Set.mem_singleton_iff.mp hy with rfl
          exact (hz.2.2 b hb).symm
        · intro q hq y hy
          rcases Set.mem_singleton_iff.mp hy with rfl
          exact (hcore hz.1.1 q hq).symm
      intro g
      exact (hc (mem_top g) z (Set.mem_singleton z)).symm
    · intro z hz
      exact ⟨⟨hz.1,fun b _ => mem_center_iff.mp hz.2 b⟩,
        ⟨hz.1,fun b _ => mem_center_iff.mp hz.2 b⟩⟩
  have hAi : A.relIndex D = (centralizer (B : Set G)).relIndex D := inf_relIndex_left _ _
  have hAxi : (A.map e).relIndex D = A.relIndex D := by
    calc
      (A.map e).relIndex D = (A.map e).relIndex (D.map e) := by rw [hDm]
      _ = A.relIndex D := relIndex_map_map_of_injective _ _ (MulAut.conj x).injective
  have hiEq : (A ⊓ A.map e).relIndex D = A.relIndex D * (A.map e).relIndex D := by
    apply le_antisymm relIndex_inf_le
    rw [hinter,inf_relIndex_left,hAxi,hAi]
    exact (Nat.mul_le_mul hi hi).trans (by simpa only [pow_two,inf_relIndex_left] using hiG)
  have hjoin : A ⊔ A.map e = D := sup_eq_of_relative_indices D A (A.map e) hAD hAxD hiEq
  have hAZ : A = D ⊓ Z := elementary_fixed_baumann S D
  apply baumann_eq_sylow_of_residual_fixed_span S D hgen hsupp hcore x hopp
  apply hjoin.symm.le.trans
  apply sup_le
  · rw [hAZ]
    exact le_sup_left
  · have hh : A.map e = D ⊓ Z.map e := by
      rw [hAZ,Subgroup.map_inf _ _ _ (MulAut.conj x).injective,hDm]
    rw [hh]
    exact le_sup_right
end Glauberman

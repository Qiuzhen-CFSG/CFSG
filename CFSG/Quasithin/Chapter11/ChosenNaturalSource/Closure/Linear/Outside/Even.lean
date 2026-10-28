module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Setup
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Preserving the moved subgroup in the even-degree ending

If C has abelian image on W/V₁, its kernel N makes X₀N invariant.
Since [N,W]≤V₁≤V, adjoining N to X₀ leaves [W,X₀]=V unchanged.
Thus C preserves V. The original two-residual lies in C, and its Sylow
supplement is T, so the selected H lies in M, a contradiction.

The actual order-three X₀ and its moved-subgroup identity remain with
the marked SL₃ calculation. This module proves the lifting step from
the literal quotient action, rather than assuming preservation of V.
Source: Aschbacher--Smith, 11.5.7, printed p.782.
-/

public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

omit [Finite G] in
private theorem normalizes_join_modulo (A B N : Subgroup G)
    (hAN : A ≤ normalizer (N : Set G)) (hc : ⁅A,B⁆ ≤ N) :
    A ≤ normalizer ((B ⊔ N : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha b hb
  let f := (MulAut.conj a).toMonoidHom
  have hB : B.map f ≤ B ⊔ N := by
    rintro _ ⟨v, hv, rfl⟩
    have he : f v = ⁅a,v⁆ * v := by
      simp [f, commutatorElement_def, mul_assoc]
    rw [he]
    exact (B ⊔ N).mul_mem (mem_sup_right (hc (commutator_mem_commutator ha hv)))
      (mem_sup_left hv)
  have hN : N.map f ≤ N := by
    rintro _ ⟨n, hn, rfl⟩
    exact le_normalizer_iff.mp hAN a ha n hn
  have hm : (B ⊔ N).map f ≤ B ⊔ N := by
    rw [Subgroup.map_sup]
    exact sup_le hB (hN.trans le_sup_right)
  exact hm (mem_map_of_mem f hb)

/-- Lift invariance through the actual action kernel, retaining the whole V. -/
theorem C_normalizes_moved_seed
    (hCG : C E ≤ E.G₁)
    (hab : IsMulCommutative (quotientAction E (C E) hCG).range)
    (X₀ : Subgroup G) (hX : X₀ ≤ X₁ E) (hmove : ⁅E.W,X₀⁆ = V) :
    C E ≤ normalizer (V : Set G) := by
  let α := quotientAction E (C E) hCG
  let N := (actionCentralizer E (C E) hCG).map (C E).subtype
  have hCN : C E ≤ normalizer (N : Set G) := by
    apply le_normalizer_iff.mpr
    rintro c hc _ ⟨n, hn, rfl⟩
    exact ⟨(⟨c,hc⟩ : C E) * n * ⟨c,hc⟩⁻¹,
      (inferInstance : (actionCentralizer E (C E) hCG).Normal).conj_mem n hn ⟨c,hc⟩, rfl⟩
  have hNW : ⁅N,E.W⁆ ≤ E.V₁ := by
    apply commutator_le.mpr
    rintro n ⟨a,ha,rfl⟩ w hw
    exact (mem_actionCentralizer_iff E (C E) hCG a).mp ha w hw
  have hXC : X₀ ≤ C E := hX.trans le_sup_right
  have hCX : ⁅C E,X₀⁆ ≤ N := by
    apply commutator_le.mpr
    intro c hc x hx
    let c' : C E := ⟨c,hc⟩
    let x' : C E := ⟨x,hXC hx⟩
    refine ⟨⁅c',x'⁆, ?_, rfl⟩
    apply MonoidHom.mem_ker.mpr
    change α ⁅c',x'⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact congrArg Subtype.val ((isMulCommutative_iff.mp hab)
      (α.rangeRestrict c') (α.rangeRestrict x'))
  have hCJ := normalizes_join_modulo (C E) X₀ N hCN hCX
  have hNV : N ≤ normalizer (V : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr
      (((commutator_mono le_rfl (le_conjugateSpanBy V E.G₁)).trans hNW).trans E.V₁_le)
  have hXV : X₀ ≤ normalizer (V : Set G) :=
    hmove ▸ normalizer_commutator_ge_right E.W X₀
  have he : ⁅E.W,X₀ ⊔ N⁆ = V := by
    apply le_antisymm
    · rw [commutator_comm]
      exact commutator_sup_le_of_relative_normal (X₀ ⊔ N) X₀ N E.W V
        (sup_le hXV hNV) le_sup_left le_sup_right
        (by rw [commutator_comm, hmove]) (hNW.trans E.V₁_le)
    · exact hmove.ge.trans (commutator_mono le_rfl le_sup_left)
  suffices hh : C E ≤ normalizer ((⁅E.W,X₀ ⊔ N⁆ : Subgroup G) : Set G) by
    simpa only [he] using hh
  intro c hc
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hCW : C E ≤ normalizer (E.W : Set G) :=
    hCG.trans (le_normalizer_conjugateSpanBy V E.G₁)
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hCW hc),
    mem_normalizer_iff_map_conj_eq.mp (hCJ hc)]

/-- The original outside-H contradiction from the marked moved subgroup. -/
theorem contradiction_of_moved_seed
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁)
    (hab : IsMulCommutative
      (quotientAction E (C E)
        (C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG)).range)
    (X₀ : Subgroup G) (hX : X₀ ≤ X₁ E) (hmove : ⁅E.W,X₀⁆ = V) : False := by
  have hCN := C_normalizes_moved_seed E
    (C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG) hab X₀ hX hmove
  have hRM : outsideResidual E ≤ E.M :=
    (show outsideResidual E ≤ C E from le_sup_of_le_left le_sup_right).trans
      (hCN.trans (seed_normalizer_le_M E))
  have hTH : (T : Subgroup G) ≤ E.H := hH.1.1.2
  have he : outsideResidual E ⊔ (T : Subgroup G) = E.H := by
    have hh := congrArg (map E.H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
    simpa only [outsideResidual, Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
      Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using hh
  exact hH.1.2 (he ▸ sup_le hRM D.sylow_normalizes_component)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside

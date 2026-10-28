module

public import Theory.SpecificGroups.PSL2.QuinticCentralizerWholeFusion
public import Theory.SpecificGroups.PSL2.QuinticCentralInvolutionEscape
public import Theory.GroupTheory.OddCentralizerWholeSubgroupPlacement

/-!
# Whole elementary fusion in a field-involution extension

Let a normal self-centralizing odd PSL₂ component generate the ambient group
with a marked element a of the elementary subgroup. An odd-index PGL₂ model
on the actual inner centralizer of a suffices for whole-subgroup fusion out
of the quintic two-core. The simultaneous Sylow placement is retained in both
branches: cyclic groups use Z-star, and noncyclic groups fuse their inner part
inside the marked centralizer.

The quadratic semilinear calculation supplies the two structural centralizer
facts. This is the whole-subgroup assembly in Aschbacher--Smith 6.1.4, p.666.
-/

public section
open Subgroup GorensteinWalter Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2

private noncomputable def inner_centralizer_conj
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (a g : G) :
    (centralizer ({a} : Set G)).subgroupOf N ≃*
      (centralizer ({g * a * g⁻¹} : Set G)).subgroupOf N := by
  let d : MulAut N := MulAut.conjNormal g
  have hc : ((centralizer ({a} : Set G)).subgroupOf N).map d.toMonoidHom =
      (centralizer ({g * a * g⁻¹} : Set G)).subgroupOf N := by
    apply le_antisymm
    · rintro _ ⟨n, hn, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      change (MulAut.conj g (n : G)) * MulAut.conj g a =
        MulAut.conj g a * MulAut.conj g (n : G)
      have hh : (n : G) * a = a * n := mem_centralizer_singleton_iff.mp hn
      exact (map_mul (MulAut.conj g) (n : G) a).symm.trans
        ((congrArg (MulAut.conj g) hh).trans (map_mul (MulAut.conj g) a (n : G)))
    · intro n hn
      refine ⟨d.symm n, ?_, d.apply_symm_apply n⟩
      apply mem_centralizer_singleton_iff.mpr
      change ((MulAut.conjNormal g).symm n : G) * a =
        a * ((MulAut.conjNormal g).symm n : G)
      rw [MulAut.conjNormal_symm_apply]
      have hh : (n : G) * (g * a * g⁻¹) = (g * a * g⁻¹) * n :=
        mem_centralizer_singleton_iff.mp hn
      calc
        _ = g⁻¹ * ((n : G) * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * a * g⁻¹) * n) * g := by rw [hh]
        _ = _ := by group
  exact (d.subgroupMap _).trans (MulEquiv.subgroupCongr hc)

/-- The two actual fixed-centralizer facts yield one conjugator of the
whole original elementary subgroup, retained in the normal PSL₂ component. -/
theorem odd_quintic_whole_fusion_of_inner_centralizer
    {G : Type*} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F]
    {E : Type*} [Field E] [Finite E]
    (hF : IsOddPrimePower (Nat.card F)) (h8 : 8 ∣ Nat.card PSL(2,F))
    (hE : IsOddPrimePower (Nat.card E))
    (N : Subgroup G) [N.Normal] (e : N ≃* PSL(2,F))
    (hC : centralizer (N : Set G) = ⊥)
    (T : Sylow 2 G) (X : Subgroup G) (hXN : X ≤ N) (hfive : Nat.card X = 5)
    (hTX : (T : Subgroup G) ≤ normalizer X)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (a : G) (haA : a ∈ A) (hgen : N ⊔ zpowers a = ⊤)
    (hi : Odd ((centralizer ({a} : Set G)).subgroupOf N).index)
    (eC : (centralizer ({a} : Set G)).subgroupOf N ≃* PGL2 E) :
    ∃ g ∈ N, A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ A.map (MulAut.conj g).toMonoidHom ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  classical
  let : IsElementaryAbelian 2 A := hA
  let : CommGroup A := IsMulCommutative.instCommGroup
  let S := (X ⊔ (T : Subgroup G)).pCoreIn 2
  have hAC : A ≤ centralizer ({a} : Set G) := by
    intro v hv
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨v, hv⟩ : A) ⟨a, haA⟩)
  obtain ⟨g, hg, hBT, hbC⟩ := odd_centralizer_whole_subgroup_placement N a hgen hi A
    (IsElementaryAbelian.isPGroup 2 A) haA hAC T
  let B := A.map (MulAut.conj g).toMonoidHom
  let b := g * a * g⁻¹
  have hbB : b ∈ B := mem_map_of_mem _ haA
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hBne : B ≠ ⊥ := fun hh => hAne ((A.map_eq_bot_iff_of_injective (MulAut.conj g).injective).mp hh)
  have hgenb : N ⊔ zpowers b = ⊤ := by
    apply top_unique
    rw [← hgen]
    refine sup_le le_sup_left (zpowers_le.mpr ?_)
    have hg' : g ∈ N ⊔ zpowers b := (show N ≤ N ⊔ zpowers b from le_sup_left) hg
    have hb' : b ∈ N ⊔ zpowers b := (show zpowers b ≤ N ⊔ zpowers b from le_sup_right) (mem_zpowers b)
    have hh := (N ⊔ zpowers b).mul_mem ((N ⊔ zpowers b).mul_mem
      ((N ⊔ zpowers b).inv_mem hg') hb') hg'
    change g⁻¹ * (g * a * g⁻¹) * g ∈ _ at hh
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  by_cases hBS : B ≤ S
  · have hk : ∃ k ∈ N, B.map (MulAut.conj k).toMonoidHom ≤ (T : Subgroup G) ∧
        ¬ B.map (MulAut.conj k).toMonoidHom ≤ S := by
      by_cases hBN : B ⊓ N = ⊥
      · have hBZ : B = zpowers b := by
          apply le_antisymm _ (zpowers_le.mpr hbB)
          intro v hv
          obtain ⟨n, hn, z, hz, he⟩ := mem_sup_of_normal_left.mp (hgenb ▸ mem_top v)
          have hzB : z ∈ B := (zpowers_le.mpr hbB) hz
          have hnB : n ∈ B := by
            have hh := B.mul_mem hv (B.inv_mem hzB)
            rwa [← he, mul_inv_cancel_right] at hh
          have hn1 : n = 1 := mem_bot.mp (hBN ▸ (show n ∈ B ⊓ N from ⟨hnB, hn⟩))
          rw [hn1, one_mul] at he
          exact he ▸ hz
        have hb1 : b ≠ 1 := by intro he; apply hBne; rw [hBZ, he, zpowers_one_eq_bot]
        have hb2 : b ^ 2 = 1 := by
          let : IsElementaryAbelian 2 B := hB
          exact elemPow_eq_one_of_isElementaryAbelian b hbB
        have hgenT : N ⊔ (T : Subgroup G) = ⊤ := top_unique (hgenb ▸
          sup_le_sup_left (zpowers_le.mpr (hBT hbB)) N)
        obtain ⟨k, hk, hkT, hkS⟩ := odd_quintic_central_involution_escape hF h8 N e hC
          T hgenT X hXN hfive hTX b (hBS hbB) hb2 hb1 hbC
        refine ⟨k, hk, ?_, ?_⟩
        · rw [hBZ, MonoidHom.map_zpowers]
          exact zpowers_le.mpr hkT
        · rw [hBZ, MonoidHom.map_zpowers]
          exact fun hh => hkS (hh (mem_zpowers _))
      · exact quintic_inner_centralizer_whole_fusion hE N T X hXN hfive hTX B hB hBS
          b hbB hbC hgenb hBN ((inner_centralizer_conj N a g).symm.trans eC)
    obtain ⟨k, hk, hkT, hkS⟩ := hk
    have hmap : B.map (MulAut.conj k).toMonoidHom = A.map (MulAut.conj (k * g)).toMonoidHom := by
      rw [map_map]
      congr 1
      ext v
      change k * (g * v * g⁻¹) * k⁻¹ = (k * g) * v * (k * g)⁻¹
      group
    exact ⟨k * g, N.mul_mem hk hg, hmap ▸ hkT, hmap ▸ hkS⟩
  · exact ⟨g, hg, hBT, hBS⟩

end Theory.PSL2

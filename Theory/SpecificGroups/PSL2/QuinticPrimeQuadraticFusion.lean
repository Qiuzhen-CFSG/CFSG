module

public import Theory.SpecificGroups.PSL2.QuinticQuadraticExtensionFusion
public import Theory.SpecificGroups.PSL2.QuinticInnerExtensionFusion
public import Theory.SpecificGroups.PSL2.QuinticLinearCoreFour
public import Mathlib.Algebra.Group.Shrink

/-!
# Whole quintic-core fusion in odd prime and quadratic PSL₂ extensions

The actual conjugation embedding separates the elementary subgroup by its
coefficient action. A quadratic field involution gives simultaneous fusion
by the proved field-extension theorem. If the coefficient action is trivial,
the normal linear kernel and its self-centralizing inner Klein four force
the entire elementary subgroup into the original PSL₂ component; inner
fusion then applies. Prime fields have no nontrivial coefficient action.

The conjugator always lies in the prescribed normal component and carries
the whole subgroup into the original Sylow outside the original O₂(XT).
This is the odd-PSL₂ model fusion step of Aschbacher--Smith 6.1.4, p.666.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

private theorem trivial_field_le_inner
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (N : Subgroup G) [N.Normal] (e : N ≃* PSL(2,F))
    (f : G →* PGammaL2 F) (hfi : Function.Injective f)
    (hfn : ∀ n : N, f n = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (e n)))
    (T : Sylow 2 G) (X : Subgroup G) (hXN : X ≤ N) (hfive : Nat.card X = 5)
    (hTX : (T : Subgroup G) ≤ normalizer X)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAS : A ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2)
    (hfield : ∀ a ∈ A, (f a).right = 1) : A ≤ N := by
  let H := (pGammaL2PGLRange F).comap f
  let l : H →* PGL2 F := (pGammaL2PGLRangeEquiv F).symm.toMonoidHom.comp
    (f.subgroupComap (pGammaL2PGLRange F))
  have hli : Function.Injective l := (pGammaL2PGLRangeEquiv F).symm.injective.comp
    (fun _ _ he => Subtype.ext (hfi (congrArg Subtype.val he)))
  have hNH : N ≤ H := by
    intro n hn
    change f n ∈ pGammaL2PGLRange F
    rw [hfn ⟨n, hn⟩]
    exact ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL (e ⟨n, hn⟩), rfl⟩
  have hAH : A ≤ H := by
    intro a ha
    change f a ∈ pGammaL2PGLRange F
    refine ⟨(f a).left, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact (hfield a ha).symm
  obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_normal N
  let P := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let j : PSL(2,F) →* G := N.subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := N.subtype_injective.comp e.symm.injective
  have hPT : (P : Subgroup PSL(2,F)).map j ≤ (T : Subgroup G) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨n, hn, rfl⟩ := hv
    change (e.symm (e n) : G) ∈ (T : Subgroup G)
    rw [e.symm_apply_apply]
    rw [hQ] at hn
    exact hn
  obtain ⟨m, hm, ⟨eP⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hF P
  obtain ⟨V, hVP, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (P : Subgroup PSL(2,F)) hm eP
  have hVN : V.map j ≤ N := by
    rintro _ ⟨v, hv, rfl⟩
    exact (e.symm v).property
  have hAV := odd_quintic_linear_core_le_four hF H l hli T X (hXN.trans hNH) hfive hTX
    (V.map j) (isKleinFour_map_of_injective V hV j hj)
    ((map_mono hVP).trans hPT) (hVN.trans hNH) A hA hAS hAH
  exact hAV.trans hVN

/-- In an actual self-centralizing normal PSL₂ extension over an odd prime
or quadratic field, every nonzero elementary subgroup of O₂(XT) has one
component conjugate returning to T and escaping that same O₂(XT). -/
private theorem same_universe_whole_fusion
    {G : Type} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] {p d : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : d = 1 ∨ d = 2) (hF : Nat.card F = p ^ d)
    (hc : 3 < Nat.card F)
    (N : Subgroup G) [N.Normal] (e : N ≃* PSL(2,F))
    (hC : centralizer (N : Set G) = ⊥)
    (T : Sylow 2 G) (X : Subgroup G) (hXN : X ≤ N) (hfive : Nat.card X = 5)
    (hTX : (T : Subgroup G) ≤ normalizer X)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hAS : A ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2) :
    ∃ g ∈ N, A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ A.map (MulAut.conj g).toMonoidHom ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  classical
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F))
    DFunLike.coe_injective
  have hdpos : 0 < d := by rcases hd with he | he <;> omega
  let hodd : IsOddPrimePower (Nat.card F) := ⟨p, d, Fact.out, ho, hdpos, hF⟩
  let hs := pGammaL2ToMulAutPSL2_surjective F hF hodd hc
  let f := normalPSL2ToPGammaL2 N F hodd hc e hs
  have hfi : Function.Injective f := normalPSL2ToPGammaL2_injective N F hodd hc e hC hs
  have hfn (n : N) : f n = SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (e n)) :=
    normalPSL2ToPGammaL2_apply_subtype N F hodd hc e hs n
  by_cases hex : ∃ a ∈ A, (f a).right ≠ 1
  · obtain ⟨a, haA, haF⟩ := hex
    rcases hd with hd | hd
    · have hcard : Nat.card (F ≃+* F) = 1 := by
        rw [FiniteField.card_ringAut_of_card_prime_pow (Fact.out : p.Prime) hF, hd]
      let : Nontrivial (F ≃+* F) := ⟨⟨(f a).right, 1, haF⟩⟩
      have hh : 1 < Nat.card (F ≃+* F) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    · subst d
      have hST : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
        have hh := (X ⊔ (T : Subgroup G)).pCoreIn_le_sylow
          (T.subtype (show (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) from le_sup_right))
        change (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤
          ((T : Subgroup G).subgroupOf (X ⊔ (T : Subgroup G))).map (X ⊔ (T : Subgroup G)).subtype at hh
        rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) from le_sup_right)] at hh
      exact quintic_quadratic_extension_whole_fusion ho hF N e hC T X hXN hfive hTX
        A hA hAne (hAS.trans hST) a haA haF
  · have hfield (a : G) (ha : a ∈ A) : (f a).right = 1 := by
      by_contra hn
      exact hex ⟨a, ha, hn⟩
    have hAN := trivial_field_le_inner hodd N e f hfi hfn T X hXN hfive hTX A hA hAS hfield
    exact odd_quintic_inner_extension_whole_fusion hodd N e T X hXN hfive hTX A hA hAne hAN hAS


/-- The prime-or-quadratic whole-subgroup fusion theorem on the original
ambient objects, with no restriction on the ambient universe. -/
theorem odd_prime_quadratic_quintic_whole_fusion
    {G : Type*} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] {p d : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : d = 1 ∨ d = 2) (hF : Nat.card F = p ^ d)
    (hc : 3 < Nat.card F)
    (N : Subgroup G) [N.Normal] (e : N ≃* PSL(2,F))
    (hC : centralizer (N : Set G) = ⊥)
    (T : Sylow 2 G) (X : Subgroup G) (hXN : X ≤ N) (hfive : Nat.card X = 5)
    (hTX : (T : Subgroup G) ≤ normalizer X)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hAS : A ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2) :
    ∃ g ∈ N, A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ A.map (MulAut.conj g).toMonoidHom ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  classical
  let k : G ≃* Shrink.{0} G := Shrink.mulEquiv.symm
  let : Finite (Shrink.{0} G) := Finite.of_surjective k k.surjective
  let N' := N.map k.toMonoidHom
  let X' := X.map k.toMonoidHom
  let A' := A.map k.toMonoidHom
  let T' := T.mapSurjective (f := k.toMonoidHom) k.surjective
  let : N'.Normal := (inferInstance : N.Normal).map k.toMonoidHom k.surjective
  let e' : N' ≃* PSL(2,F) := (k.subgroupMap N).symm.trans e
  have hC' : centralizer (N' : Set (Shrink.{0} G)) = ⊥ := by
    apply bot_unique
    intro c hc'
    have hh : k.symm c ∈ centralizer (N : Set G) := by
      intro n hn
      apply k.injective
      simpa only [map_mul, k.apply_symm_apply] using hc' (k n) (mem_map_of_mem _ hn)
    rw [hC] at hh
    apply mem_bot.mpr
    apply k.symm.injective
    simpa only [map_one] using mem_bot.mp hh
  have hX'N' : X' ≤ N' := map_mono hXN
  have hfive' : Nat.card X' = 5 := by
    rw [card_map_of_injective k.injective]
    exact hfive
  have hT'X' : (T' : Subgroup (Shrink.{0} G)) ≤ normalizer X' := by
    have hh := map_mono (f := k.toMonoidHom) hTX
    rwa [map_equiv_normalizer_eq] at hh
  have hA' : IsElementaryAbelian 2 A' := by
    let : IsElementaryAbelian 2 A := hA
    exact IsElementaryAbelian.map k.toMonoidHom
  have hAne' : A' ≠ ⊥ := fun he => hAne ((A.map_eq_bot_iff_of_injective k.injective).mp he)
  have hS : ((X ⊔ (T : Subgroup G)).pCoreIn 2).map k.toMonoidHom =
      (X' ⊔ (T' : Subgroup (Shrink.{0} G))).pCoreIn 2 := by
    rw [← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ k.injective,
      Subgroup.map_sup]
    rfl
  have hA'S : A' ≤ (X' ⊔ (T' : Subgroup (Shrink.{0} G))).pCoreIn 2 :=
    (map_mono hAS).trans hS.le
  obtain ⟨g, hg, hgT, hgS⟩ := same_universe_whole_fusion ho hd hF hc N' e' hC'
    T' X' hX'N' hfive' hT'X' A' hA' hAne' hA'S
  have hgN : k.symm g ∈ N := by
    obtain ⟨n, hn, rfl⟩ := hg
    change k.symm (k n) ∈ N
    rwa [k.symm_apply_apply]
  have hmap : (A.map (MulAut.conj (k.symm g)).toMonoidHom).map k.toMonoidHom =
      A'.map (MulAut.conj g).toMonoidHom := by
    rw [map_map, map_map]
    apply congrArg (fun z : G →* Shrink.{0} G => A.map z)
    apply MonoidHom.ext
    intro v
    change k (k.symm g * v * (k.symm g)⁻¹) = g * k v * g⁻¹
    simp only [map_mul, map_inv, k.apply_symm_apply]
  refine ⟨k.symm g, hgN, ?_, ?_⟩
  · apply (map_le_map_iff_of_injective (f := k.toMonoidHom) k.injective).mp
    rw [hmap]
    exact hgT
  · intro hh
    apply hgS
    rw [← hmap, ← hS]
    exact map_mono hh

end Theory.PSL2

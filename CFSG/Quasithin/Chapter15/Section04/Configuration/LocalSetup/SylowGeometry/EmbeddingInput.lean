module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.FactorActors
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.RControl
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry

/-!
# Intrinsic embedding inputs for the Sylow contradiction

From the full symmetric-three product quotient of `XS` and the actual
factor permutation by `U`, construct the independent inversion and exchange
witnesses, canonical `X ∈ Ξ(G,U)`, a noncommutative quotient action, and an
explicit inverting element of `Φ(U)`. The movement hypothesis may concern
either factor. The two-perfect and order-nine assumptions are the preceding
source facts about `X`; no Xi membership is assumed in this construction.

For the local group `H=I₀`, Sylow restriction and the proved Chapter 1
transport then give intrinsic Xi membership and all conclusions of 1.3.2,
including the complement, both generation statements, literal Frattini
irreducibility, Frattini commutators, and the two-residual equality. SQTK
is inherited from the genuine ambient simple QTKE hypothesis.

This supplies the input to the intrinsic local form of 1.3.4. It does not
assert its classification alternatives, identify the quotient action as D₈,
or complete either generalized-Fitting case of 15.4.20.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.3.1–4,
printed pp.508–509; the local-use explanation on p.1052; and 15.4.20, p.1164.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
variable {G : Type*} [Group G] [Finite G]

/-- The full product and actual factor movement construct Xi membership and
an inverting Frattini commutator, uniformly for either chosen factor. -/
theorem contrary_Xi_from_full_product
    (X S U : Subgroup G) (hU : IsPGroup 2 U) (hSU : S ≤ U)
    (hn : U ≤ normalizer (X : Set G))
    (hperfect : IsPPerfect 2 X) (hcore : X.pCoreIn 2 ≠ ⊥)
    (e : (X ⧸ pCore 2 X) ≃* Multiplicative (ZMod 3 × ZMod 3))
    (L : Bool → Subgroup G) (hL : L false ⊔ L true = X)
    (f : (X ⊔ S : Subgroup G) →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hf : Function.Surjective f) (hker : f.ker = pCore 2 (X ⊔ S : Subgroup G))
    (hf1 : ((L false).subgroupOf (X ⊔ S)).map f = (alternatingGroup (Fin 3)).prod ⊥)
    (hf2 : ((L true).subgroupOf (X ⊔ S)).map f =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)))
    (hp : ∀ u ∈ U, ∀ V ∈ ({L false, L true} : Set (Subgroup G)),
      V.map (MulAut.conj u).toMonoidHom ∈ ({L false, L true} : Set (Subgroup G)))
    (i : Bool) (hmove : ¬ U ≤ normalizer (L i : Set G)) :
    X ∈ Chapter1.Xi G U ∧
      let α := (quotientAut (pCore 2 X)).comp (X.normalizerMonoidHom.comp (inclusion hn))
      (¬ IsMulCommutative α.range) ∧
      ∃ a b : U, ⁅a,b⁆ ∈ frattini U ∧ ∀ x : X ⧸ pCore 2 X, α ⁅a,b⁆ x = x⁻¹ := by
  let A1 := ((L false).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  let A2 := ((L true).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  obtain ⟨hgen,hcard1,hcard2,a,hinv,hfix⟩ :=
    independent_inverter_from_product X S U hSU hn L hL f hf hker hf1 hf2
  obtain ⟨b,hb1,hb2⟩ := quotient_factor_exchange_of_movement X U hn L hL hp i hmove
  have hH : X ⊔ U ∈ Chapter1.H G := by
    have hc : X.pCoreIn 2 ≤ (X ⊔ U : Subgroup G).pCoreIn 2 :=
      le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X)
        ((pCoreIn_le 2 X).trans le_sup_left)
        ((sup_le X.le_normalizer hn).trans
          (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
    exact fun he => hcore (le_bot_iff.mp (he ▸ hc))
  have hXi := contrary_X_mem_Xi_of_factor_exchange X U hn hperfect hH e
    A1 A2 hgen hcard1 hcard2 a b hinv hfix hb1 hb2
  let : IsElementaryAbelian 3 (X ⧸ pCore 2 X) := (order_nine_quotient_structure e).1
  let α := (quotientAut (pCore 2 X)).comp (X.normalizerMonoidHom.comp (inclusion hn))
  refine ⟨hXi, not_commutative_image_of_factor_exchange α A1 A2 hgen hcard1 a b
    hinv hfix hb1 hb2, a,b,?_⟩
  exact frattini_inverter_of_factor_exchange hU α A1 A2 hgen a b hinv hfix hb1 hb2


/-- All genuine 1.3.2 inputs for the intrinsic SQTK embedding argument. The
Xi premise is constructed by `contrary_Xi_from_full_product`; the local Sylow
condition is derived from the actual Sylow subgroup of `H`. -/
theorem contrary_intrinsic_embedding_inputs {K : GroupClass} (hG : IsSimpleQTKE K G)
    {X U H : Subgroup G} (hH : H ∈ Chapter1.H G) (hXH : X ≤ H)
    (P₂ : Sylow 2 H) (hP₂ : (P₂ : Subgroup H).map H.subtype = U)
    (hXi : X ∈ Chapter1.Xi G U)
    (e : (X ⧸ pCore 2 X) ≃* Multiplicative (ZMod 3 × ZMod 3))
    (P : Sylow 3 X) :
    let P₀ := (P : Subgroup X).map X.subtype
    let N := U ⊓ normalizer (P₀ : Set G)
    IsSQTK K H ∧ X.subgroupOf H ∈ Chapter1.Xi H (U.subgroupOf H) ∧
      (X.pCoreIn 2 ⊔ P₀ = X ∧ Disjoint (X.pCoreIn 2) P₀) ∧
      (normalClosure (P : Set X)).map X.subtype = X ∧
      closure {g : G | ∃ n ∈ X.pCoreIn 2, ∃ a ∈ P₀, n * a * n⁻¹ = g} = X ∧
      X.pCoreIn 2 = ⁅X.pCoreIn 2,P₀⁆ ∧
      U = X.pCoreIn 2 ⊔ N ∧
      (∀ D : Subgroup (P₀ ⧸ frattini P₀),
        (∀ n : N, ∀ x ∈ D, Chapter1.frattiniConjugationAction N P₀ inf_le_right n x ∈ D) →
          D = ⊥ ∨ D = ⊤) ∧
      P₀ = ⁅P₀,(frattini N).map N.subtype⁆ ∧
      (pResidual 2 (H.pCoreIn 2 ⊔ X : Subgroup G)).map (H.pCoreIn 2 ⊔ X).subtype = X := by
  have hUH : U ≤ H := hP₂ ▸ map_subtype_le _
  have hq : Chapter1.XiOddQuotient 3 (Chapter1.XiQuotient X) := by
    have hs := order_nine_quotient_structure e
    exact Or.inl ⟨hs.1,hs.2.1⟩
  have hUX : Chapter1.IsSylowIn 2 U (X ⊔ U) :=
    ⟨restrictSylow P₂ (sup_le hXH hUH) (hP₂ ▸ le_sup_right), by
      rw [restrictSylow_image,hP₂]⟩
  have hgen := Chapter1.lemma_1_3_2_2 hXi (by decide : Odd 3) hq P
  have hirr := Chapter1.lemma_1_3_2_3 hXi hUX (by decide : Odd 3) hq P
  exact ⟨Chapter3.sqtk_of_mem_H hG hH,
    (Chapter1.mem_XiIn_iff_subgroupOf hUH hXH).mp ⟨hXH,hXi⟩,
    ⟨hXi.sylow_sup hq P, hXi.sylow_disjoint (by decide : Odd 3) P⟩,
    hgen.1,hgen.2.1,hgen.2.2,hirr.1,hirr.2,
    Chapter1.lemma_1_3_2_4 hXi hUX (by decide : Odd 3) hq P,
    Chapter1.lemma_1_3_2_5_local hXi ⟨P₂,hP₂⟩⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup

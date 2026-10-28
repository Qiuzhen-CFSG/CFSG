module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.CubicFactor.Torus
public import Theory.GroupTheory.CubicPairCharacters

/-!
# Both cubic characters of the literal Cartan quotient

The first character is the action on the original tensor line. Its kernel
inside the normal quotient torus is the original Hall cubic. An invariant
complementary cubic and the three-coset construction give the second
character, and the pair is faithful on the two-core quotient. Composing
with the actual quotient map gives kernel exactly O₂(A∨T), Cartan image
A₃×A₃ and Hall image 1×A₃, retaining the first character's exact kernel.

The exchange-sign assertion is established in MarkedQuotient using the
independent factor-exchange obstruction. Final source assembly remains
with qt-d-tensor-mixed-zero-core.
Source: Aschbacher–Smith, original 9.3.1, printed p.732.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Construct both cubic characters, retaining the original line, Cartan and Hall maps. -/
theorem exists_cartan_pair_characters
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hAe : IsElementaryAbelian 3 A) (hBA : B ≤ A) (hB3 : Nat.card B = 3)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)) :
    ∃ q : (A ⊔ (T : Subgroup G) : Subgroup G) →*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),
      q.ker = pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G) ∧
      (A.subgroupOf (A ⊔ (T : Subgroup G))).map q =
        (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) ∧
      (B.subgroupOf (A ⊔ (T : Subgroup G))).map q =
        (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)) ∧
      ∀ x : (A ⊔ (T : Subgroup G) : Subgroup G),
        (q x).1 = 1 ↔ (x : G) ∈ centralizer (m.tensorLine : Set G) := by
  let E := cartanQuotientTorus (T := T) A
  let B' := cartanQuotientHall (T := T) A B
  let S := ((T : Subgroup G).subgroupOf (A ⊔ (T : Subgroup G))).map (cartanTwoCoreMap A)
  let := m.cartanQuotientTorus_normal A hAB hA9
  let := m.cartanQuotientHall_normal hH A B hAB hA9 hBA hB3 hBC hmove
  obtain ⟨C,hCN,hC3,hd,hgen⟩ := m.exists_normal_complementary_cartan_cubic
    hH A B hAB hA9 hAe hBA hB3 hBC hmove
  let := hCN
  obtain ⟨f,_,hf,hline⟩ := m.exists_tensorLine_quotient_character hH A B hAB hA9 hBA hB3 hBC hmove
  have hEf : E ⊓ f.ker = B' :=
    (m.cartanQuotientHall_eq_inf_line_kernel A B hAB hBA hBC f hf).symm
  obtain ⟨g,hfg,hEfg,hBfg,_⟩ := CubicPairCharacters.exists_second_character E B' C
    (card_cartanQuotientTorus A hA9) (card_cartanQuotientHall A B hBA hB3) hC3 hd hgen
    S (T.isPGroup'.comap_subtype.map (cartanTwoCoreMap A))
    (cartanQuotientTorus_sup_sylow A) (pCore_quotient_pCore_eq_bot 2) f hEf
  let q := (f.prod g).comp (cartanTwoCoreMap A)
  refine ⟨q,?_,?_,?_,?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ hfg]
    exact QuotientGroup.ker_mk' _
  · change (A.subgroupOf (A ⊔ (T : Subgroup G))).map
      ((f.prod g).comp (cartanTwoCoreMap A)) = _
    rw [←Subgroup.map_map]
    exact hEfg
  · change (B.subgroupOf (A ⊔ (T : Subgroup G))).map
      ((f.prod g).comp (cartanTwoCoreMap A)) = _
    rw [←Subgroup.map_map]
    exact hBfg
  · exact hline

end CFSG.Quasithin.Chapter10.SourceA5TensorModel

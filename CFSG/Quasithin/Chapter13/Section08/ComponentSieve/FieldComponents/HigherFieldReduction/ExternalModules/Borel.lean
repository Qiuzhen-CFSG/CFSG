module

public import Theory.Representation.HigherFieldBorelFixedSpaces
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalIndex

/-!
# Marked source Borels in the external-X module argument

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.20, printed pp.954–955 (PDF pp.971–972).

The lift is taken inside K through the literal quotient H/O₂(H). A marking
of B₀* under the component isomorphism determines the marking of B* = O²(B₀)*;
this follows by transporting residuals through subgroup images. In odd degree,
the concrete L₂ and L₃ torus orders then make the lifted residual centralize V
from the local O³(B) ≤ B_C ≤ C_G(V) identities. This also centralizes the seed.

For the even-degree index argument, normalization of L by BL₁ implies that
O₂(B) normalizes the actual quotient-centralizing residual B_C. The containment
B_C ≤ K remains explicit: it requires the covered local geometry and does not
follow merely from the displayed index three. The source assembly must supply
that containment and the original Borel marking; no external-X exclusion or
module classification is asserted here.
-/

@[expose] public section
open Subgroup Representation Representation.HigherFieldBorelFixedSpaces
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
variable {G : Type*} [Group G] [Finite G]

private theorem residualIn_map {D : Type*} [Group D]
    (p : ℕ) (B : Subgroup G) (f : G →* D) :
    (residualIn p B).map f = residualIn p (B.map f) := by
  have h := congrArg (fun S => S.map (B.map f).subtype)
    (map_pResidual_of_surjective p (f.subgroupMap B) (f.subgroupMap_surjective B))
  have hf : (B.map f).subtype.comp (f.subgroupMap B) = f.comp B.subtype := by
    ext x
    rfl
  simpa only [residualIn, map_map, hf] using h

private theorem residualIn_subgroupOf (p : ℕ) (B K : Subgroup G) (hBK : B ≤ K) :
    residualIn p (B.subgroupOf K) = (residualIn p B).subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [residualIn_map, map_subgroupOf_eq_of_le hBK,
    map_subgroupOf_eq_of_le ((map_subtype_le _).trans hBK)]

/-- The original Borel marking determines the residual marking on the literal source lift. -/
theorem lifted_borel_residual_marking
    {D : Type*} [Group D] (H K : Subgroup G) (hKH : K ≤ H)
    (B₀ : Subgroup (Source.Hstar H)) (hB₀ : B₀ ≤ Source.starImage H K)
    (e : Source.starImage H K ≃* D) (Bmodel : Subgroup D)
    (hmark : (B₀.subgroupOf (Source.starImage H K)).map e.toMonoidHom = Bmodel) :
    ((Source.starImage H (borelResidual (borelLift H K hKH B₀))).subgroupOf
      (Source.starImage H K)).map e.toMonoidHom = twoResidualImage Bmodel := by
  rw [starImage_borelResidual H K hKH B₀ hB₀,
    ← residualIn_subgroupOf 2 B₀ _ hB₀, residualIn_map, hmark]

/-- Restrict the marked component isomorphism to its Borel. -/
noncomputable def markedBorelEquiv
    {D : Type*} [Group D] (H K : Subgroup G)
    (B₀ : Subgroup (Source.Hstar H)) (hB₀ : B₀ ≤ Source.starImage H K)
    (e : Source.starImage H K ≃* D) (Bmodel : Subgroup D)
    (hmark : (B₀.subgroupOf (Source.starImage H K)).map e.toMonoidHom = Bmodel) :
    B₀ ≃* Bmodel :=
  (subgroupOfEquivOfLe hB₀).symm.trans
    (((B₀.subgroupOf (Source.starImage H K)).equivMapOfInjective e.toMonoidHom
      e.injective).trans (MulEquiv.subgroupCongr hmark))

/-- In odd degree the actual lifted L₂ Borel residual centralizes V. -/
theorem sl2_odd_borel_centralizes
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hodd : Odd n)
    (H K V C : Subgroup G) (hKH : K ≤ H)
    (B₀ : Subgroup (Source.Hstar H)) (hB₀ : B₀ ≤ Source.starImage H K)
    (e : Source.starImage H K ≃* SL(2,F))
    (hmark : (B₀.subgroupOf (Source.starImage H K)).map e.toMonoidHom =
      Matrix.SpecialLinearGroup.rankOneBorel F)
    (hR : residualIn 3 (borelResidual (borelLift H K hKH B₀)) ≤ C)
    (hC : C ≤ centralizer (V : Set G)) :
    borelResidual (borelLift H K hKH B₀) ≤ centralizer (V : Set G) := by
  let eB := (markedBorelEquiv H K B₀ hB₀ e _ hmark).trans
    (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.rankOneBorelEquiv F)
  exact borel_centralizes_of_threePrime _ C V
    (TorusModels.linearTwo_star_odd_threePrime hF hodd H K hKH B₀ hB₀ eB) hR hC

/-- The odd-degree projective L₃ calculation uses the same marked source lift. -/
theorem psl3_odd_borel_centralizes
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hodd : Odd n)
    (H K V C : Subgroup G) (hKH : K ≤ H)
    (B₀ : Subgroup (Source.Hstar H)) (hB₀ : B₀ ≤ Source.starImage H K)
    (e : Source.starImage H K ≃* PSL(3,F))
    (hmark : (B₀.subgroupOf (Source.starImage H K)).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F)
    (hR : residualIn 3 (borelResidual (borelLift H K hKH B₀)) ≤ C)
    (hC : C ≤ centralizer (V : Set G)) :
    borelResidual (borelLift H K hKH B₀) ≤ centralizer (V : Set G) :=
  borel_centralizes_of_threePrime _ C V
    (TorusModels.linearThree_star_odd_threePrime hF hodd H K hKH B₀ hB₀
      (markedBorelEquiv H K B₀ hB₀ e _ hmark)) hR hC

omit [Finite G] in
/-- The local normalizer of L also normalizes the quotient centralizer's
residual. This discharges the normalization needed by the index-three lemma. -/
theorem twoCore_normalizes_centralizingResidual (B L₁ L : Subgroup G)
    (hL : B ⊔ L₁ ≤ normalizer (L : Set G)) :
    B.pCoreIn 2 ≤ normalizer (centralizingResidual B L₁ L : Set G) := by
  have hQ : B ⊔ L₁ ≤ normalizer (L.pCoreIn 2 : Set G) :=
    hL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hB : B.pCoreIn 2 ≤ B ⊔ L₁ := (pCoreIn_le 2 B).trans le_sup_left
  have hC : B.pCoreIn 2 ≤ normalizer (borelCentralizer B L₁ L : Set G) :=
    commutatorPreimage_normalized _ _ _ _ hQ
      (hB.trans (B ⊔ L₁).le_normalizer) (hB.trans hL) (hB.trans hQ)
  exact hC.trans (normalizer_le_normalizer_characteristic_image
    (borelCentralizer B L₁ L) (pResidual 2 (borelCentralizer B L₁ L)))

/-- Once the covered local calculation places B_C in K, the source index
forces the whole lifted Borel residual into C_G(V). Its two-core placement
and normalization are derived here. -/
theorem borel_centralizes_of_local_index
    (H K L₁ L X V : Subgroup G) (hKH : K ≤ H)
    (B₀ : Subgroup (Source.Hstar H)) (hXK : ¬ X ≤ K)
    (hCK : centralizingResidual (borelResidual (borelLift H K hKH B₀)) L₁ L ≤ K)
    (hCJ : centralizingResidual (borelResidual (borelLift H K hKH B₀)) L₁ L ≤
      borelResidual (borelLift H K hKH B₀) ⊔ X)
    (hL : borelResidual (borelLift H K hKH B₀) ⊔ L₁ ≤ normalizer (L : Set G))
    (hindex : (centralizingResidual (borelResidual (borelLift H K hKH B₀)) L₁ L ⊔
      (borelResidual (borelLift H K hKH B₀)).pCoreIn 2).relIndex
        (borelResidual (borelLift H K hKH B₀) ⊔ X) = 3)
    (hC : centralizingResidual (borelResidual (borelLift H K hKH B₀)) L₁ L ≤
      centralizer (V : Set G)) :
    borelResidual (borelLift H K hKH B₀) ≤ centralizer (V : Set G) := by
  have hBK : borelResidual (borelLift H K hKH B₀) ≤ K :=
    (map_subtype_le _).trans (borelLift_le H K hKH B₀)
  exact (borel_le_centralizingResidual_of_external_index _ L₁ L K X hBK hXK
    (sup_le hCK ((pCoreIn_le 2 _).trans hBK)) hCJ
    (twoCore_normalizes_centralizingResidual _ L₁ L hL) hindex).trans hC

omit [Finite G] in
/-- Centralizing the original V gives the required commutator bound on its seed. -/
theorem seed_commutator_of_borel_centralizes (B V V₃ V₁ : Subgroup G)
    (hV₃ : V₃ ≤ V) (hB : B ≤ centralizer (V : Set G)) : ⁅V₃, B⁆ ≤ V₁ := by
  rw [commutator_comm]
  exact (commutator_mono le_rfl hV₃).trans
    ((commutator_eq_bot_iff_le_centralizer.mpr hB).le.trans bot_le)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
end

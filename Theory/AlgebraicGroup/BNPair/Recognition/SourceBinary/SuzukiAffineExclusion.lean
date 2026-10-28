module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineUnitaryExclusion
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartanAction

/-!
# Excluding affine hexagons opposite a nonbinary Suzuki factor

The actual Suzuki actor and the root order identify the canonical root
with a model Sylow, including parameter zero for that identification.
At positive parameters the actor's Cartan has order q-1 greater than one.
A nonidentity root element has its full centralizer inside that Sylow.
Since the source Cartan meets U trivially, the full Cartan has no fixed
nonidentity root elements. Normalization by N transports this to every
root of the same type.

The global Cartan-fixed kernel theorem now excludes the opposite affine
nine-point action of order 144: its kernel would have order at least 256
and at most 64. The exact source maps are retained, and neither endpoint
is assumed perfect. BinaryAffinePerfectExclusion applies this to the
original Suzuki quotient, then exhausts the original perfect-factor
catalogue to prove both endpoint regularity statements on the hexagon.

Source: the centralizer and torus geometry of Suzuki groups in Huppert--
Blackburn XI.3.6; the solvable-module argument in Fong--Seitz I (4D), (5I),
pp.21--23,31--35; DGS Theorem D, p.224. This does not prove the other even
Weyl branches, minimal-configuration reduction or marked rank-two recognition.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The root order and actual Suzuki actor identify the root with its model Sylow. -/
def suzukiRootEquivOfCard (i : Fin 2) {m : ℕ}
    (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (hc : Nat.card (simpleRoot Q split i) = (2^(2*m+1))^2) :
    simpleRoot Q split i ≃* SuzukiRootSubgroup m := by
  let R := rankOne Q split i
  let A := (simpleRoot Q split i).subgroupOf R
  have hA : IsPGroup 2 A := (split.isTwo.to_le (simpleRoot_le Q split i)).comap_subtype
  let S := Classical.choose hA.exists_le_sylow
  have hS := Classical.choose_spec hA.exists_le_sylow
  let S' := S.mapSurjective (f := μ.toMonoidHom) μ.surjective
  let a : S ≃* S' := (S : Subgroup R).equivMapOfInjective μ.toMonoidHom μ.injective
  let b : S' ≃* SuzukiRootSubgroup m :=
    (S'.equiv (ReeSource.matrixRootSylow m)).trans
      (MulEquiv.subgroupCongr (ReeSource.matrixRootSylow_carrier m))
  have hcA : Nat.card A = (2^(2*m+1))^2 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (show simpleRoot Q split i ≤ R from le_sup_left)).toEquiv).trans hc
  have hcS : Nat.card S = (2^(2*m+1))^2 :=
    (Nat.card_congr (a.trans b).toEquiv).trans (ReeSource.matrixRoot_card m)
  have he : A = (S : Subgroup R) := eq_of_le_of_card_ge hS (by rw [hcA,hcS])
  exact (subgroupOfEquivOfLe (show simpleRoot Q split i ≤ R from le_sup_left)).symm.trans
    ((MulEquiv.subgroupCongr he).trans (a.trans b))

/-- The full Cartan has no nonidentity fixed points on any nonbinary Suzuki root. -/
theorem suzuki_cartan_all_roots_fixedFree (i : Fin 2) {m : ℕ} (hm : 0 < m)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (hc : Nat.card (simpleRoot Q split i) = (2^(2*m+1))^2)
    (w : Weyl Q) :
    rootAt Q split i w ⊓ centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) = ⊥ := by
  let ν := suzukiRootEquivOfCard Q split i μ hc
  obtain ⟨S,hS⟩ := simpleRoot_sylow_of_suzuki Q split i μ ν
  have hcart := suzuki_rankOne_cartan_cyclic_card Q split i hKi hm μ ν
    (UnitarySource.actorReflection Q split i)
  let H := (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split i)
  have hHcard : 1 < Nat.card H := by
    change 1 < Nat.card ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split i))
    rw [hcart.2]
    have hb := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*m+1)
    norm_num at hb
    omega
  let : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp hHcard
  obtain ⟨t,ht⟩ := exists_ne (1 : H)
  have hf : simpleRoot Q split i ⊓
      centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    apply mem_bot.mpr
    by_contra hune
    let a : rankOne Q split i := ⟨u,(show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) hu.1⟩
    have haS : a ∈ (S : Subgroup (rankOne Q split i)) := by rw [hS]; exact hu.1
    have htC : t.val ∈ centralizer ({a} : Set (rankOne Q split i)) := by
      apply mem_centralizer_singleton_iff.mpr
      exact Subtype.ext (mem_centralizer_iff.mp hu.2 _ t.property)
    have htS := BenderSuzuki.ZD.RankOneModelGeometry.suzuki_centralizer_le_sylow
      hm μ S haS (fun he => hune (congrArg Subtype.val he)) htC
    rw [hS] at htS
    have htzero : ((t.val : rankOne Q split i) : X ⧸ Q.D) = 1 := by
      apply mem_bot.mp
      rw [←split.unipotent_inf_N]
      exact ⟨simpleRoot_le Q split i htS,t.property.2⟩
    exact ht (Subtype.ext (Subtype.ext htzero))
  let a := representative w
  have hh := congrArg (fun C => rightConjugate C (a : X ⧸ Q.D)) hf
  rw [rightConjugate_inf,rightConjugate_eq_self _
    (normalizer_le_normalizer_centralizer _ (torus_normalizes a))] at hh
  have hb : rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (a : X ⧸ Q.D) = ⊥ := by
    ext x
    exact (MulAut.conj (a : X ⧸ Q.D)).map_eq_one_iff
  rwa [hb] at hh

/-- A nonbinary Suzuki endpoint excludes the opposite affine hexagon. -/
theorem no_affine_hexagon_of_suzuki
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    {m : ℕ} (hm : 0 < m) (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (hc : Nat.card (simpleRoot Q split i) = (2^(2*m+1))^2)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) : False :=
  no_affine_hexagon_of_cartan_fixedFree Q split hhex i j hij
    (suzuki_cartan_all_roots_fixedFree Q split i hm hKi μ hc) hs hp hg
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

module

public import Stellmacher.SectionTwo.LemmaTwoOne


open scoped BigOperators Pointwise

namespace Stellmacher.SectionTwo

universe u

public structure LemmaTwoTwoConclusion
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (barJ barB : Subgroup barG) : Prop where
  part_a :
    (⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ).Normal
  part_b : barJ = barB
  part_c :
    ∃ (n : ℕ) (E : Fin n → Subgroup barG),
      (⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ) = ⨆ i : Fin n, E i ∧
      IsInternalDirectProductFamily
        (⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ) E ∧
      ∀ i : Fin n, IsSL2Two (↥(E i))
  part_d :
    ∃ (n : ℕ) (E : Fin n → Subgroup barG) (Vf : Fin n → Subgroup G),
      (⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ) = ⨆ i : Fin n, E i ∧
      (∀ i : Fin n, Vf i =
        ambientCommutator ((E i).comap q) (vSubgroup S) ∧ Nat.card (Vf i) = 4) ∧
      IsInternalDirectProductFamily (vSubgroup S)
        (fun i : Option (Fin n) =>
          match i with
          | none => vSubgroup S ⊓
              Subgroup.centralizer
                (((⁅pPrimeCore 2 barG, barJ⁆ ⊔ barJ).comap q : Subgroup G) : Set G)
          | some i => Vf i)

/-! **Stellmacher (2.2).**  Here `q : G → barG` is the quotient map with
kernel `C_G(V)`.  The bars in the paper denote images of the unbarred
subgroups `J(S)` and `B`, and `bar E` uses the odd core `O_{2'}(bar G)`.
-/
public theorem lemma_two_two
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q)
    (hker : q.ker = cSubgroup S)
    (barS barJ barB : Subgroup barG)
    (hbarS : barS = (S : Subgroup G).map q)
    (B : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓
      Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (hbarJ : barJ =
      (elementaryAbelianMaxJ (S : Subgroup G)).map q)
    (hbarB : barB = B.map q)
    (hJne : barJ ≠ ⊥) :
    LemmaTwoTwoConclusion (G := G) S q barJ barB := by
  sorry

end Stellmacher.SectionTwo

module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CoreShapeSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.QuaternionAutomizerSource
public import GorensteinWalter.PGL2DihedralSylow

/-!
# Core models from the original automizer quotient

The literal quotient model supplies its epimorphism and exact SC kernel.
An outside Sylow normalizer element is selected internally. The actual
M₁₀ Sylow is semidihedral sixteen, while odd PGL₂ Sylows are dihedral.
Applying the faithful core embedding gives the initial 2.5.21 alternatives.
The independent quaternion terminal removes its Q₈ branch in M₁₀.

All local actions, crossing elements and kernel identifications are proved
from the original source setup. Normality of K remains the genuine 2.5.20
input; the marked quotient models are supplied by the 2.5.16 source family.
Source: Aschbacher--Smith 2.5.21, printed pp.565 and 567.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- PGL₂ quotient models give the cyclic-or-dihedral source alternatives. -/
theorem MathieuSourceSetup.pgl_twoCore_models
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    {F : Type*} [Field F] [Finite F]
    (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 F) :
    IsCyclic (twoCore H) ∨ ∃ k : ℕ, Nonempty (twoCore H ≃* DihedralGroup (2 ^ k)) := by
  obtain ⟨f, hf, hk⟩ := MathieuSourceSetup.exists_surjective_core_model c hgen eQ
  obtain ⟨x, hxT, hxS, hxN, hx2⟩ := exists_outside_normalizer_square_mem
    ((S : Subgroup H).map H.subtype) (c.T : Subgroup G) c.T.isPGroup' c.sylow_lt
  obtain ⟨n, _, ⟨eP⟩⟩ := GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model F hodd
    (S.mapSurjective hf)
  exact MathieuSourceSetup.twoCore_cyclic_or_dihedral c hgen f hk x hxT hxS hxN hx2 eP

/-- M₁₀ quotient models give the precise remaining core alternatives, with
its quaternion branch discharged by the actual crossing-core contradiction. -/
theorem MathieuSourceSetup.m10_twoCore_models
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (eQ : (H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension) :
    IsCyclic (twoCore H) ∨ IsKleinFour (twoCore H) ∨
      Nonempty (twoCore H ≃* DihedralGroup 4) ∨
      Nonempty (twoCore H ≃* Semidihedral.StandardModel 4 (by decide)) := by
  obtain ⟨f, hf, hk⟩ := MathieuSourceSetup.exists_surjective_core_model c hgen eQ
  obtain ⟨x, hxT, hxS, hxN, hx2⟩ := exists_outside_normalizer_square_mem
    ((S : Subgroup H).map H.subtype) (c.T : Subgroup G) c.T.isPGroup' c.sylow_lt
  have hs := AlternatingSix.M10.sylowTwoEquivSemidihedral (S.mapSurjective hf)
  have hm := MathieuSourceSetup.twoCore_models_of_semidihedral_sixteen
    c hgen f hk x hxT hxS hxN hx2 hs
  rcases hm with hc | hm
  · exact Or.inl hc
  rcases hm with hfour | hm
  · exact Or.inr (Or.inl hfour)
  rcases hm with hd | hm
  · exact Or.inr (Or.inr (Or.inl hd))
  rcases hm with hq | hsd
  · obtain ⟨eq⟩ := hq
    exact (MathieuSourceSetup.quaternion_m10_core_quotient_impossible c hgen eK eQ eq).elim
  · exact Or.inr (Or.inr (Or.inr hsd))

/-- The binary linear source automizer supplies its own quotient model. -/
theorem MathieuSourceSetup.linear_binary_twoCore_models
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (eK : K ≃* Matrix.PSL3Two.PSL) :
    IsCyclic (twoCore H) ∨ ∃ k : ℕ, Nonempty (twoCore H ≃* DihedralGroup (2 ^ k)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨eQ⟩ := MathieuSourceSetup.normal_linear_binary_core_quotient c hG hempty hgen eK
  have hseven : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod 7)) := by
    exact ⟨7, 1, by decide, by decide, by decide, by norm_num⟩
  exact MathieuSourceSetup.pgl_twoCore_models (F := ZMod 7) c hgen hseven
    (eQ.trans Matrix.PSL3Two.Automorphisms.pgl2SevenEquivAut.symm)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection

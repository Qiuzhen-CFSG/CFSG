module
public import Theory.Representation.PSL3Four.SmallDegree
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCoreComplete
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameLinearAdjoint

/-!
# Elementary sections and cubic parity in the original component core

The original Sylow intersection has two-rank twelve in degree two. Every
quotient of an elementary subgroup of that Sylow therefore has at most 4096
elements. An adjoint carrier over F₄ has 65536 elements, excluding both its
ordinary and determinant-twisted extensions on such sections. The application
to Ω₁(Z(O₂(K_Z))) retains both original component inclusions.

The actual centralizer C_K₂(X) acts as the full natural SL₂(4) on C_R₂(X).
Its invariant subgroups are therefore trivial or the whole group of order
sixteen. Cubic orbit counting gives |A| ≡ 1 mod 3 for each subgroup A of R₂
normalized by X and C_K₂(X). Applying this to both endpoints of an invariant
section gives |A:B| ≡ 1 mod 3, excluding every odd binary degree. The original
source cubic supplies all these action premises. For an elementary numerator,
the checked PSL₃(4) degree-one-or-nine classification below dimension thirteen
then rules out irreducibility on the literal section A/B.

These statements control actual core sections; they do not identify a whole
extension action from its SL₃ restriction. In particular a section of a
nonabelian numerator need not satisfy the elementary order bound. Control of
those remaining chief factors, strict secondary-core enlargement, and the
general MS witness remain with qt-d-1222-rankone-uniqueness-nonblock. The
original A₅ nonblock and Baumann obligations are already closed.

Source: Aschbacher--Smith C.1.35(4), pp.137--138, and the conclusion of
original 4.3.2, pp.618--619. The small-degree classification is the proved
PSL₃(4) tensor-word classification used in Representation.PSL3Four.SmallDegree.
-/

public section
open Subgroup Theory.GroupTheory
open Representation.SL3.AdjointCubicCentralizer
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- The original Sylow rank bounds every quotient carrier of an elementary subgroup. -/
theorem MSData.elementary_section_card_le (d : MSData c n) (hn : 1 < n)
    (A : Subgroup G) (hA : A ≤ S c) [IsElementaryAbelian 2 A]
    {M : Type*} (f : A → M) (hf : Function.Surjective f) : Nat.card M ≤ 2^(6*n) := by
  have he : IsElementaryAbelian 2 (A.subgroupOf (S c)) :=
    IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hA).toMonoidHom
      (subgroupOfEquivOfLe hA).injective
  have hh := (primeRank_le_iff_elementary_card_le (S c)).mp (d.sylow_primeRank hn).le
    (A.subgroupOf (S c)) he
  rw [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv] at hh
  exact (Nat.card_le_card_of_surjective f hf).trans hh

/-- The adjoint carrier is too large for an elementary section, independently of its extension action. -/
theorem MSData.elementary_section_not_adjoint (d : MSData c 2)
    (A : Subgroup G) (hA : A ≤ S c) [IsElementaryAbelian 2 A]
    {M F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (f : A → M) (hf : Function.Surjective f) : ¬ Nonempty (M ≃ TraceZero F) := by
  rintro ⟨e⟩
  have hh := d.elementary_section_card_le (by decide) A hA f hf
  have hc : Nat.card (TraceZero F) = 4^8 := by
    rw [Module.natCard_eq_pow_finrank (K := F),←(matrixAdjointEquiv F).finrank_eq,
      Representation.SL3.BinaryDefiningFactors.finrank_adjointSpace,hF]
  rw [Nat.card_congr e,hc] at hh
  norm_num at hh

/-- Apply the size obstruction inside the original component core through both subtype maps. -/
theorem MSData.component_elementary_section_not_adjoint (d : MSData c 2)
    (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    (A : Subgroup G)
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    [IsElementaryAbelian 2 A] {M F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) (f : A → M) (hf : Function.Surjective f) :
    ¬ Nonempty (M ≃ TraceZero F) := by
  have hc : ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype ≤ R₂ c := by
    change (s.component.pCoreIn 2).map (rootNormalizer c).subtype ≤ R₂ c
    rw [map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    exact s.component_core_le D
  exact d.elementary_section_not_adjoint A (hA.trans (hc.trans (radical_le_sylow c))) hF f hf


/-- In particular no quotient of the actual central omega subgroup has an adjoint carrier. -/
theorem MSData.component_centralOmega_section_not_adjoint (d : MSData c 2)
    (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    {M F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (f : omegaCenterIn ((pCore 2 s.component).map s.component.subtype |>.map
      (rootNormalizer c).subtype) → M) (hf : Function.Surjective f) :
    ¬ Nonempty (M ≃ TraceZero F) :=
  d.component_elementary_section_not_adjoint s D _ (map_subtype_le _) hF f hf

namespace RootCoordinates
variable {d : MSData c 2} (m : RootCoordinates d)
  (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
  (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ (K c).coreCenterIn 2)
  (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)
  (hcomm : ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2)
include m s D hX hXK hfix hcomm

/-- The original secondary centralizer acts irreducibly on the cubic-fixed radical, even on additive subgroups. -/
theorem fixedRadical_invariant_subgroup (A : Subgroup G)
    (hA : A ≤ R₂ c ⊓ centralizer (X : Set G))
    (hN : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (A : Set G)) :
    A = ⊥ ∨ A = R₂ c ⊓ centralizer (X : Set G) := by
  let R := R₂ c ⊓ centralizer (X : Set G)
  let e := m.fixedRadicalCoordinates D s X hX hXK hfix
  let B := A.subgroupOf R
  let E := B.map e.toMonoidHom
  have hinv : ∀ g v, v ∈ E → Matrix.SL2.naturalAction d.field.Carrier g v ∈ E := by
    intro g v hv
    obtain ⟨k,rfl⟩ := m.fixedSecondaryLinear_surjective X hX hcomm g
    obtain ⟨a,ha,rfl⟩ := hv
    refine ⟨fixedRadicalAction X k a,?_,?_⟩
    · change (k : G) * (a : G) * (k : G)⁻¹ ∈ A
      exact (mem_normalizer_iff.mp (hN k.property) (a : G)).mp ha
    · exact m.fixedRadical_action_natural D s X hX hXK hfix k a
  rcases Matrix.SL2.naturalAction_irreducible d.field.Carrier E hinv with hb | ht
  · left
    have hb' : B = ⊥ := (map_eq_bot_iff_of_injective B e.injective).mp hb
    apply bot_unique
    intro x hx
    have hh : (⟨x,hA hx⟩ : R) ∈ B := hx
    have he : (⟨x,hA hx⟩ : R) = 1 :=
      mem_bot.mp (show (⟨x,hA hx⟩ : R) ∈ (⊥ : Subgroup R) from hb' ▸ hh)
    exact mem_bot.mpr (congrArg (fun z : R => (z : G)) he)
  · right
    have ht' : B = ⊤ := by
      apply map_injective e.injective
      change E = (⊤ : Subgroup R).map e.toMonoidHom
      have he : (⊤ : Subgroup R).map e.toMonoidHom = ⊤ :=
        (MonoidHom.range_eq_map _).symm.trans (MonoidHom.range_eq_top.mpr e.surjective)
      exact ht.trans he.symm
    apply le_antisymm hA
    intro x hx
    exact ht'.ge (mem_top (⟨x,hx⟩ : R))

/-- Every invariant subgroup meets the cubic-fixed radical trivially or in the whole fixed radical. -/
theorem invariant_cubic_fixed_subgroup (A : Subgroup G) (hA : A ≤ R₂ c)
    (hN : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (A : Set G)) :
    A ⊓ centralizer (X : Set G) = ⊥ ∨
      A ⊓ centralizer (X : Set G) = R₂ c ⊓ centralizer (X : Set G) := by
  apply m.fixedRadical_invariant_subgroup s D X hX hXK hfix hcomm _ (inf_le_inf_right _ hA)
  exact (le_inf hN (inf_le_right.trans (centralizer (X : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

/-- The only fixed subgroup orders are one and sixteen. -/
theorem invariant_cubic_fixed_card (A : Subgroup G) (hA : A ≤ R₂ c)
    (hN : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (A : Set G)) :
    Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 1 ∨
      Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 16 := by
  rcases m.invariant_cubic_fixed_subgroup s D X hX hXK hfix hcomm A hA hN with hb | ht
  · exact Or.inl (hb ▸ Subgroup.card_bot)
  · exact Or.inr (ht ▸ m.radical_cubic_fixed_card D s X hX hXK hfix)

/-- Cubic orbits force the original invariant subgroup order to be one modulo three. -/
theorem invariant_cubic_card_mod_three (A : Subgroup G) (hA : A ≤ R₂ c)
    (hN : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (A : Set G))
    (hXA : X ≤ normalizer (A : Set G)) : Nat.card A % 3 = 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hX)
  have hc := Subgroup.card_modEq_card_inf_centralizer X A hp hXA
  change Nat.card A % 3 = Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) % 3 at hc
  rcases m.invariant_cubic_fixed_card s D X hX hXK hfix hcomm A hA hN with h1 | h16
  · simpa only [h1] using hc
  · simpa only [h16] using hc

/-- The same congruence holds for a section with both original endpoints invariant. -/
theorem invariant_cubic_section_index_mod_three (A B : Subgroup G)
    (hA : A ≤ R₂ c) (hBA : B ≤ A)
    (hNA : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (A : Set G))
    (hNB : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (B : Set G))
    (hXA : X ≤ normalizer (A : Set G)) (hXB : X ≤ normalizer (B : Set G)) :
    B.relIndex A % 3 = 1 := by
  have ha := m.invariant_cubic_card_mod_three s D X hX hXK hfix hcomm A hA hNA hXA
  have hb := m.invariant_cubic_card_mod_three s D X hX hXK hfix hcomm B (hBA.trans hA) hNB hXB
  have hc := (B.subgroupOf A).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv] at hc
  have hh := congrArg (fun j => j % 3) hc
  change (Nat.card B * B.relIndex A) % 3 = Nat.card A % 3 at hh
  simpa only [Nat.mul_mod,hb,ha,one_mul,Nat.mod_mod] using hh

/-- An original invariant section cannot have odd binary degree. -/
theorem invariant_cubic_section_not_odd_degree (A B : Subgroup G)
    (hA : A ≤ R₂ c) (hBA : B ≤ A)
    (hNA : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (A : Set G))
    (hNB : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (B : Set G))
    (hXA : X ≤ normalizer (A : Set G)) (hXB : X ≤ normalizer (B : Set G))
    {r : ℕ} (hr : Odd r) : B.relIndex A ≠ 2^r := by
  intro he
  have hh := m.invariant_cubic_section_index_mod_three s D X hX hXK hfix hcomm
    A B hA hBA hNA hNB hXA hXB
  obtain ⟨j,hj⟩ := hr
  have hj' : r = 2*j+1 := by omega
  rw [he,hj',pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod] at hh
  norm_num at hh

/-- Apply parity to sections of the component core normalized by the original cubic extension. -/
theorem component_section_not_odd_degree (A B : Subgroup G)
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    (hBA : B ≤ A)
    (hNA : s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (A : Set G))
    (hNB : s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (B : Set G))
    {r : ℕ} (hr : Odd r) : B.relIndex A ≠ 2^r := by
  have hc : ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype ≤ R₂ c := by
    change (s.component.pCoreIn 2).map (rootNormalizer c).subtype ≤ R₂ c
    rw [map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    exact s.component_core_le D
  have hK : secondary c ⊓ centralizer (X : Set G) ≤
      s.component.map (rootNormalizer c).subtype ⊔ X :=
    (inf_le_left.trans s.secondary_le).trans le_sup_left
  exact m.invariant_cubic_section_not_odd_degree s D X hX hXK hfix hcomm A B
    (hA.trans hc) hBA (hK.trans hNA) (hK.trans hNB)
    (le_sup_right.trans hNA) (le_sup_right.trans hNB) hr
end RootCoordinates

/-- The source cubic itself supplies the parity constraint on every invariant section of the original component core. -/
theorem MSData.exists_source_cubic_even_sections (d : MSData c 2)
    (m : RootCoordinates d) (s : SecondarySourceData c 2)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ∃ X : Subgroup G, Nat.card X = 3 ∧ X ≤ (K c).coreCenterIn 2 ∧
      X ≤ rootNormalizer c ∧ Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
      ∀ A B : Subgroup G,
        A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype →
        B ≤ A →
        s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (A : Set G) →
        s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (B : Set G) →
        ∀ r : ℕ, Odd r → B.relIndex A ≠ 2^r := by
  obtain ⟨X,hX,hXK,hr,hfix,_,_,_,hcomm,_,_⟩ := d.exists_source_cubic_root D
  refine ⟨X,hX,hXK,hr,hfix,?_⟩
  intro A B hA hBA hNA hNB r hr
  exact m.component_section_not_odd_degree s D X hX hXK hfix hcomm A B hA hBA hNA hNB hr
namespace RootCoordinates
open scoped IsMulCommutative
variable {d : MSData c 2} (m : RootCoordinates d)
include m

/-- The literal elementary quotient cannot be irreducible for the marked full PSL₃(4) quotient: its degree is at most twelve and cannot be one or nine. -/
theorem component_elementary_quotient_not_irreducible
    (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ (K c).coreCenterIn 2)
    (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)
    (hcomm : ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2)
    (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    (hBA : B ≤ A)
    (hNA : s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (A : Set G))
    (hNB : s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (B : Set G))
    (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL)
    (ρ : Representation (ZMod 2) (s.component ⧸ pCore 2 s.component)
      (Additive (A ⧸ B.subgroupOf A))) : ¬ ρ.IsIrreducible := by
  intro hi
  let : ρ.IsIrreducible := hi
  have hc : ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype ≤ R₂ c := by
    change (s.component.pCoreIn 2).map (rootNormalizer c).subtype ≤ R₂ c
    rw [map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    exact s.component_core_le D
  have hbound : Nat.card (Additive (A ⧸ B.subgroupOf A)) ≤ 2^12 :=
    d.elementary_section_card_le (by decide) A
      (hA.trans (hc.trans (radical_le_sylow c)))
      (fun a => Additive.ofMul (QuotientGroup.mk' (B.subgroupOf A) a))
      (QuotientGroup.mk'_surjective (B.subgroupOf A))
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hbound
  have hdim := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound
  let τ : Representation (ZMod 2) Matrix.PSL3Four.PSL
      (Additive (A ⧸ B.subgroupOf A)) := ρ.comp e.symm.toMonoidHom
  let : τ.IsIrreducible :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr hi
  have hd := Representation.MathieuSmall.M22Recognition.PointRestriction.SimpleDegrees.simple_degree τ hdim
  have hodd : Odd (Module.finrank (ZMod 2) (Additive (A ⧸ B.subgroupOf A))) := by
    rcases hd with hd | hd <;> rw [hd] <;> decide
  apply m.component_section_not_odd_degree s D X hX hXK hfix hcomm A B hA hBA hNA hNB hodd
  change (B.subgroupOf A).index = _
  rw [Subgroup.index_eq_card]
  exact (Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (A ⧸ B.subgroupOf A))).trans (by rw [Nat.card_zmod])
end RootCoordinates

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

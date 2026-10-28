module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalCoordinates
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The original line from scalar movement and orbit spanning

A nonidentity scalar on the marked line has zero fixed space. Once the
original central kernel vanishes, coprime action gives V₁=[V₁,D₀] on the
literal flag preimage. Separately, the orbits of the points of V₁∩Z
lie in the image of V∩V_H. If these orbits span the original line,
injectivity of the original projection puts the whole original V₁ in V_H.

The scalar witness and orbit span remain model-theoretic obligations;
these lemmas do not assume either ambient conclusion. The earlier flag
owner supplies inner uniqueness. The Cartan assembly must construct the
model witnesses before this yields source 11.3.7(5).
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.3.7(3,5), printed p.773.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {F : BinaryField}

/-- Scalar movement and coprime decomposition on the literal flag preimage. -/
theorem source_line_commutator_of_scalar
    (c : Coordinates D F) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (A X : Subgroup G) (hX : IsCartan T L X) (hAX : A ≤ X)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (d : L) (hd : (d : G) ∈ A)
    (a : F.Carrier) (ha : a ≠ 1)
    (hscalar : ∀ w ∈ f.space 0, c.modelAction (c.quotientMap d) w = a • w) :
    f.Vi 0 = ⁅f.Vi 0, A⁆ := by
  let U := f.Vi 0
  have hn : A ≤ normalizer (U : Set G) := hAX.trans (f.cartan_normalizes hu hX 0)
  have hU : IsPGroup 2 U :=
    @IsElementaryAbelian.isPGroup 2 _ _ (D.centralQuotientPreimage_elementary _)
  have hf : U ⊓ centralizer (A : Set G) = ⊥ := by
    apply bot_unique
    rintro v ⟨hv,hvc⟩
    have hvV : v ∈ V := D.centralQuotientPreimage_le _ hv
    let v' : V := ⟨v,hvV⟩
    have he : V.normalizerMonoidHom (inclusion D.normalizes d) v' = v' := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hvc d hd)
    have hw := c.projection_component_conjugation d v'
    have hwmem : (c.projection v').toAdd ∈ f.space 0 :=
      (c.mem_preimage (f.space 0) v').mp hv
    rw [he, hscalar _ hwmem] at hw
    have hz : (c.projection v').toAdd = 0 := by
      have heq : (a - 1) • (c.projection v').toAdd = 0 := by
        rw [sub_smul,one_smul,← hw,sub_self]
      exact (smul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr ha)
    have hk : c.projection v' = 1 := hz
    exact hfixed.le ⟨hvV,(c.projection_eq_one_iff v').mp hk⟩
  have ho : Odd (Nat.card A) := hX.odd.of_dvd_nat (card_dvd_of_le hAX)
  obtain ⟨n,hncard⟩ := hU.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card U) := by
    rw [hncard]
    exact (Nat.coprime_two_right.mpr ho).pow_right n
  let : Group.IsNilpotent U := hU.isNilpotent
  have he := eq_commutator_sup_centralizer_of_solvable_coprime U A hn inferInstance hcop
  simpa only [hf, sup_bot_eq] using he

/-- Orbit spanning in the original natural coordinates puts the original flag
preimage in V_H. The central kernel is removed by the proved fixed-space step. -/
theorem source_line_le_closure_of_orbit_span
    {H : Subgroup G} (c : Coordinates D F) (f : InvariantFlag c)
    (A : Subgroup G) (hAH : A ≤ H)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hspan : (f.space 0).toAddSubgroup ≤ AddSubgroup.closure
      {w : c.Space | ∃ (z : V) (d : L), (z : G) ∈ f.Vi 0 ⊓ omegaCenter T ∧ (d : G) ∈ A ∧
        w = c.modelAction (c.quotientMap d) (c.projection z).toAdd}) :
    f.Vi 0 ≤ omegaClosure T H := by
  let W := ((omegaClosure T H).subgroupOf V).map c.projection
  have hi : Function.Injective c.projection := by
    apply c.projection.ker_eq_bot_iff.mp
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact hfixed.le ⟨v.property, (c.projection_eq_one_iff v).mp hv⟩
  have hs : AddSubgroup.closure
      {w : c.Space | ∃ (z : V) (d : L), (z : G) ∈ f.Vi 0 ⊓ omegaCenter T ∧ (d : G) ∈ A ∧
        w = c.modelAction (c.quotientMap d) (c.projection z).toAdd} ≤
        W.toAddSubgroup := by
    apply (AddSubgroup.closure_le _).mpr
    rintro w ⟨z,d,hz,hd,rfl⟩
    rw [← c.projection_component_conjugation]
    exact mem_map_of_mem c.projection
      ((omegaClosure_normalized T H (hAH hd) z.val).mp
        (omegaCenter_le_closure T H hz.2))
  intro v hv
  have hvV : v ∈ V := D.centralQuotientPreimage_le _ hv
  let v' : V := ⟨v,hvV⟩
  have hm : c.projection v' ∈ W :=
    hs (hspan ((c.mem_preimage (f.space 0) v').mp hv))
  obtain ⟨u,hu,he⟩ := hm
  have heu : u = v' := hi he
  have hvW : v' ∈ (omegaClosure T H).subgroupOf V := heu ▸ hu
  exact hvW

/-- Specialization to the literal D₀, retaining the source Cartan choice and
original flag. The two model inputs are a nontrivial line scalar and an orbit
span; neither the ambient commutator nor V₁≤V_H is an input. -/
theorem source_line_of_scalar_and_orbit
    {H : Subgroup G} (c : Coordinates D F) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (A X : Subgroup G) (hAH : A ≤ H)
    (hX : IsCartan T L X) (hAX : oddCartanPart A ≤ X)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (d : L) (hd : (d : G) ∈ oddCartanPart A)
    (a : F.Carrier) (ha : a ≠ 1)
    (hscalar : ∀ w ∈ f.space 0, c.modelAction (c.quotientMap d) w = a • w)
    (hspan : (f.space 0).toAddSubgroup ≤ AddSubgroup.closure
      {w : c.Space | ∃ (z : V) (d : L), (z : G) ∈ f.Vi 0 ⊓ omegaCenter T ∧
        (d : G) ∈ oddCartanPart A ∧
        w = c.modelAction (c.quotientMap d) (c.projection z).toAdd}) :
    f.Vi 0 = ⁅f.Vi 0, oddCartanPart A⁆ ∧ f.Vi 0 ≤ omegaClosure T H :=
  ⟨source_line_commutator_of_scalar c f hu _ X hX hAX hfixed d hd a ha hscalar,
    source_line_le_closure_of_orbit_span c f _ ((oddCartanPart_le A).trans hAH)
      hfixed hspan⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

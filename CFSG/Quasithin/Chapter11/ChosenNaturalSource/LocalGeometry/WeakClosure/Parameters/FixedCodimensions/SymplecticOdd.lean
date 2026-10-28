module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.Involutions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.OddField
public import Theory.Representation.SymplecticConjugatePair.OddOrder

/-!
# Odd prime displacement on the full symplectic natural automizer

Write a binary normalizer actor as scalar times inner-field. A nontrivial
field part moves at least two thirds of the four-space. For a field-linear
actor, a nonidentity scalar makes its fixed space totally isotropic;
otherwise coprime symplectic invariants are nondegenerate and have even
dimension. Both branches give binary codimension at least 2n.

The faithful coordinate quotient transports the bound to the literal
original automizer, including nonsplit central covers. The Source endpoint
uses this result to complete FixedCodimensions and the residual application
in the symplectic row.

Source: Aschbacher--Smith, I.2.3(1) and 11.2.2(1--2), printed pp.413,767--768.
-/

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
variable {H F : Type*} [Group H] [Field F] [Finite F] [Algebra (ZMod 2) F]
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
variable [CharP F 2]

/-- All odd prime actors in the full binary symplectic normalizer move at
least two coefficient-field dimensions, including scalar and field actors. -/
theorem symplectic_odd_lower
    (ρ : Representation (ZMod 2) H (Vector F)) (hρ : Function.Injective ρ)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (a : H) (ha : orderOf a = p)
    (hn : linearAction ρ a ∈ naturalNormalizer) :
    2 * Module.finrank (ZMod 2) F ≤ fixedCodim ρ (zpowers a) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨b,g,σ,he⟩ := naturalNormalizer_semilinear (linearAction ρ a) hn
  have hsemi (r : F) (v : Vector F) : ρ a (r • v) = σ r • ρ a v := by
    have hf : fieldVector σ (r • v) = σ r • fieldVector σ v := by
      funext i
      exact map_mul σ r (v i)
    change linearAction ρ a (r • v) = σ r • linearAction ρ a v
    rw [he,he]
    change b.val • symplecticNatural 2 g (fieldVector σ (r • v)) =
      σ r • (b.val • symplecticNatural 2 g (fieldVector σ v))
    rw [hf,map_smul,smul_comm]
  by_cases hs : σ = 1
  · have he' (v : Vector F) : ρ a v = b.val • symplecticNatural 2 g v := by
      rw [hs] at he
      have hf : fieldVector (1 : F ≃+* F) v = v := by ext i; rfl
      have hh := he v
      change ρ a v = b.val • symplecticNatural 2 g (fieldVector 1 v) at hh
      rwa [hf] at hh
    let t : Module.End F (Vector F) := b.val • symplecticNatural 2 g
    let Q := (t - LinearMap.id).ker
    have hQ (v : Vector F) : v ∈ Q ↔ ρ a v = v := by
      change t v - v = 0 ↔ _
      rw [sub_eq_zero]
      exact (congrArg (· = v) (he' v).symm).to_iff
    have hfix : fixedSpace ρ (zpowers a) = Q.restrictScalars (ZMod 2) := by
      ext v
      exact (mem_fixedSpace_zpowers_iff ρ a v).trans (hQ v).symm
    by_cases hb : b = 1
    · have hact (v : Vector F) : ρ a v = symplecticNatural 2 g v := by
        simpa only [hb, Units.val_one, one_smul] using he' v
      have hn1 : g ≠ 1 := by
        intro hg
        have ha1 : a = 1 := hρ (by
          apply LinearMap.ext
          intro v
          simpa only [hg, map_one, Module.End.one_apply] using hact v)
        simp only [ha1, orderOf_one] at ha
        exact hp.ne_one ha.symm
      have hgp : g ^ p = 1 := by
        apply SymplecticNaturalNormalizer.naturalHom_injective
        have hop : linearAction ρ a = SymplecticNaturalNormalizer.naturalHom g := by
          apply LinearEquiv.ext
          intro v
          exact hact v
        rw [map_pow, ← hop, ← map_pow, show a ^ p = 1 from ha ▸ pow_orderOf_eq_one a,
          map_one, map_one]
      have hgo : Odd (orderOf g) := (orderOf_eq_prime hgp hn1).symm ▸ ho
      have hfg : Q = SymplecticConjugatePair.OddOrder.naturalFixed g := by
        ext v
        rw [hQ, hact, SymplecticConjugatePair.OddOrder.mem_naturalFixed]
      have hdim := SymplecticConjugatePair.OddOrder.natural_codim_cases hn1 hgo
      unfold fixedCodim
      rw [hfix, (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) Q).finrank_eq,
        ← Module.finrank_mul_finrank (ZMod 2) F (Vector F ⧸ Q), hfg]
      rcases hdim with h | h <;> rw [h] <;> omega
    · have hb2 : b.val ^ 2 ≠ 1 := by
        intro h
        apply hb
        apply Units.ext
        exact CharTwo.sq_injective (h.trans (one_pow 2).symm)
      have hi : Q ≤ (form F).orthogonal Q := by
        intro v hv w hw
        have hv' := (hQ v).mp hv
        have hw' := (hQ w).mp hw
        have hpair : form F w v = b.val ^ 2 * form F w v := by
          calc
            form F w v = form F (ρ a w) (ρ a v) := by rw [hw',hv']
            _ = b.val ^ 2 * form F w v := by
              rw [he',he']
              simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
              change b.val * (b.val * form F (g • w) (g • v)) = _
              rw [preserves_form]
              ring
        have hz : (b.val ^ 2 - 1) * form F w v = 0 := by rw [sub_mul,one_mul,← hpair,sub_self]
        exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hb2)
      have hdim := Submodule.finrank_mono hi
      rw [LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate] at hdim
      have hd : Module.finrank F (Vector F) = 4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
      have hsum := Q.finrank_quotient_add_finrank
      have htwo : 2 ≤ Module.finrank F (Vector F ⧸ Q) := by omega
      unfold fixedCodim
      rw [hfix, (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) Q).finrank_eq,
        ← Module.finrank_mul_finrank (ZMod 2) F (Vector F ⧸ Q)]
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (Module.finrank (ZMod 2) F) htwo
  · have hh := odd_field_lower ρ hp ho a ha σ hs hsemi
    have hd : Module.finrank F (Vector F) = 4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
    rw [hd] at hh
    omega

open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The odd-prime bound on the literal full automizer of the original Sp₄
module. The coordinate surjection retains every nonsplit central attachment. -/
theorem sp4_odd_prime_lower
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    letI := D.elementary
    ∀ p : ℕ, p.Prime → Odd p → ∀ a : Automizer V, orderOf a = p →
      2 * S.field.degree ≤ fixedCodim (automizerRepresentation V) (zpowers a) := by
  let := D.elementary
  intro p hp ho a ha
  let c := Coordinates.sp4 m
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let := layer_normal D S
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    have hn := S.nonbinary
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hn
  have hn := SymplecticNaturalNormalizer.operator_mem_naturalNormalizer
    (inducedAutomizer V L) hq (layerEquiv D S c) ρ hres a
  have hd := symplectic_odd_lower ρ hρ hp ho a ha hn
  rw [Representation.OneCohomology.coefficient_finrank_of_card 2 _ S.field.card_eq] at hd
  exact hd.trans (fixedCodim_le_of_equivariant_surjection
    (automizerRepresentation V) ρ (projectionLinear D S c)
    (projectionLinear_surjective D S c) he (zpowers a))
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer

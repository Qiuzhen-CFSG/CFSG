module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Fusion
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.Marking
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Equivalence

/-!
# The source flag and square conjugator for denominator symmetry

The Sylow image in the actual six-letter action contains a conjugate of the
canonical two-Sylow subgroup. Reframing the original coordinates therefore
constructs the natural line/hyperplane flag required by the cover argument.
The original line and plane also admit one even marking. Explicit plane
involutions lift through L's given central quotient; their squares fix V
and lie in the centralizer of the original line generator.

These constructions remove the geometry inputs in the source application of
13.8.7 used in 13.8.27(3). No abstract model tag or transporter is assumed.
Source: Aschbacher--Smith, Notation 13.2.1 and 13.8.7, pp.877,948--949.
-/

public section

open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Symmetry
open SourceCompletion Section07.NaturalAction
open CriticalGeometry.AsymmetricPair
open CoverGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem subspace_rank {V : Subgroup G} (e : V ≃* Multiplicative N)
    (X : Subgroup G) (hX : X ≤ V) (n : ℕ) (hc : Nat.card X = 2^n) :
    Module.finrank (ZMod 2) (subspace e X) = n := by
  have he : Nat.card (subspace e X) = Nat.card X := by
    change Nat.card ((X.subgroupOf V).map e.toMonoidHom) = Nat.card X
    rw [card_map_of_injective e.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card,
    ZMod.card, hc] at he
  exact Nat.pow_right_injective (by decide : 1 < 2) he

private noncomputable def reframe {M V : Subgroup G} (a : NaturalAction M V)
    (g : Equiv.Perm (Fin 6)) : NaturalAction M V where
  normalizes := a.normalizes
  perm := (MulAut.conj g⁻¹).toMonoidHom.comp a.perm
  coordinate := a.coordinate.trans
    (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((naturalRepresentation (Fin 6)).asGroupHom g⁻¹)).toAddEquiv.toMultiplicative
  equivariant := by
    intro m v
    change naturalRepresentation (Fin 6) g⁻¹ (a.coordinate _).toAdd =
      naturalRepresentation (Fin 6) (g⁻¹ * a.perm m * g)
        (naturalRepresentation (Fin 6) g⁻¹ (a.coordinate v).toAdd)
    rw [a.equivariant]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 1
    group

variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)

include d in
theorem natural_flag : ∃ a : NaturalAction (M ⊓ normalizer (V : Set G)) V,
    NaturalFlag a (T : Subgroup G) V₁ V₃ := by
  let B := M ⊓ normalizer (V : Set G)
  have hTB : (T : Subgroup G) ≤ B := le_inf (by rw [d.local_normalizer]; exact d.normalizes_L)
    (le_sup_right.trans d.normalizes_V)
  let a₀ : NaturalAction B V := {
    normalizes := inf_le_right
    perm := Section05.QuadraticSource.permutation d
    coordinate := d.coordinate
    equivariant := fun g v => Section05.QuadraticSource.conjugation d g v }
  have hAlt : alternatingGroup (Fin 6) ≤ a₀.perm.range := by
    intro x hx
    obtain ⟨q, hq⟩ := d.local_quotient.surjective ⟨x,hx⟩
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective _ q
    refine ⟨inclusion (Section05.QuadraticSource.L_le_local d) l, ?_⟩
    change (Section05.QuadraticSource.local_permutation_extension d).choose _ = x
    rw [(Section05.QuadraticSource.local_permutation_extension d).choose_spec.1 l, hl, hq]
  let Q := (T.subtype hTB).mapSurjective a₀.perm.rangeRestrict_surjective
  have hQ : (Q : Subgroup a₀.perm.range).map a₀.perm.range.subtype =
      ((T : Subgroup G).subgroupOf B).map a₀.perm := by
    rw [Sylow.coe_mapSurjective, map_map, Sylow.coe_subtype]
    rfl
  obtain ⟨g, hg⟩ := exists_conjugate_T0_le a₀.perm.range hAlt Q
  let a := reframe a₀ g.val
  refine ⟨a, {
    line_le := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
    hyperplane_le := d.seed_le
    line_rank := subspace_rank a.coordinate _
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 d.line_card
    hyperplane_rank := subspace_rank a.coordinate _ d.seed_le 3 d.seed_card
    normalizes_line := d.line_stable
    normalizes_hyperplane := d.seed_stable
    borel_lifts := ?_ }⟩
  intro t ht
  have hh := hg (mem_map_of_mem (MulAut.conj g.val).toMonoidHom ht)
  rw [hQ] at hh
  obtain ⟨m, hm, he⟩ := hh
  refine ⟨m, ?_, hm⟩
  change g.val⁻¹ * a₀.perm m * g.val = t
  change a₀.perm m = g.val * t * g.val⁻¹ at he
  rw [he]
  group


include d in
theorem square_conjugator {H : Subgroup G} (A : Subgroup G) (z : V)
    (hH : H = centralizer ({(z : G)} : Set G))
    (hline : V₁ = zpowers (z : G)) (hA : A ≤ V₂) (hc : Nat.card A = 2) :
    ∃ l ∈ L, A = V₁.conjBy l ∧ l ^ 2 ∈ H := by
  let ρ := naturalRepresentation (Fin 6)
  obtain ⟨g, hg₁, hg₂⟩ := Section05.QuadraticSource.source_even_flag d
  have unmark {X : Subgroup G} {W : Submodule (ZMod 2) N}
      (he : image d X = move g.val W) (v : V) (hv : (v : G) ∈ X) :
      ρ g.val⁻¹ (d.coordinate v).toAdd ∈ W := by
    have hm := (mem_image d X _).mpr ⟨v, hv, rfl⟩
    rw [he] at hm
    obtain ⟨w, hw, hew⟩ := hm
    change ρ g.val w = (d.coordinate v).toAdd at hew
    rw [← hew, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    exact hw
  have nz (v : V) (hv : (v : G) ≠ 1) :
      ρ g.val⁻¹ (d.coordinate v).toAdd ≠ 0 := by
    intro he
    have he' := congrArg (ρ g.val) he
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, map_zero] at he'
    exact hv (congrArg Subtype.val (d.coordinate.injective
      (he'.trans (map_one d.coordinate).symm)))
  have hz1 : (z : G) ≠ 1 := by
    intro hz
    have h := d.line_card
    rw [hline, hz] at h
    simp at h
  have hz : ρ g.val⁻¹ (d.coordinate z).toAdd = pairVector 4 5 := by
    have hm := unmark hg₁ z (hline ▸ mem_zpowers (z : G))
    obtain ⟨c, he⟩ := Submodule.mem_span_singleton.mp hm
    have hn := nz z hz1
    fin_cases c
    · change (0 : ZMod 2) • (pairVector 4 5 : N) = _ at he
      exact False.elim (hn (by simpa only [zero_smul] using he.symm))
    · change (1 : ZMod 2) • (pairVector 4 5 : N) = _ at he
      simpa only [one_smul] using he.symm
  obtain ⟨x, hx, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hc
  have hx1 : (x : G) ≠ 1 := fun he => hx (Subtype.ext he)
  let xv : V := ⟨x, (d.plane_le_seed.trans d.seed_le) (hA x.property)⟩
  obtain ⟨s, hs, hs2, hsw⟩ := SixCenterGeometry.square_swap
    (ρ g.val⁻¹ (d.coordinate xv).toAdd) (unmark hg₂ xv (hA x.property)) (nz xv hx1)
  let k : alternatingGroup (Fin 6) := g * ⟨s, hs.2⟩ * g⁻¹
  obtain ⟨l, hl⟩ := Section05.QuadraticSource.exists_source_even_actor d k
  let lM := inclusion (Section05.QuadraticSource.L_le_local d) l
  have he (v : V) := Section05.QuadraticSource.conjugation d lM v
  have hlz : V.normalizerMonoidHom ⟨l.val, lM.property.2⟩ z = xv := by
    have hact : ρ k.val (d.coordinate z).toAdd = (d.coordinate xv).toAdd := by
      change ρ (g.val * s * g.val⁻¹) _ = _
      rw [map_mul, Module.End.mul_apply, hz, map_mul, Module.End.mul_apply, hsw]
      simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    have hez := he z
    rw [hl] at hez
    exact d.coordinate.injective (hez.trans hact)
  have hk2 : k.val ^ 2 = 1 := by
    change (g.val * s * g.val⁻¹) ^ 2 = 1
    calc
      _ = g.val * s ^ 2 * g.val⁻¹ := by simp [pow_two, mul_assoc]
      _ = 1 := by rw [hs2]; group
  have hperm2 : Section05.QuadraticSource.permutation d (lM ^ 2) = 1 := by
    rw [map_pow, hl, hk2]
  refine ⟨l.val, l.property, ?_, ?_⟩
  · rw [hline, CenterQuotientAction.line_eq_zpowers A hc x hx1]
    change zpowers (x : G) = (zpowers (z : G)).map (MulAut.conj l.val).toMonoidHom
    rw [MonoidHom.map_zpowers]
    exact congrArg zpowers (congrArg Subtype.val hlz).symm
  · rw [hH]
    apply mem_centralizer_singleton_iff.mpr
    apply (mul_inv_eq_iff_eq_mul).mp
    have he2 := Section05.QuadraticSource.conjugation d (lM ^ 2) z
    rw [hperm2, map_one, Module.End.one_apply] at he2
    exact congrArg Subtype.val (d.coordinate.injective he2)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Symmetry

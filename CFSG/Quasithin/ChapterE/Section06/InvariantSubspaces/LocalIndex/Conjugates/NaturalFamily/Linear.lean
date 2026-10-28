module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.NaturalFamily.FixedSpaces
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Coordinates
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Full fixed subgroups from the natural Baumann action

Assume the published factorizations `Q = UD`, `S = UˣQ` and
`D ≤ C_S(Uˣ)`, with `Φ(D) = 1`. Given the actual natural action coordinates,
we prove `C_Q(s) = Q ∩ (UˣD)` for every `s ∈ S - Q`.

The central layer is retained. In the natural plane, a nonidentity
upper-unipotent actor fixes the first coordinate line. Every vector on this
line is a displacement of an actual vector of U by an actual element of S.
Thus its full preimage lies in `[U,S] C_U(L)`. Normality and `S = UˣQ`
put `[U,S]` in Uˣ, while `C_U(L) ≤ D`. Also D centralizes S, since Q and
UˣD are elementary. This gives the required containment of full fixed
subgroups; the reverse containment follows from the same elementary factors.

The final theorem remains conditional on `LinearCoordinatesInput`, whose
owner constructs the genuine natural action. No additional fixed-lifting
or universal-cover premise is needed after the authorized factorizations.
The argument applies to the defining module for L₂(4) as well.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the natural
case of C.5.6, printed pp.156–157, and C.5.7, printed p.160.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.NaturalFamily.Linear

open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
open Factorizations.NaturalIndices
universe u
variable {G : Type u} [Group G] {R L : Subgroup G}
variable {F₀ : Type*} [Field F₀]

private theorem first_line_lifts (c : ActionCoordinates R L F₀) (u : U L)
    (hu : (c.projection u).toAdd 1 = 0) :
    (u : G) ∈ ⁅U L, S R⁆ ⊔ (U L ⊓ centralizer (L : Set G)) := by
  obtain ⟨s, hs⟩ := c.parameter_surjective (Multiplicative.ofAdd (1 : F₀))
  obtain ⟨v, hv⟩ := c.projection_surjective
    (Multiplicative.ofAdd ![0, (c.projection u).toAdd 0])
  let w : U L := moduleConjugate c.normalizes s v * v⁻¹
  have hw : (w : G) ∈ ⁅U L, S R⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator s.property v.property
  have hp : c.projection w = c.projection u := by
    apply Multiplicative.toAdd.injective
    change (c.projection (moduleConjugate c.normalizes s v * v⁻¹)).toAdd = _
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
    rw [c.equivariant, hs, hv]
    ext i
    fin_cases i <;> simp [hu]
  have hk : (u * w⁻¹ : U L) ∈ c.projection.ker := by
    change c.projection (u * w⁻¹) = 1
    rw [map_mul, map_inv, hp, mul_inv_cancel]
  have hker : ((u * w⁻¹ : U L) : G) ∈ U L ⊓ centralizer (L : Set G) :=
    ⟨(u * w⁻¹).property, (c.projection_kernel _).mp hk⟩
  have hh := (⁅U L, S R⁆ ⊔ (U L ⊓ centralizer (L : Set G))).mul_mem
    (mem_sup_right hker) (mem_sup_left hw)
  simpa only [coe_mul, coe_inv, inv_mul_cancel_right] using hh

variable [Finite G] {K : GroupClass.{u}} {A H : Subgroup G} {x : G}

/-- The actual natural quotient action suffices for the full fixed subgroup
once the conjugate factorizations and Frattini-zero hypothesis are supplied.
The central kernel is absorbed in D, rather than discarded. -/
theorem fixedSpaceCalculation_of_coordinates
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hx : x ∈ A) (hp : Factorization R L x) (hf : F R L = ⊥)
    (c : ActionCoordinates R L F₀) : FixedSpaceCalculation R L x := by
  let V := (U L).map (MulAut.conj x).toMonoidHom
  have hel := elementary_candidates_of_frattini_eq_bot h hb hp hf
  let _ : IsElementaryAbelian 2 (Q R L) := hel.1
  let _ : IsElementaryAbelian 2 (opposite R L x) := hel.2
  have hQself : Q R L ≤ centralizer (Q R L : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hEself : opposite R L x ≤ centralizer (opposite R L x : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hDQ : D R L ≤ Q R L := hp.core ▸ le_sup_right
  have hQS : Q R L ≤ S R := hb.core_eq ▸ inf_le_left
  have hVS : V ≤ S R := hp.span ▸ le_sup_left
  have hSV : S R ≤ normalizer (V : Set G) :=
    (show S R ≤ R from inf_le_left).trans (Factorizations.R_normalizes_conjugate h hx)
  have hQV : Q R L ≤ normalizer (V : Set G) := hQS.trans hSV
  have hQcent : Q R L ≤ centralizer (U L : Set G) := hb.core_eq ▸ inf_le_right
  have hcomm : ⁅U L, S R⁆ ≤ V := by
    rw [← commutator_eq_of_centralizing_sup
      ((sup_comm (Q R L) V).trans hp.span.symm) hQcent (hVS.trans c.normalizes)]
    exact le_normalizer_iff_commutator_le_right.mp ((module_le_core h hb).trans hQV)
  have hDcent : D R L ≤ centralizer (S R : Set G) := by
    rw [hp.span]
    exact le_centralizer_sup_of_le_centralizers hp.centralizes (hDQ.trans hQself)
  have hIcent : Q R L ⊓ opposite R L x ≤ centralizer (S R : Set G) := by
    rw [hp.span]
    exact le_centralizer_sup_of_le_centralizers
      ((inf_le_right.trans hEself).trans
        (centralizer_le (show V ≤ opposite R L x from le_sup_left)))
      (inf_le_left.trans hQself)
  refine ⟨fun s hs hsq => le_antisymm ?_ ?_⟩
  · rintro q ⟨hq, hqfix⟩
    refine ⟨hq, ?_⟩
    have hqprod : q ∈ (U L : Set G) * (D R L : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right]
      · exact hp.core ▸ hq
      · exact (le_centralizer_iff.mp (hDQ.trans hQcent)).trans
          (Subgroup.centralizer_le_normalizer _)
    obtain ⟨u, hu, d, hd, rfl⟩ := hqprod
    have hdfix : d ∈ centralizer ({s} : Set G) :=
      (centralizer_le (Set.singleton_subset_iff.mpr hs)) (hDcent hd)
    have hufix : u ∈ centralizer ({s} : Set G) :=
      ((centralizer ({s} : Set G)).mul_mem_cancel_right hdfix).mp hqfix
    let s₀ : S R := ⟨s, hs⟩
    let u₀ : U L := ⟨u, hu⟩
    have hparam : (c.parameter s₀).toAdd ≠ 0 := by
      intro he
      apply hsq
      rw [hb.core_eq]
      exact ⟨hs, (c.parameter_kernel s₀).mp (Multiplicative.toAdd.injective he)⟩
    have hfix : moduleConjugate c.normalizes s₀ u₀ = u₀ := by
      apply Subtype.ext
      change s * u * s⁻¹ = u
      rw [← mem_centralizer_singleton_iff.mp hufix, mul_inv_cancel_right]
    have hzero : (c.projection u₀).toAdd 1 = 0 := by
      have hh := congrArg (fun v : Multiplicative (Fin 2 → F₀) => v.toAdd 0)
        (congrArg c.projection hfix)
      rw [c.equivariant] at hh
      have hz : (c.parameter s₀).toAdd * (c.projection u₀).toAdd 1 = 0 := by
        simpa using hh
      exact (mul_eq_zero.mp hz).resolve_left hparam
    have hfixedD : U L ⊓ centralizer (L : Set G) ≤ D R L :=
      le_inf (inf_le_left.trans hb.module_le) inf_le_right
    have huE : u ∈ opposite R L x :=
      (sup_le (hcomm.trans le_sup_left) (hfixedD.trans le_sup_right))
        (first_line_lifts c u₀ hzero)
    exact (opposite R L x).mul_mem huE (mem_sup_right hd)
  · rintro q ⟨hq, hqe⟩
    exact ⟨hq, (centralizer_le (Set.singleton_subset_iff.mpr hs)) (hIcent ⟨hq, hqe⟩)⟩

/-- Assemble the natural fixed-space input from the earlier action-coordinate
construction. That construction remains an explicit undischarged premise. -/
theorem linearInput_of_coordinates
    (K : GroupClass.{u}) (hc : LinearCoordinatesInput (G := G) K) :
    LinearInput (G := G) K := by
  intro A H R L h hb hn x hx _ hp hf
  obtain ⟨n, hn⟩ := hn
  obtain ⟨F₀, _, _, _, c, _⟩ := hc A H R L h hb n hn
  exact fixedSpaceCalculation_of_coordinates h hb hx hp hf c

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.NaturalFamily.Linear

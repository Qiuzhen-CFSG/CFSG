module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Consequences
public import Theory.GroupTheory.SylowKernelCore
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Choosing an endpoint with the symmetric centralizer cover

The reversal in F.9.17 transports the entire pair of endpoints by one
ambient conjugation. It does not transport an assumption that one particular
large star image is not strong. Accordingly, refine the F.9.16(4) choice:
among all admissible endpoints with positive selected small-star rank,
maximize the large-star rank. This maximum exists because the endpoint
family is finite.

Suppose the rank squeeze at this endpoint gives the three equalities in
`equalities_of_not_strong`. The dimension equality says that the two
small-star ranks coincide. The reversed endpoint therefore remains eligible.
Maximality bounds its large-star rank by the original one, which equals the
small-star rank by the second equality. Inclusion and elementary abelianness
force equality of the two reversed star images. The exact action kernel then
gives the section-centralizer cover; cross-centralization turns this into
the ordinary-centralizer cover required by `strong_from_symmetric_cover`.
The fixed-space equality is part of that interface, but the other two
equalities already suffice for this argument.

The inputs `hselected` and `hreversal` are the precise earlier F.9.16(4)
and F.9.17 outputs needed here. The latter includes the same conjugating
element for all four endpoint groups, in both directions. The F.9 owner
must obtain it from the actual geodesics; arbitrary endpoint-specific
nonstrong hypotheses are never used in its place. The other inputs are the
actual section actions, F.9.13 endpoint placements, and the cross-centralizer
bound from Geometry.Local. This is a conditional chapter-15 helper, not a
formalization of the entire F.9 geometry or of 15.3.49.

The caller must adopt the resulting endpoint choice before using its later
local conclusions. The theorem does not assert the cover implication at
every previously selected endpoint. The comparison uses U_gamma/D_gamma,
not the rank of the whole U_gamma. Throughout U_H = localSpan ZS H and
V_H = localSpan V H retain their distinct source meanings.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.9.12–17, printed pp.322–324, especially the geodesic reversal on p.324;
15.3.49(n), printed p.1144. The maximal finite choice above makes the
quantifiers in that application of symmetry explicit.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Symmetry
variable {G : Type*} [Group G]

/-- The ambient local group, small span, large span, and central line at
one endpoint. At the base these are H, U_H, V_H, and Z. -/
structure Endpoint (G : Type*) [Group G] where
  K : Subgroup G
  U : Subgroup G
  V : Subgroup G
  Z : Subgroup G

/-- Transport all endpoint data by the same actual ambient conjugation.
Our convention is x ↦ g * x * g⁻¹. -/
def Endpoint.conjugate (a : Endpoint G) (g : G) : Endpoint G :=
  ⟨a.K.map (MulAut.conj g).toMonoidHom, a.U.map (MulAut.conj g).toMonoidHom,
    a.V.map (MulAut.conj g).toMonoidHom, a.Z.map (MulAut.conj g).toMonoidHom⟩

/-- F.9.17's normalized reversal: the old opposite endpoint becomes the
base, and the old base becomes another admissible opposite endpoint.
Both equalities concern all four subgroups, with one conjugating element. -/
def Reversal (base a b : Endpoint G) : Prop :=
  ∃ g : G, base.conjugate g = b ∧ a.conjugate g = base

variable [Finite G]

omit [Finite G] in
private theorem starRank_map (H A : Subgroup G) (hAH : A ≤ H) (e : G ≃* G) :
    rank (starImage (H.map e.toMonoidHom) (A.map e.toMonoidHom)) =
      rank (starImage H A) := by
  rw [rank, rank, starImage_card _ _ (map_mono hAH), starImage_card H A hAH]
  change Nat.log 2 (((H.map e.toMonoidHom).pCoreIn 2).relIndex (A.map e.toMonoidHom)) = _
  rw [← map_pCoreIn_of_injective 2 H e.toMonoidHom e.injective,
    relIndex_map_map_of_injective _ _ e.injective]
  rfl

private theorem kernelRank_eq_starRank
    (K U Z X : Subgroup G) [IsElementaryAbelian 2 U]
    (action : SectionAction K U Z) (hXK : X ≤ K) :
    Nat.log 2 ((sectionCentralizer X U Z).relIndex X) = rank (starImage K X) :=
  (starImage_rank K X _ hXK
    (sectionCentralizer_eq_core_intersection K U Z X action hXK)).symm

private theorem starImage_eq_of_rank_le
    (K U V : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hUV : U ≤ V) (hVK : V ≤ K)
    (hpos : 0 < rank (starImage K U))
    (hrank : rank (starImage K V) ≤ rank (starImage K U)) :
    starImage K U = starImage K V := by
  have hle : starImage K U ≤ starImage K V := map_mono (fun _ hx => hUV hx)
  have hUne : starImage K U ≠ ⊥ := by
    intro he
    rw [he, Representation.BinaryOffender.rank_bot] at hpos
    exact (Nat.lt_irrefl 0) hpos
  have hVne : starImage K V ≠ ⊥ := fun he => hUne (le_bot_iff.mp (hle.trans_eq he))
  have hU : IsElementaryTwo (starImage K U) := by
    let := IsElementaryAbelian.subgroupOf (p := 2) (hUV.trans hVK)
    exact ⟨hUne, IsElementaryAbelian.map _⟩
  have hV : IsElementaryTwo (starImage K V) := by
    let := IsElementaryAbelian.subgroupOf (p := 2) hVK
    exact ⟨hVne, IsElementaryAbelian.map _⟩
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hU.card_eq_two_pow_rank, hV.card_eq_two_pow_rank]
  exact pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) hrank

/-- Refine the F.9.16(4) choice so that the three nonstrong rank-squeeze
equalities imply the ordinary-centralizer cover. The finite maximum and the
reversed star-image equality are proved here; neither is an input.

`ends` ranges over the admissible geometric endpoints at the fixed base H.
`hselected` is the positive quotient-rank choice, and `hreversal` is the
simultaneous endpoint conjugation of F.9.17. All additional local inputs
are stated uniformly over this family, so the chosen endpoint retains them.
Final assembly of 15.3.49 must supply these earlier geometric inputs. -/
theorem exists_symmetric_cover
    {ι : Type*} [Finite ι]
    (H V ZS Z : Subgroup G) (ends : ι → Endpoint G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    [IsElementaryAbelian 2 (localSpan V H)]
    [∀ i, IsElementaryAbelian 2 (ends i).U]
    (action : SectionAction H (localSpan ZS H) Z)
    (opposite : ∀ i, SectionAction (ends i).K (ends i).U (ends i).Z)
    (hZS : ZS ≤ V) (hHZ : H ≤ centralizer (Z : Set G))
    (hUV : ∀ i, (ends i).U ≤ (ends i).V)
    (hVgH : ∀ i, (ends i).V ≤ H)
    (hVHK : ∀ i, localSpan V H ≤ (ends i).K)
    (hcross : ∀ i, sectionCentralizer (localSpan V H) (ends i).U (ends i).Z ≤
      centralizer ((ends i).V : Set G))
    (hselected : ∃ i,
      0 < Nat.log 2 ((sectionCentralizer (ends i).U (localSpan ZS H) Z).relIndex (ends i).U) ∧
      Nat.log 2 ((sectionCentralizer (localSpan ZS H) (ends i).U (ends i).Z).relIndex
        (localSpan ZS H)) ≤
      Nat.log 2 ((sectionCentralizer (ends i).U (localSpan ZS H) Z).relIndex (ends i).U))
    (hreversal : ∀ i,
      0 < Nat.log 2 ((sectionCentralizer (ends i).U (localSpan ZS H) Z).relIndex (ends i).U) →
      ∃ j, Reversal ⟨H, localSpan ZS H, localSpan V H, Z⟩ (ends i) (ends j)) :
    ∃ i,
      (0 < Nat.log 2 ((sectionCentralizer (ends i).U (localSpan ZS H) Z).relIndex (ends i).U) ∧
        Nat.log 2 ((sectionCentralizer (localSpan ZS H) (ends i).U (ends i).Z).relIndex
          (localSpan ZS H)) ≤
        Nat.log 2 ((sectionCentralizer (ends i).U (localSpan ZS H) Z).relIndex (ends i).U)) ∧
      (let D := sectionImage (localSpan ZS H) Z
          (sectionCentralizer (localSpan ZS H) (ends i).U (ends i).Z)
       D = fixedSpace action.representation (starImage H (ends i).V) →
       starImage H (ends i).U = starImage H (ends i).V →
       rank (starImage H (ends i).U) = Module.finrank (ZMod 2)
         (Additive (localSpan ZS H ⧸ Z.subgroupOf (localSpan ZS H)) ⧸ D) →
       localSpan V H = localSpan ZS H ⊔
         (localSpan V H ⊓ centralizer ((ends i).U : Set G))) := by
  let U := localSpan ZS H
  let X := localSpan V H
  have hUX : U ≤ X := conjugateSpanBy_mono hZS le_rfl
  have hUgH (i) : (ends i).U ≤ H := (hUV i).trans (hVgH i)
  have hUK (i) : U ≤ (ends i).K := hUX.trans (hVHK i)
  have hforward (i) := kernelRank_eq_starRank H U Z (ends i).U action (hUgH i)
  have hback (i) := kernelRank_eq_starRank (ends i).K (ends i).U (ends i).Z U
    (opposite i) (hUK i)
  let eligible : Set ι := {i | 0 < rank (starImage H (ends i).U) ∧
    rank (starImage (ends i).K U) ≤ rank (starImage H (ends i).U)}
  have hnonempty : eligible.Nonempty := by
    obtain ⟨i, hi, hle⟩ := hselected
    rw [hforward i] at hi hle
    rw [hback i] at hle
    exact ⟨i, hi, hle⟩
  obtain ⟨i, hi, hmax⟩ := Set.exists_max_image eligible
    (fun i => rank (starImage H (ends i).V)) (Set.toFinite _) hnonempty
  refine ⟨i, ?_, ?_⟩
  · rw [hforward i, hback i]
    exact hi
  · dsimp only
    intro _hfixed hstars hdim
    have hZD : Z ≤ sectionCentralizer U (ends i).U (ends i).Z := by
      apply le_commutatorPreimage action.layer_le
      exact (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp ((hUgH i).trans hHZ))).le.trans bot_le
    rw [sectionImage_quotient_finrank U Z _ hZD, hback i] at hdim
    have hipos : 0 < Nat.log 2
        ((sectionCentralizer (ends i).U U Z).relIndex (ends i).U) := by
      rw [hforward i]
      exact hi.1
    obtain ⟨j, g, hbase, hend⟩ := hreversal i hipos
    have hH := congrArg Endpoint.K hbase
    have hU := congrArg Endpoint.U hbase
    have hX := congrArg Endpoint.V hbase
    have hK := congrArg Endpoint.K hend
    have hUg := congrArg Endpoint.U hend
    dsimp only [Endpoint.conjugate] at hH hU hX hK hUg
    change U.map (MulAut.conj g).toMonoidHom = (ends j).U at hU
    change X.map (MulAut.conj g).toMonoidHom = (ends j).V at hX
    change (ends i).U.map (MulAut.conj g).toMonoidHom = U at hUg
    have hjforward : rank (starImage H (ends j).U) = rank (starImage (ends i).K U) := by
      have hh := starRank_map (ends i).K U (hUK i) (MulAut.conj g)
      rw [hK, hU] at hh
      exact hh
    have hjback : rank (starImage (ends j).K U) = rank (starImage H (ends i).U) := by
      have hh := starRank_map H (ends i).U (hUgH i) (MulAut.conj g)
      rw [hH, hUg] at hh
      exact hh
    have hjlarge : rank (starImage H (ends j).V) = rank (starImage (ends i).K X) := by
      have hh := starRank_map (ends i).K X (hVHK i) (MulAut.conj g)
      rw [hK, hX] at hh
      exact hh
    have hj : j ∈ eligible := by
      change 0 < rank (starImage H (ends j).U) ∧
        rank (starImage (ends j).K U) ≤ rank (starImage H (ends j).U)
      rw [hjforward, hjback, ← hdim]
      exact ⟨hi.1, le_rfl⟩
    have hlarge := hmax j hj
    rw [hjlarge, ← hstars, hdim] at hlarge
    have hreverseStar : starImage (ends i).K U = starImage (ends i).K X :=
      starImage_eq_of_rank_le (ends i).K U X hUX (hVHK i)
        (by rw [← hdim]; exact hi.1) hlarge
    have hcover := (starImage_eq_iff_centralizer_cover (ends i).K (ends i).U
      (ends i).Z X U (opposite i) hUX (hVHK i)).mp hreverseStar
    have hcentral : sectionCentralizer X (ends i).U (ends i).Z =
        X ⊓ centralizer ((ends i).U : Set G) :=
      commutatorPreimage_eq_relativeCentralizer _ _ _
        ((hcross i).trans (centralizer_le (hUV i)))
    exact hcover.trans (congrArg (fun D => U ⊔ D) hcentral)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Symmetry

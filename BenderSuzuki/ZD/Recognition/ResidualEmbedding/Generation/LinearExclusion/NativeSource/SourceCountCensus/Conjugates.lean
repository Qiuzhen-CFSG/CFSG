module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountCensus.Geometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountCensus.Family

/-!
# The original M-conjugates of the centralizer two-core

The q² distinct conjugate subgroups have equal orders and disjoint
nonidentity parts. Each avoids A, which is normal in M. Their literal
inclusions give the lower bound needed before the normalizer-growth step.

Source: GLS4, Chapter 2, Lemma 15.6, first paragraph.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount.Census
open Subgroup Theory.GroupTheory
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "A" => closure (Z ∩ (M : Set G))
local notation "U" => twoCore M z t
local notation "R" => sourceNormalizer Z M z t

@[expose] public def conjugateFamily (M : Subgroup G) (z t : G) :=
  Set.range fun m : M => (twoCore M z t).conjBy (m : G)

omit [Finite G] in
public theorem conjugate_card (C : conjugateFamily M z t) : Nat.card C.val = Nat.card U := by
  obtain ⟨m, hm⟩ := C.property
  rw [← hm]
  exact card_map_of_injective (MulAut.conj (m : G)).injective

include d
public theorem conjugate_square (hs : CentralizerLocalTwoData d)
    (C : conjugateFamily M z t) {x : G} (hx : x ∈ C.val) : x ^ 2 = 1 := by
  obtain ⟨m, hm⟩ := C.property
  rw [← hm] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [← map_pow, twoCore_square d hs hu, map_one]

public theorem conjugate_disjoint_distinguished (C : conjugateFamily M z t) :
    Disjoint A C.val := by
  obtain ⟨m, hm⟩ := C.property
  rw [← hm]
  apply disjoint_def.mpr
  rintro x hx ⟨u, hu, rfl⟩
  have huA : u ∈ A := by
    have hh := distinguished_conj_mem d (M.inv_mem m.property) hx
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hh
  rw [disjoint_def.mp (distinguished_disjoint_twoCore d) huA hu, map_one]

public theorem conjugate_pairwise_disjoint (C D : conjugateFamily M z t) (hne : C ≠ D) :
    Disjoint C.val D.val := by
  obtain ⟨m, hm⟩ := C.property
  obtain ⟨v, hv⟩ := D.property
  dsimp only at hm hv
  rcases d.centralizer_twoCore_ti ((m : G)⁻¹ * v) with he | hd
  · have he' := congrArg (fun H : Subgroup G => H.conjBy (m : G)) he
    change ((U).conjBy ((m : G)⁻¹ * v)).conjBy (m : G) = (U).conjBy (m : G) at he'
    rw [conjBy_conjBy, mul_inv_cancel_left, hm, hv] at he'
    exact (hne (Subtype.ext he'.symm)).elim
  · have hd' := disjoint_map (f := (MulAut.conj (m : G)).toMonoidHom) (MulAut.conj (m : G)).injective hd
    change Disjoint ((U).conjBy (m : G)) (((U).conjBy ((m : G)⁻¹ * v)).conjBy (m : G)) at hd'
    rw [conjBy_conjBy, mul_inv_cancel_left, hm, hv] at hd'
    exact hd'

public theorem conjugate_le_source (hs : CentralizerLocalTwoData d) (hg : NormalizerData d)
    (C : conjugateFamily M z t) : C.val ≤ R := by
  obtain ⟨m, hm⟩ := C.property
  rw [← hm]
  rintro x ⟨u, hu, rfl⟩
  exact source_conj_mem d hg m.property ((sup_le_sourceNormalizer d hs) ((show U ≤ A ⊔ U from le_sup_right) hu))

public theorem conjugate_le_pointCore (hs : CentralizerLocalTwoData d)
    (C : conjugateFamily M z t) : C.val ≤ pointCore M := by
  obtain ⟨m, hm⟩ := C.property
  rw [← hm]
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨v, hv, rfl⟩ := twoCore_le_pointCore d hs hu
  exact ⟨m * v * m⁻¹, (inferInstance : (pCore 2 M).Normal).conj_mem v hv m, rfl⟩

/-- The actual pre-growth lower bound: q²(r-1)+q elements already lie in V. -/
public theorem pointCore_card_lower (hs : CentralizerLocalTwoData d) :
    (2 ^ n) ^ 2 * (Nat.card U - 1) + 2 ^ n ≤ Nat.card (pointCore M) := by
  have hc := family_union_card A (pointCore M)
    (fun C : conjugateFamily M z t => C.val)
    (distinguished_le_pointCore d) (conjugate_le_pointCore d hs)
    (conjugate_disjoint_distinguished d) (conjugate_pairwise_disjoint d)
    (conjugate_card (M := M) (z := z) (t := t))
  have hcount : Nat.card (conjugateFamily M z t) = (2 ^ n) ^ 2 :=
    d.centralizer_twoCore_conjugates_card hs.twoCore_ne_bot
  rw [d.distinguished_elementary_card.2, hcount] at hc
  exact (Nat.add_comm _ _).trans_le hc

end BenderSuzuki.ZD.LinearExclusion.SourceCount.Census

module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Geometry
public import Theory.Representation.BinaryPermutation.FiveComplementSpan

/-!
# The original complementary-point four-group and its cubic displacement

Transport the explicit plane supported away from v into the actual A₅
module. Its three nonzero vectors are the conjugates of z v under the
literal residual O²(C_L(v)); thus this local span has order four and misses
v. The cubic displacement calculation puts z v in the commutator of this
span with the same residual, with no change of actor or quotient map.

This is the local orbit calculation in Aschbacher--Smith 13.2.12, printed
p.882. OriginalCentralization/PointSupport uses it to exclude a normal
four-element moved support in the full paired-point FF module.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open BinaryPermutation.FiveCentralizerGeometry
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G} (s : Marking L V)

def complementSpan : Subgroup G :=
  conjugateSpanBy (zpowers (markedZ s * markedV s)) (Lv L (markedV s))

private theorem complement_point_mem (i : Fin 3) :
    s.map (Multiplicative.ofAdd (ComplementSpan.point i)) ∈ complementSpan s := by
  obtain ⟨c,hc,he⟩ := exists_residual_cubic s
  have hconj (a : ↥(L ⊓ Gv (markedV s))) (ha : a ∈ pResidual 2 ↥(L ⊓ Gv (markedV s))) :
      s.map (Multiplicative.ofAdd (act (s.action (inclusion inf_le_left a)) (z+v))) ∈
        complementSpan s := by
    rw [← s.equivariant]
    have hx : s.map (Multiplicative.ofAdd (z+v)) = markedZ s * markedV s := s.map.map_mul _ _
    rw [hx]
    exact subset_closure ⟨a,⟨a,ha,rfl⟩,markedZ s * markedV s,mem_zpowers _,rfl⟩
  fin_cases i
  · change s.map (Multiplicative.ofAdd z * Multiplicative.ofAdd v) ∈ _
    rw [map_mul]
    exact le_conjugateSpanBy _ _ (mem_zpowers _)
  · change s.map (Multiplicative.ofAdd (act cubic (z+v))) ∈ _
    simpa only [he] using hconj c hc
  · change s.map (Multiplicative.ofAdd (act (cubic^2) (z+v))) ∈ _
    simpa only [map_pow,he] using hconj (c^2) ((pResidual 2 _).pow_mem hc 2)

/-- The local conjugate span is the actual complementary four-group. -/
theorem complementSpan_eq_plane : complementSpan s = ComplementSpan.plane.map s.map := by
  apply le_antisymm
  · apply conjugateSpanBy_le
    · apply zpowers_le.mpr
      exact ⟨Multiplicative.ofAdd (ComplementSpan.point 0),ComplementSpan.points_mem 0,
        s.map.map_mul _ _⟩
    · apply le_normalizer_iff.mpr
      rintro c ⟨a,ha,rfl⟩ x ⟨y,hy,rfl⟩
      exact ⟨Multiplicative.ofAdd (act (s.action (inclusion inf_le_left a)) y.toAdd),
        ComplementSpan.plane_invariant _ (stabilizer_fixes_v s a) y hy,
        (s.equivariant (inclusion inf_le_left a) y.toAdd).symm⟩
  · rintro x ⟨y,hy,rfl⟩
    rcases ComplementSpan.plane_cases y.toAdd hy with he | ⟨i,hi⟩
    · have he' : y=1 := he
      rw [he',map_one]
      exact one_mem _
    · change s.map (Multiplicative.ofAdd y.toAdd) ∈ _
      rw [hi]
      exact complement_point_mem s i

theorem complementSpan_card : Nat.card (complementSpan s) = 4 := by
  rw [complementSpan_eq_plane,card_map_of_injective s.injective]
  exact ComplementSpan.plane_card

theorem markedV_not_mem_complementSpan : markedV s ∉ complementSpan s := by
  rw [complementSpan_eq_plane]
  rintro ⟨y,hy,he⟩
  have he' : y = Multiplicative.ofAdd v := s.injective he
  exact ComplementSpan.v_not_mem_plane (he' ▸ hy)

/-- The marked complementary point already belongs to the local moved group. -/
theorem complement_mem_commutator_span :
    markedZ s * markedV s ∈ ⁅complementSpan s,Lv L (markedV s)⁆ := by
  obtain ⟨c,hc,he⟩ := exists_residual_cubic s
  obtain ⟨i,hi⟩ := ComplementSpan.point_mem_commutator 0
  have hh := commutator_mem_commutator (show (c:G) ∈ Lv L (markedV s) from ⟨c,hc,rfl⟩)
    (complement_point_mem s i)
  rw [commutator_comm] at hh
  have hcj := s.equivariant (inclusion inf_le_left c) (ComplementSpan.point i)
  rw [he] at hcj
  change MulAut.conj (c:G) (s.map (Multiplicative.ofAdd (ComplementSpan.point i))) = _ at hcj
  have hid : ⁅(c:G),s.map (Multiplicative.ofAdd (ComplementSpan.point i))⁆ =
      s.map (Multiplicative.ofAdd (ComplementSpan.point 0)) := by
    rw [commutatorElement_def]
    change MulAut.conj (c:G) (s.map (Multiplicative.ofAdd (ComplementSpan.point i))) *
      (s.map (Multiplicative.ofAdd (ComplementSpan.point i)))⁻¹ = _
    rw [hcj,←map_inv,←map_mul]
    rw [hi,ofAdd_sub,div_eq_mul_inv]
  rw [hid] at hh
  change s.map (Multiplicative.ofAdd z * Multiplicative.ofAdd v) ∈ _ at hh
  rwa [map_mul] at hh

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module

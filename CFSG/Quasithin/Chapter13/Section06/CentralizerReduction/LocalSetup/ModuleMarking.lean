module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Notation
public import Theory.Representation.BinaryPermutation.FiveCentralizerGeometry
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Transporting the binary A₅ marking to the actual residual

A marking identifies the even-weight five-point core with an actual subgroup
V, together with the surjective A₅ action induced by conjugation by L.
These are earlier module data, not a characteristic-two certificate. No
existence of a marking compatible with the source Sylow flag is asserted here.

The stabilizer of the marked v contains the displayed three-cycle. Surjective
transport of the two-residual lifts that cycle into O²(C_L(v)), even if its
first chosen lift has even order. The three conjugates of z then have product
v in the ambient group. In particular v belongs to the literal conjugate
span Vᵥ. The same marking supplies an ambient L-conjugate a of z.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the paragraph
before 13.6.4 on printed p.926, with the module conventions of §B.3.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
namespace A5Module
open BinaryPermutation.FiveCentralizerGeometry
variable {G : Type*} [Group G]
/-- An actual faithful module identification and its conjugation action. -/
structure Marking (L V : Subgroup G) where
  map : Multiplicative Space →* G
  injective : Function.Injective map
  range_eq : map.range = V
  action : L →* alternatingGroup (Fin 5)
  onto : Function.Surjective action
  equivariant : ∀ (l : L) (x : Space),
    MulAut.conj (l : G) (map (Multiplicative.ofAdd x)) =
      map (Multiplicative.ofAdd (act (action l) x))

variable {L V : Subgroup G} (s : Marking L V)
def markedZ : G := s.map (Multiplicative.ofAdd z)
def markedV : G := s.map (Multiplicative.ofAdd v)
def markedA : G := s.map (Multiplicative.ofAdd a)

theorem markedZ_mem_Gv : markedZ s ∈ Gv (markedV s) := by
  apply mem_centralizer_singleton_iff.mpr
  simpa only [markedZ, markedV, map_mul] using congrArg s.map
    (mul_comm (Multiplicative.ofAdd z) (Multiplicative.ofAdd v))

theorem exists_a_conjugator : ∃ c ∈ L, MulAut.conj c (markedZ s) = markedA s := by
  obtain ⟨c, hc⟩ := s.onto aConjugator
  refine ⟨c, c.property, ?_⟩
  change MulAut.conj (c : G) (s.map (Multiplicative.ofAdd z)) = _
  rw [s.equivariant, hc, conjugate_z_eq_a]
  rfl

/-- Lift the model three-cycle into the actual two-residual of C_L(v). -/
theorem exists_residual_cubic [Finite G] :
    ∃ c : ↥(L ⊓ Gv (markedV s)), c ∈ pResidual 2 ↥(L ⊓ Gv (markedV s)) ∧
      s.action (inclusion inf_le_left c) = cubic := by
  let D := L ⊓ Gv (markedV s)
  let f : D →* alternatingGroup (Fin 5) := s.action.comp (inclusion inf_le_left)
  have hg : cubic ∈ f.range := by
    obtain ⟨c, hc⟩ := s.onto cubic
    have hcv : (c : G) ∈ Gv (markedV s) := by
      apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      have he := s.equivariant c v
      rw [hc, cubic_fixes_v] at he
      exact he
    exact ⟨⟨c, c.property, hcv⟩, hc⟩
  let g : f.range := ⟨cubic, hg⟩
  have hg3 : g ^ 3 = 1 := Subtype.ext cubic_pow
  have hgr : g ∈ pResidual 2 f.range :=
    mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hg3))
  rw [← map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective] at hgr
  obtain ⟨c, hc, he⟩ := hgr
  exact ⟨c, hc, congrArg Subtype.val he⟩

/-- The three singular conjugates have product v in the ambient group. -/
theorem exists_residual_triple [Finite G] :
    ∃ c ∈ Lv L (markedV s),
      markedZ s * MulAut.conj c (markedZ s) * MulAut.conj (c ^ 2) (markedZ s) =
        markedV s := by
  obtain ⟨c, hc, he⟩ := exists_residual_cubic s
  refine ⟨c, ⟨c, hc, rfl⟩, ?_⟩
  have he2 : s.action (inclusion inf_le_left (c ^ 2)) = cubic ^ 2 := by
    rw [map_pow, map_pow, he]
  have h₁ := s.equivariant (inclusion inf_le_left c) z
  have h₂ := s.equivariant (inclusion inf_le_left (c ^ 2)) z
  rw [he] at h₁
  rw [he2] at h₂
  change MulAut.conj (c : G) (s.map (Multiplicative.ofAdd z)) = _ at h₁
  change MulAut.conj ((c : G) ^ 2) (s.map (Multiplicative.ofAdd z)) = _ at h₂
  simp only [markedZ, markedV]
  rw [h₁, h₂, ← map_mul, ← map_mul]
  exact congrArg (fun x : Space => s.map (Multiplicative.ofAdd x)) orbit_sum
/-- The product calculation puts the actual marked v in Vᵥ. -/
theorem markedV_mem_Vv [Finite G] : markedV s ∈ Vv L (markedZ s) (markedV s) := by
  obtain ⟨c, hc, he⟩ := exists_residual_triple s
  have hconj (d : G) (hd : d ∈ Lv L (markedV s)) :
      MulAut.conj d (markedZ s) ∈ Vv L (markedZ s) (markedV s) :=
    subset_closure ⟨d, hd, markedZ s, mem_zpowers _, rfl⟩
  have hp := mul_mem (mul_mem (z_mem_Vv L (markedZ s) (markedV s)) (hconj c hc))
    (hconj (c ^ 2) ((Lv L (markedV s)).pow_mem hc 2))
  rwa [he] at hp

/-- The mark z is a nonidentity vector in the actual subgroup. -/
theorem markedZ_ne_one : markedZ s ≠ 1 := by
  intro he
  have hh : Multiplicative.ofAdd z = 1 := s.injective (he.trans s.map.map_one.symm)
  exact z_ne_zero (congrArg Multiplicative.toAdd hh)

/-- The mark v is a nonidentity vector in the actual subgroup. -/
theorem markedV_ne_one : markedV s ≠ 1 := by
  intro he
  have hh : Multiplicative.ofAdd v = 1 := s.injective (he.trans s.map.map_one.symm)
  exact v_ne_zero (congrArg Multiplicative.toAdd hh)

/-- The mark a is a nonidentity vector in the actual subgroup. -/
theorem markedA_ne_one : markedA s ≠ 1 := by
  intro he
  have hh : Multiplicative.ofAdd a = 1 := s.injective (he.trans s.map.map_one.symm)
  exact a_ne_zero (congrArg Multiplicative.toAdd hh)

end A5Module
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction

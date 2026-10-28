module

public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.Commutator.NilpotentSaturation
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.Commutator.TwoOrbitSpan

/-!
# Collapsing a conjugate span inside a nilpotent kernel

Let W be the C-conjugate span of V inside a nilpotent subgroup Q which
normalizes V. If the C-displacements of W lie in [W,Q]Z with Z contained
in V, each conjugate generator lies in V[W,Q]. Nilpotent commutator
saturation then gives W = V. A local-generation wrapper derives the
displacement hypothesis from a bound for L when H = LQ and H normalizes
W, Q and Z.

This is the last span-collapse calculation in Meierfrankenfeld--Stellmacher,
*Pushing up weak BN-pairs of rank two* (1993), (5.9), printed p.921.
Only the kernel is required to be nilpotent; the ambient group may be an
infinite free amalgam.
-/

public section
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

/-- A comparison with kernel displacements and a normalized layer makes
the centralizer span invariant under a generating second subgroup. -/
theorem conjugateSpanBy_normalized_of_commutator_comparison
    (V C Q Z E H : Subgroup G) (hQV : Q ≤ normalizer (V : Set G))
    (hHQ : H ≤ normalizer (Q : Set G))
    (hHZ : H ≤ normalizer (Z : Set G)) (hZV : Z ≤ V)
    (hgen : C ⊔ E = H)
    (hcomm : ⁅conjugateSpanBy V C,E⁆ ≤
      ⁅conjugateSpanBy V C,Q⁆ ⊔ ⁅Z,E⁆) :
    H ≤ normalizer (conjugateSpanBy V C : Set G) := by
  have hCH : C ≤ H := hgen ▸ le_sup_left
  have hEH : E ≤ H := hgen ▸ le_sup_right
  have hQW := TwoOrbitSpan.normalizes_span V C Q hQV (hCH.trans hHQ)
  have hZW : Z ≤ conjugateSpanBy V C := hZV.trans (le_conjugateSpanBy V C)
  have hEW : E ≤ normalizer (conjugateSpanBy V C : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans (sup_le
      (le_normalizer_iff_commutator_le_left.mp hQW)
      ((le_normalizer_iff_commutator_le_left.mp (hEH.trans hHZ)).trans hZW)))
  rw [←hgen]
  exact sup_le (le_normalizer_conjugateSpanBy V C) hEW

/-- A displacement bound modulo the kernel commutator collapses the literal
conjugate span to its kernel-normalized seed. -/
theorem conjugateSpanBy_eq_of_nilpotent_commutator_bound
    (V C Q Z : Subgroup G) (hQ : Group.IsNilpotent Q)
    (hWQ : conjugateSpanBy V C ≤ Q) (hQV : Q ≤ normalizer (V : Set G))
    (hZV : Z ≤ V)
    (hcomm : ⁅conjugateSpanBy V C,C⁆ ≤ ⁅conjugateSpanBy V C,Q⁆ ⊔ Z) :
    conjugateSpanBy V C = V := by
  let W := conjugateSpanBy V C
  have hVW : V ≤ W := le_conjugateSpanBy V C
  apply le_antisymm ?_ hVW
  apply le_of_le_sup_commutator_of_isNilpotent Q W V Q hQ hWQ
    (hVW.trans hWQ) le_rfl hQV
  apply (closure_le _).mpr
  rintro _ ⟨c,hc,v,hv,rfl⟩
  change c * v * c⁻¹ ∈ V ⊔ ⁅W,Q⁆
  have hcv : ⁅c,v⁆ ∈ ⁅W,Q⁆ ⊔ Z := hcomm (by
    rw [commutator_comm]
    exact commutator_mem_commutator hc (hVW hv))
  have hbound : ⁅W,Q⁆ ⊔ Z ≤ V ⊔ ⁅W,Q⁆ :=
    sup_le le_sup_right (hZV.trans le_sup_left)
  have hmul := (V ⊔ ⁅W,Q⁆).mul_mem (hbound hcv) (mem_sup_left hv)
  simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hmul

/-- A bound for one local generator extends to the whole local group and
collapses the conjugate span in its nilpotent kernel. -/
theorem conjugateSpanBy_eq_of_nilpotent_local_generation
    (V C Q Z L H : Subgroup G) (hQ : Group.IsNilpotent Q)
    (hWQ : conjugateSpanBy V C ≤ Q) (hQV : Q ≤ normalizer (V : Set G))
    (hZV : Z ≤ V) (hCH : C ≤ H) (hgen : L ⊔ Q = H)
    (hHW : H ≤ normalizer (conjugateSpanBy V C : Set G))
    (hHQ : H ≤ normalizer (Q : Set G))
    (hHZ : H ≤ normalizer (Z : Set G))
    (hcomm : ⁅conjugateSpanBy V C,L⁆ ≤ ⁅conjugateSpanBy V C,Q⁆ ⊔ Z) :
    conjugateSpanBy V C = V := by
  let W := conjugateSpanBy V C
  let D := ⁅W,Q⁆ ⊔ Z
  have hHD : H ≤ normalizer (D : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_sup,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hHW hg),
      mem_normalizer_iff_map_conj_eq.mp (hHQ hg),
      mem_normalizer_iff_map_conj_eq.mp (hHZ hg)]
  have hfull : ⁅W,H⁆ ≤ D := by
    rw [commutator_comm,←hgen]
    exact commutator_sup_le_of_relative_normal H L Q W D hHD
      (hgen ▸ le_sup_left) (hgen ▸ le_sup_right)
      (by rwa [commutator_comm]) (by rw [commutator_comm]; exact le_sup_left)
  exact conjugateSpanBy_eq_of_nilpotent_commutator_bound V C Q Z hQ hWQ hQV hZV
    ((commutator_mono le_rfl hCH).trans hfull)

end Subgroup

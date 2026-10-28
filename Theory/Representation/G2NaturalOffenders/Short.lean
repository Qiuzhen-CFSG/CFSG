module
public import Theory.Representation.G2NaturalOffenders.Coordinates
public import Theory.SpecificGroups.G2Even.TwoRank
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Short-root-containing offenders on the natural G₂ module

A short root fixes a three-dimensional space over the defining field. The
sharp two-rank of the actual octonion group is three times the binary field
degree. The offender inequality therefore forces equality in both bounds.
Every offender containing the short root fixes that three-space pointwise;
the explicit centralizer calculation removes its SL₂ block and places it in
the A–B–C subgroup. Equality of orders then identifies the whole subgroup.

The argument concerns the actual restricted natural representation; its
coordinate equivalence preserves all fixed codimensions. Source:
Aschbacher–Smith B.4.6(6), (13), printed pp.88–90.
-/

@[expose] public noncomputable section
namespace Atlas.G2.NaturalOffenders
open Representation Representation.BinaryOffender Subgroup
open Restricted.NaturalCoordinates LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

def binaryAction : Representation (ZMod 2) (Model F) (Fin 6 → F) := restrictScalars (action F)

def binaryNatural : Representation (ZMod 2) (Model F) (Natural.Space F) :=
  restrictScalars (Natural.action F)

theorem natural_fixedCodim_eq (A : Subgroup (Model F)) :
    fixedCodim (binaryNatural (F:=F)) A = fixedCodim (binaryAction (F:=F)) A := by
  have h := fixedCodim_map_equivariant (binaryNatural (F:=F)) (binaryAction (F:=F))
    (MonoidHom.id _) ((equiv F).restrictScalars (ZMod 2))
    (fun g v => LinearMap.congr_fun ((repEquiv F).isIntertwining' g) v) A
  simpa only [Subgroup.map_id] using h

theorem natural_offender_iff (A : Subgroup (Model F)) :
    IsOffender (binaryNatural (F:=F)) A ↔ IsOffender (binaryAction (F:=F)) A := by
  simp only [IsOffender,natural_fixedCodim_eq]

theorem fixedSpace_elementary : fixedSpace (binaryAction (F:=F)) (EvenTwoRank.elementary F) =
    (upper (F:=F)).restrictScalars (ZMod 2) := by
  ext v
  constructor
  · intro hv
    exact (fixed_rootC_iff (1:F) one_ne_zero v).mp (hv ⟨rootC 1,rootC_mem_elementary 1⟩)
  · intro hv g
    exact elementary_fix_upper g.prop hv

theorem fixedSpace_longRootLocal : fixedSpace (binaryAction (F:=F)) longRootLocal =
    (upper (F:=F)).restrictScalars (ZMod 2) := by
  ext v
  constructor
  · intro hv
    exact mem_upper_of_fixed_longRoots
      (hv ⟨rootA 1,rootA_mem_longRootLocal 1⟩) (hv ⟨rootB 1,rootB_mem_longRootLocal 1⟩)
  · intro hv g
    exact longRoot_fix_upper g.prop hv

variable [Finite F]

omit [CharP F 2] in
theorem finrank_binary_field {n : ℕ} (hc : Nat.card F = 2^n) :
    Module.finrank (ZMod 2) F = n := by
  have h := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=F)
  rw [Nat.card_zmod,hc] at h
  exact (Nat.pow_right_injective (by decide : 1<2) h).symm

omit [CharP F 2] in
theorem upper_binary_finrank {n : ℕ} (hc : Nat.card F = 2^n) :
    Module.finrank (ZMod 2) ((upper (F:=F)).restrictScalars (ZMod 2)) = 3*n := by
  change Module.finrank (ZMod 2) (upper (F:=F)) = _
  rw [((upperEquiv (F:=F)).restrictScalars (ZMod 2)).finrank_eq]
  simp [Module.finrank_pi_fintype,finrank_binary_field hc]

omit [CharP F 2] in
theorem coordinates_binary_finrank {n : ℕ} (hc : Nat.card F = 2^n) :
    Module.finrank (ZMod 2) (Fin 6 → F) = 6*n := by
  simp [Module.finrank_pi_fintype,finrank_binary_field hc]

theorem fixedCodim_elementary {n : ℕ} (hc : Nat.card F = 2^n) :
    fixedCodim (binaryAction (F:=F)) (EvenTwoRank.elementary F) = 3*n := by
  have h := fixedCodim_add_finrank (binaryAction (F:=F)) (EvenTwoRank.elementary F)
  rw [fixedSpace_elementary,upper_binary_finrank hc,coordinates_binary_finrank hc] at h
  omega

theorem fixedCodim_longRootLocal {n : ℕ} (hc : Nat.card F = 2^n) :
    fixedCodim (binaryAction (F:=F)) longRootLocal = 3*n := by
  have h := fixedCodim_add_finrank (binaryAction (F:=F)) (longRootLocal (F:=F))
  rw [fixedSpace_longRootLocal,upper_binary_finrank hc,coordinates_binary_finrank hc] at h
  omega

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem elementary_rank {n : ℕ} (hc : Nat.card F = 2^n) :
    rank (EvenTwoRank.elementary F) = 3*n := by
  rw [rank,EvenTwoRank.elementary_card,hc,← pow_mul,Nat.log_pow (by decide : 1<2),Nat.mul_comm]

theorem offender_eq_elementary_of_shortRoot {n : ℕ} (hc : Nat.card F = 2^n)
    (A : Subgroup (Model F)) (hA : IsOffender (binaryAction (F:=F)) A)
    (a : F) (ha : a ≠ 0) (hmem : rootC a ∈ A) : A = EvenTwoRank.elementary F := by
  let : IsElementaryAbelian 2 A := hA.1.2
  have hfix : fixedSpace (binaryAction (F:=F)) A ≤ (upper (F:=F)).restrictScalars (ZMod 2) := by
    intro v hv
    exact (fixed_rootC_iff a ha v).mp (hv ⟨rootC a,hmem⟩)
  have hr : rank A ≤ 3*n := by
    have hb := (primeRank_le_iff_elementary_card_le (Model F)).mp (EvenTwoRank.two_rank F hc).le A hA.1.2
    have hh := Nat.log_mono_right (b:=2) hb
    simpa only [rank,Nat.log_pow (by decide : 1<2)] using hh
  have hd := fixedCodim_add_finrank (binaryAction (F:=F)) A
  have hf := Submodule.finrank_mono hfix
  rw [upper_binary_finrank hc] at hf
  rw [coordinates_binary_finrank hc] at hd
  have hcost := hA.2
  have heq : Module.finrank (ZMod 2) (fixedSpace (binaryAction (F:=F)) A) = 3*n := by omega
  have hAr : rank A = 3*n := by omega
  have hfE : fixedSpace (binaryAction (F:=F)) A = (upper (F:=F)).restrictScalars (ZMod 2) :=
    Submodule.eq_of_le_of_finrank_eq hfix (heq.trans (upper_binary_finrank hc).symm)
  have hle : A ≤ EvenTwoRank.elementary F := by
    intro g hg
    apply mem_elementary_of_centralizes_of_fix_upper a ha
    · exact congrArg (fun x : A => x.val)
        ((IsMulCommutative.is_comm (M:=A)).comm ⟨g,hg⟩ ⟨rootC a,hmem⟩)
    · intro v hv
      have hvA : v ∈ fixedSpace (binaryAction (F:=F)) A := hfE.symm ▸ hv
      exact hvA ⟨g,hg⟩
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [EvenTwoRank.elementary_card,hc,hA.1.card_eq_two_pow_rank,hAr,← pow_mul,Nat.mul_comm n 3]

end Atlas.G2.NaturalOffenders

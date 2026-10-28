module
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow normal closures contain p-subgroups

If a p-subgroup P is contained in a normal subgroup E of a finite group,
then P is contained in the normal closure of S∩E for any Sylow p-subgroup
S. The case E=G says that a Sylow normal closure contains every p-subgroup.

Extend P to a Sylow subgroup and conjugate that Sylow to S. Normality of E
keeps the conjugated elements in E; normality of the resulting normal
closure allows conjugation back. This generic reduction is used for the
SL₂ factor normal-closure step in Stellmacher (1.7) and for the dihedral
quotient bridge in (8.2), Journal of Algebra 190 (1997), pp.19 and37.
-/

public theorem IsPGroup.le_normalClosure_sylow_inf
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) (S : Sylow p G)
    (E : Subgroup G) (hE : E.Normal) (hPE : P ≤ E) :
    P ≤ Subgroup.normalClosure (((S : Subgroup G) ⊓ E : Subgroup G) : Set G) := by
  classical
  obtain ⟨T, hT⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  intro t ht
  let N := Subgroup.normalClosure (((S : Subgroup G) ⊓ E : Subgroup G) : Set G)
  have htS : g * t * g⁻¹ ∈ (S : Subgroup G) := by
    rw [← hg]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hT ht)
  have htn : g * t * g⁻¹ ∈ N :=
    Subgroup.le_normalClosure ⟨htS, hE.conj_mem t (hPE ht) g⟩
  have hback := (inferInstance : N.Normal).conj_mem (g * t * g⁻¹) htn g⁻¹
  change t ∈ N
  simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hback

public theorem IsPGroup.le_normalClosure_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) (S : Sylow p G) :
    P ≤ Subgroup.normalClosure ((S : Subgroup G) : Set G) := by
  simpa only [inf_top_eq] using
    hP.le_normalClosure_sylow_inf S ⊤ inferInstance le_top

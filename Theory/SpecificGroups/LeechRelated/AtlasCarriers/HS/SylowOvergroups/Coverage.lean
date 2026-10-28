module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Checks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.SupportChecks
public import Theory.GroupTheory.DoubleCosetCoverage

/-!
# Exhaustive Higman--Sims Sylow double cosets

The 270 representatives are words in the existing six-level stabilizer chain.
Counts of intersections between invariant orbits on ordered pairs separate
their double cosets. The rejection witnesses bound each intersection of the
Sylow with its conjugate. The corresponding lower bounds on double-coset
sizes sum to the exact carrier order, 44,352,000, proving coverage.

Source: ATLAS HSG1-p100B0; the Sylow-overgroup calculation in
Aschbacher--Smith A.3.12(18), printed pp.47--48. GAP only discovers candidates;
the finite equalities and the counting argument are checked in Lean.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.SylowOvergroups
open Subgroup DoubleCoset Theory.GroupTheory Data EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData


def representative (j : Fin 270) : Carrier := ⟨repPerm j, by
  rw [← NormalizerIndex.H0_eq_generated]
  exact OrderCertificate.H0.mul_mem
    (OrderCertificate.H0.mul_mem (OrderCertificate.H0.mul_mem
      (OrderCertificate.H0.mul_mem (OrderCertificate.H0.mul_mem
        (OrderCertificate.rep0_mem _) (OrderCertificate.H1_le (OrderCertificate.rep1_mem _)))
        (OrderCertificate.H1_le (OrderCertificate.H2_le (OrderCertificate.rep2_mem _))))
      (OrderCertificate.H1_le (OrderCertificate.H2_le (OrderCertificate.H3_le (OrderCertificate.rep3_mem _)))))
      (OrderCertificate.H1_le (OrderCertificate.H2_le (OrderCertificate.H3_le
        (OrderCertificate.H4_le (OrderCertificate.rep4_mem _))))))
    (OrderCertificate.H1_le (OrderCertificate.H2_le (OrderCertificate.H3_le
      (OrderCertificate.H4_le (OrderCertificate.H5_le (OrderCertificate.rep5_mem _))))))⟩

theorem representative_value (j : Fin 270) (p : Fin 100) : inclusion (representative j) p = dVal j p := rep_spec j p

theorem representative_inverse_value (j : Fin 270) (p : Fin 100) :
    inclusion (representative j)⁻¹ p = diVal j p := by
  rw [map_inv]
  apply (inclusion (representative j)).injective
  change (inclusion (representative j)) ((inclusion (representative j)).symm p) = _
  rw [Equiv.apply_symm_apply,representative_value,inverse_spec]

def pairPerm (g : Carrier) : Equiv.Perm Point := Equiv.prodCongr (inclusion g) (inclusion g)
private theorem pairPerm_inv (g : Carrier) : pairPerm g⁻¹ = (pairPerm g).symm := rfl

private theorem preserves_color (g : Carrier) (hg : g ∈ subgroup) :
    ∀ x : Point, color (pairPerm g x) = color x := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    rintro ⟨x,y⟩
    change color ((sylowGenerator i : Equiv.Perm (Fin 100)) x,
      (sylowGenerator i : Equiv.Perm (Fin 100)) y) = color (x,y)
    simpa only [sylow_generator_values] using generator_color i x y
  | one => intro x; rfl
  | mul a b _ _ ha hb => intro x; exact (ha (pairPerm b x)).trans (hb x)
  | inv a _ ha =>
    intro x
    have h := ha (pairPerm a⁻¹ x)
    simpa only [pairPerm_inv,Equiv.apply_symm_apply] using h.symm

private theorem preserves_source (g : Carrier) (hg : g ∈ subgroup) (k : Fin 16) :
    ∀ x : Point, pairPerm g x ∈ source k ↔ x ∈ source k := by
  have hforward : ∀ g ∈ subgroup, ∀ x ∈ source k, pairPerm g x ∈ source k := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      intro x hx
      change ((sylowGenerator i : Equiv.Perm (Fin 100)) x.1,
        (sylowGenerator i : Equiv.Perm (Fin 100)) x.2) ∈ source k
      simpa only [pairVal,sylow_generator_values] using generator_source i k x hx
    | one => intro x hx; exact hx
    | mul a b _ _ ha hb => intro x hx; exact ha _ (hb _ hx)
    | inv a _ ha =>
      have hinj : Function.Injective (fun x : source k =>
          (⟨pairPerm a x,ha x x.property⟩ : source k)) := fun x y h =>
        Subtype.ext ((pairPerm a).injective (congrArg Subtype.val h))
      intro x hx
      obtain ⟨y,hy⟩ := (Finite.surjective_of_injective hinj) ⟨x,hx⟩
      have he : pairPerm a y = x := congrArg Subtype.val hy
      have he' : pairPerm a⁻¹ x = y := by
        rw [← he]
        simp only [pairPerm_inv,Equiv.symm_apply_apply]
      exact he' ▸ y.property
  intro x
  constructor
  · intro hx
    have hh := hforward g⁻¹ (subgroup.inv_mem hg) _ hx
    simpa only [pairPerm_inv,Equiv.symm_apply_apply] using hh
  · exact hforward g hg x

private theorem count_invariant (g a b : Carrier) (ha : a ∈ subgroup) (hb : b ∈ subgroup) (k : Fin 16) :
    count (inclusion (a*g*b)) k = count (inclusion g) k := by
  exact filter_card_perm_mul_of_color (source k) color (target k) (pairPerm g) (pairPerm a) (pairPerm b)
    (preserves_color a ha) (preserves_source b hb k)

private theorem double_cosets_disjoint : Pairwise fun i j =>
    Disjoint (doubleCoset (representative i) subgroup subgroup)
      (doubleCoset (representative j) subgroup subgroup) := by
  intro i j hij
  by_contra hn
  obtain ⟨a,ha,b,hb,he⟩ := mem_doubleCoset.mp (mem_doubleCoset_of_not_disjoint hn)
  apply hij
  apply count_values_injective
  intro k
  have hcounts (t : Fin 270) :
      count (inclusion (if inverseFlag k then (representative t)⁻¹ else representative t)) k = countVal t k := by
    have heq : (fun p => inclusion (if inverseFlag k then (representative t)⁻¹ else representative t) p) =
        (if inverseFlag k then diVal t else dVal t) := by
      split <;> funext p
      · exact representative_inverse_value t p
      · exact representative_value t p
    exact (congrArg (fun f => count f k) heq).trans (counts_spec t k)
  rw [← hcounts i,← hcounts j,he]
  split
  · simp only [mul_inv_rev]
    exact (count_invariant _ _ _ (subgroup.inv_mem hb) (subgroup.inv_mem ha) k).symm
  · exact (count_invariant _ _ _ ha hb k).symm

private theorem intersection_bound (j : Fin 270) :
    Nat.card (subgroup ⊓ subgroup.map (MulAut.conj (representative j)).toMonoidHom : Subgroup Carrier) ≤ bound j := by
  classical
  let I := subgroup ⊓ subgroup.map (MulAut.conj (representative j)).toMonoidHom
  let f : I → {i : Fin 512 // reject j i = 100} := fun x =>
    let i := enumeration.symm ⟨x.val,x.property.1⟩
    ⟨i,by
      have hi : element i = x.val := congrArg Subtype.val (enumeration.apply_symm_apply ⟨x.val,x.property.1⟩)
      have hmem : (representative j)⁻¹ * x.val * representative j ∈ subgroup := by
        obtain ⟨y,hy,he⟩ := x.property.2
        change (representative j) * y * (representative j)⁻¹ = x.val at he
        rw [← he]
        simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using (show y ∈ subgroup from hy)
      have hcol := preserves_color _ hmem
      have ht := rejects_spec j i
      by_contra hn
      simp only [rejectTest,if_neg hn,decide_eq_true_eq] at ht
      apply ht
      let p : Fin 100 := ⟨reject j i % 100,Nat.mod_lt _ (by decide)⟩
      have h := hcol (p,p)
      change color (inclusion ((representative j)⁻¹ * x.val * representative j) p,
        inclusion ((representative j)⁻¹ * x.val * representative j) p) = color (p,p) at h
      have hsval (i : Fin 512) (p : Fin 100) : inclusion (element i) p = sVal i p :=
        (element_point i p).trans (sylow_values i p).symm
      simpa only [←hi,map_mul,Equiv.Perm.mul_apply,hsval,representative_value,
        representative_inverse_value,conjugateVal] using h⟩

  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have he := congrArg (fun z : {i : Fin 512 // reject j i = 100} => enumeration z.val) h
    have he' : (⟨x.val,x.property.1⟩ : subgroup) = ⟨y.val,y.property.1⟩ := by
      simpa only [f,Equiv.apply_symm_apply] using he
    exact congrArg (fun z : subgroup => (z : Carrier)) he'
  have hc : Nat.card {i : Fin 512 // reject j i = 100} = bound j := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    exact bound_spec j
  exact (Nat.card_le_card_of_injective f hf).trans_eq hc

/-- Every element belongs to one of the 270 certified Sylow double cosets. -/
theorem double_coset_cover (g : Carrier) :
    ∃ j, g ∈ doubleCoset (representative j) subgroup subgroup := by
  apply doubleCoset_cover_of_card_bound subgroup representative lower bound
    double_cosets_disjoint intersection_bound bounds_positive
  · intro i
    rw [EvenLocalCandidates.subgroup_card]
    exact sizes_mul i
  · rw [NormalizerIndex.card_carrier,sizes_sum]

end Sporadic.LeechRelated.HS.SylowOvergroups

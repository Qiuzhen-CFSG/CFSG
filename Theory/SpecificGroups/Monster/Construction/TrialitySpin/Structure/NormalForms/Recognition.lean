module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.NormalForms.Coordinates
/-!
# Recognition and cardinality from the triality collection argument

Every generator of `Q1` fixes the first coordinate's Golay projection. On a
normal-form word this projection is the affine map `a ↦ ᾱ(a + e.code)`, so
membership forces `e.code = 0` and `ᾱ = 1`. The converse requires only the
remaining generator fact `z2N ∈ Q1`. Thus, once words cover `N1`, `Q1` is the
kernel of its action on the first-coordinate code and is normal in `N1`.

The same two explicit inputs give an actual equivalence between `Q1` and
`ParkerLoop × ParkerBit × Cocode`, whose cardinality is `2^26`. The concrete
`k1` formula and the code action of `k2` and `k3` give `Q1 ⊓ K = K1`.
All conditional results retain these inputs in their statements. They do not
assert that the source collection theorem or unquotiented extraspeciality has
been established.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.3 and Lemma 14.4(1,4,5),
printed pp. 60–62. Products follow Lean's left-composition convention.
-/

@[expose] public section
open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin

def firstCode (x : Triple) : Option golay := x.1.map Prod.fst

theorem Q1_fixes_firstCode {g : N} (hg : g ∈ Q1) (x : Triple) :
    firstCode (g.val x) = firstCode x := by
  induction hg using Subgroup.closure_induction generalizing x with
  | mem g hg =>
    rcases hg with ⟨d,rfl⟩ | ⟨e,he,hg⟩
    · rcases x with ⟨a,b,c⟩
      change firstCode (psi1 d (a,b,c)) = _
      cases a <;> simp [firstCode, normalForm_sandwich, parkerSign]
    · rw [hg]
      rcases x with ⟨a,b,c⟩
      by_cases hpar : e parkerOmega = parkerOmega <;>
        cases a <;>
        simp [firstCode, psiAut1, hpar, diagonal, flip1, he.2, loopInverse, parkerSign]
  | one => rfl
  | mul g h _ _ ihg ihh => exact (ihg (h.val x)).trans (ihh x)
  | inv g _ ih =>
    have ht := ih (g.val.symm x)
    simpa only [Subgroup.coe_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using ht.symm

theorem normalForm_firstCode (d e : ParkerLoop) (α : ParkerStandardGroup) (x : Triple) :
    firstCode ((normalForm d e α).val.val x) =
      (firstCode x).map (fun a => parkerCodeEquiv (parkerStandardProjection α) (a + e.1)) := by
  rcases x with ⟨a,b,c⟩
  by_cases ha : α.val parkerOmega = parkerOmega <;> cases a <;>
    simp [firstCode, normalForm, psiAut1N, psi1N, psi2N, psiAut1, ha, diagonal,
      flip1, parkerStandardProjection_spec, loopInverse,
      parkerSign, parkerLoopMultiply, parkerMultiply]
  all_goals rw [add_comm (parkerCodeEquiv (parkerStandardProjection α) d.1),
    add_assoc, parkerGolay_add_self, add_zero]

theorem normalForm_parameters_of_firstCode (d e : ParkerLoop) (α : ParkerStandardGroup)
    (hg : ∀ x, firstCode ((normalForm d e α).val.val x) = firstCode x) :
    e.1 = 0 ∧ parkerStandardProjection α = 1 := by
  have hc (a : golay) : parkerCodeEquiv (parkerStandardProjection α) (a + e.1) = a := by
    have ht := hg (axis1 (a,0))
    rw [normalForm_firstCode] at ht
    exact Option.some.inj ht
  have he : e.1 = 0 := by
    apply (parkerCodeEquiv (parkerStandardProjection α)).injective
    simpa only [zero_add, map_zero] using hc 0
  refine ⟨he, parkerCodeEquiv_faithful _ 1 ?_⟩
  intro a
  simpa only [he, add_zero, parkerCodeEquiv_one] using hc a

theorem normalForm_Q1_parameters (d e : ParkerLoop) (α : ParkerStandardGroup)
    (hg : (normalForm d e α).val ∈ Q1) :
    e.1 = 0 ∧ parkerStandardProjection α = 1 :=
  normalForm_parameters_of_firstCode d e α (Q1_fixes_firstCode hg)

theorem normalForm_mem_Q1_of_parameters (hz2 : z2N ∈ Q1)
    (d e : ParkerLoop) (α : ParkerStandardGroup)
    (he : e.1 = 0) (hα : parkerStandardProjection α = 1) :
    (normalForm d e α).val ∈ Q1 := by
  have he' : psi2N e ∈ Q1 := by
    have hs : ∀ t : ParkerBit, t = 0 ∨ t = 1 := by decide
    have hh : e = (0,e.2) := Prod.ext he rfl
    rw [hh]
    rcases hs e.2 with ht | ht
    · rw [ht]
      have h0 : psi2N (0,0) = 1 := by
        apply Subtype.ext
        ext ⟨a,b,c⟩ : 1
        change psi2 loopOne (a,b,c) = (a,b,c)
        simp
      rw [h0]
      exact Q1.one_mem
    · rw [ht]
      exact hz2
  apply Q1.mul_mem
  · apply Q1.mul_mem
    · apply Subgroup.subset_closure
      exact Or.inr ⟨α.val,(parkerStandardProjection_eq_one_iff α).mp hα,rfl⟩
    · exact he'
  · exact Subgroup.subset_closure (Or.inl ⟨d,rfl⟩)

theorem normalForm_mem_Q1_iff_of_z2 (hz2 : z2N ∈ Q1)
    (d e : ParkerLoop) (α : ParkerStandardGroup) :
    (normalForm d e α).val ∈ Q1 ↔ e.1 = 0 ∧ parkerStandardProjection α = 1 :=
  ⟨normalForm_Q1_parameters d e α,
    fun ⟨he,hα⟩ => normalForm_mem_Q1_of_parameters hz2 d e α he hα⟩

theorem q1Word_mem_Q1_of_z2 (hz2 : z2N ∈ Q1)
    (d : ParkerLoop) (t : ParkerBit) (c : Cocode) : (q1Word d t c).val ∈ Q1 :=
  normalForm_mem_Q1_of_parameters hz2 d (0,t) (parkerCocodeStandard c)
    rfl (parkerCocodeStandard_projection c)


theorem mem_Q1_iff_firstCode_of_collection
    (hs : Function.Surjective
      (fun x : ParkerLoop × ParkerLoop × ParkerStandardGroup => normalForm x.1 x.2.1 x.2.2))
    (hz2 : z2N ∈ Q1) (g : N) (hg : g ∈ N1) :
    g ∈ Q1 ↔ ∀ x, firstCode (g.val x) = firstCode x := by
  constructor
  · exact Q1_fixes_firstCode
  · intro hc
    obtain ⟨⟨d,e,α⟩,hw⟩ := hs ⟨g,hg⟩
    have hv : (normalForm d e α).val = g := congrArg Subtype.val hw
    rw [← hv] at hc ⊢
    obtain ⟨he,hα⟩ := normalForm_parameters_of_firstCode d e α hc
    exact normalForm_mem_Q1_of_parameters hz2 d e α he hα

theorem N1_firstCode_congr_of_collection
    (hs : Function.Surjective
      (fun x : ParkerLoop × ParkerLoop × ParkerStandardGroup => normalForm x.1 x.2.1 x.2.2))
    (g : N1) {x y : Triple} (hxy : firstCode x = firstCode y) :
    firstCode (g.val.val x) = firstCode (g.val.val y) := by
  obtain ⟨⟨d,e,α⟩,rfl⟩ := hs g
  rw [normalForm_firstCode,normalForm_firstCode,hxy]

theorem Q1_normal_in_N1_of_collection
    (hs : Function.Surjective
      (fun x : ParkerLoop × ParkerLoop × ParkerStandardGroup => normalForm x.1 x.2.1 x.2.2))
    (hz2 : z2N ∈ Q1) : (Q1.subgroupOf N1).Normal := by
  constructor
  intro q hq g
  apply (mem_Q1_iff_firstCode_of_collection hs hz2
    (g.val * q.val * g.val⁻¹) (g * q * g⁻¹).prop).mpr
  intro x
  change firstCode (g.val.val (q.val.val (g.val.val.symm x))) = firstCode x
  calc
    _ = firstCode (g.val.val (g.val.val.symm x)) :=
      N1_firstCode_congr_of_collection hs g (Q1_fixes_firstCode hq _)
    _ = firstCode x := by rw [Equiv.apply_symm_apply]


theorem k1_eq_z2_mul_psi1_omega : k1 = z2N * psi1N parkerOmega := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change k1.val (a,b,c) = z2 (psi1 parkerOmega (a,b,c))
  simp [k1_apply]

theorem K1_le_Q1_of_z2 (hz2 : z2N ∈ Q1) : K1 ≤ Q1 := by
  apply Subgroup.zpowers_le.mpr
  rw [k1_eq_z2_mul_psi1_omega]
  exact Q1.mul_mem hz2 (Subgroup.subset_closure (Or.inl ⟨parkerOmega,rfl⟩))

theorem k2_not_mem_Q1 : k2 ∉ Q1 := by
  intro hk
  have ht := Q1_fixes_firstCode hk (axis1 loopOne)
  have hh : golayOne = 0 := by
    simpa [firstCode, axis1, k2_apply, loopOne, parkerSign, parkerOmega,
      parkerLoopMultiply_one_left] using ht
  exact golayOne_ne_zero hh

theorem k3_not_mem_Q1 : k3 ∉ Q1 := by
  intro hk
  have ht := Q1_fixes_firstCode hk (axis1 loopOne)
  have hh : golayOne = 0 := by
    simpa [firstCode, axis1, k3_apply, loopOne, parkerOmega,
      parkerLoopMultiply_one_left] using ht
  exact golayOne_ne_zero hh

theorem Q1_inf_K_le_K1 : Q1 ⊓ K ≤ K1 := by
  intro g hg
  rcases (mem_K_iff g).mp hg.2 with rfl | rfl | rfl | rfl
  · exact K1.one_mem
  · exact Subgroup.mem_zpowers _
  · exact (k2_not_mem_Q1 hg.1).elim
  · exact (k3_not_mem_Q1 hg.1).elim

theorem Q1_inf_K_eq_K1_of_z2 (hz2 : z2N ∈ Q1) : Q1 ⊓ K = K1 :=
  le_antisymm Q1_inf_K_le_K1 (le_inf (K1_le_Q1_of_z2 hz2) K1_le_K)

/-- The actual specialized word as an element of `Q1`, once `z2N ∈ Q1` is proved. -/
def q1ParamOfZ2 (hz2 : z2N ∈ Q1) (x : ParkerLoop × ParkerBit × Cocode) : Q1 :=
  ⟨(q1Word x.1 x.2.1 x.2.2).val, q1Word_mem_Q1_of_z2 hz2 _ _ _⟩

theorem q1ParamOfZ2_injective (hz2 : z2N ∈ Q1) :
    Function.Injective (q1ParamOfZ2 hz2) := by
  intro x y h
  apply q1Word_injective
  apply Subtype.ext
  simpa only [q1ParamOfZ2] using congrArg (fun z : Q1 => z.val) h

theorem q1ParamOfZ2_surjective
    (hs : Function.Surjective
      (fun x : ParkerLoop × ParkerLoop × ParkerStandardGroup => normalForm x.1 x.2.1 x.2.2))
    (hz2 : z2N ∈ Q1) : Function.Surjective (q1ParamOfZ2 hz2) := by
  intro g
  obtain ⟨⟨d,e,α⟩,hw⟩ := hs ⟨g.val,Q1_le_N1 g.prop⟩
  have hv : (normalForm d e α).val = g.val := congrArg Subtype.val hw
  obtain ⟨he,hα⟩ := normalForm_Q1_parameters d e α (hv ▸ g.prop)
  obtain ⟨c,hc⟩ := parkerCocodeKernelHom_surjective ⟨α,hα⟩
  have hα' : parkerCocodeStandard c.toAdd = α := congrArg Subtype.val hc
  have he' : ((0 : golay),e.2) = e := Prod.ext he.symm rfl
  refine ⟨(d,e.2,c.toAdd),?_⟩
  apply Subtype.ext
  change (normalForm d (0,e.2) (parkerCocodeStandard c.toAdd)).val = g.val
  rw [he',hα']
  exact hv

/-- A genuine equivalence with the source word map, conditional only on the
remaining collection and sign-generator results. -/
def q1WordEquivOfCollection
    (hs : Function.Surjective
      (fun x : ParkerLoop × ParkerLoop × ParkerStandardGroup => normalForm x.1 x.2.1 x.2.2))
    (hz2 : z2N ∈ Q1) : (ParkerLoop × ParkerBit × Cocode) ≃ Q1 :=
  Equiv.ofBijective (q1ParamOfZ2 hz2)
    ⟨q1ParamOfZ2_injective hz2,q1ParamOfZ2_surjective hs hz2⟩

theorem Q1_card_of_collection
    (hs : Function.Surjective
      (fun x : ParkerLoop × ParkerLoop × ParkerStandardGroup => normalForm x.1 x.2.1 x.2.2))
    (hz2 : z2N ∈ Q1) : Nat.card Q1 = 2 ^ 26 := by
  rw [← Nat.card_congr (q1WordEquivOfCollection hs hz2),
    Nat.card_prod ParkerLoop (ParkerBit × Cocode), Nat.card_prod ParkerBit Cocode,
    parkerLoop_card, cocode_card]
  norm_num [ParkerBit]

end Sporadic.Monster.Construction.TrialitySpin

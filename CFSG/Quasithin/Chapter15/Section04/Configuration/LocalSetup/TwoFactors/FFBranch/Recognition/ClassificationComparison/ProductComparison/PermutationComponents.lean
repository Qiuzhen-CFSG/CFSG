module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.Obstruction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.GoldschmidtAlternatives.Cases
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.GeneralizedFitting.AutomorphismSimple
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.Mathieu.M12.A5Fixer.Automorphisms.OuterIndex
public import Theory.Mathieu.M12.Properties.AutCover
public import Theory.Mathieu.M12.Properties.Simplicity

/-!
# Permutation, covering and Mathieu rows of F.6.18

The concrete rows in F.6.18(6)--(9), (12) and (13) carry enough actual group
structure to identify a quasisimple normal subgroup of the ambient group.  For
an alternating model this is the whole group.  For a symmetric or triple
symmetric model it is the inverse image of the alternating subgroup under the
literal permutation quotient; the sign quotient is an actual two-group.  The
Mathieu row uses the actual inner automorphism subgroup and its checked outer
index bound.  In every case the two-core hypothesis then identifies this
normal subgroup with the generalized Fitting subgroup.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
F.6.18, pp.309--310, and 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace ProductComparison
open GoldschmidtAlternatives

universe u v

private theorem alternating_quasisimple {n : ℕ} (hn : 5 ≤ n) :
    IsQuasisimple (alternatingGroup (Fin n)) := by
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
  refine {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simpa using hn)⟩
    simple := ?_ }
  have hn4 : 4 ≤ Nat.card (Fin n) := by simpa using (show 4 ≤ n by omega)
  exact ((QuotientGroup.quotientMulEquivOfEq
    (alternatingGroup.center_eq_bot hn4)).trans QuotientGroup.quotientBot).isSimpleGroup

private theorem fitting_of_whole_quasisimple
    {D : Type u} [Group D] [Finite D]
    (hD : IsQuasisimple D) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  let : IsQuasisimple (⊤ : Subgroup D) := IsQuasisimple.of_mulEquiv topEquiv.symm
  let : Subsingleton (D ⧸ (⊤ : Subgroup D)) := QuotientGroup.subsingleton_quotient_top
  have hfit := generalizedFitting_eq_of_quasisimple_two_quotient
    (⊤ : Subgroup D) (IsPGroup.of_subsingleton 2 _) hcore
  rw [hfit]
  infer_instance

private theorem fitting_of_normal_quasisimple
    {D : Type u} [Group D] [Finite D] (L : Subgroup D) [L.Normal]
    (hL : IsQuasisimple L) (hquot : IsPGroup 2 (D ⧸ L))
    (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  let : IsQuasisimple L := hL
  have hfit := generalizedFitting_eq_of_quasisimple_two_quotient L hquot hcore
  rw [hfit]
  infer_instance

private theorem sign_quotient_isTwo
    {D : Type u} [Group D] {n : ℕ}
    (hn : 5 ≤ n) (f : D →* Equiv.Perm (Fin n)) (hf : Function.Surjective f)
    (A : Subgroup D) [A.Normal]
    (hA : A = (alternatingGroup (Fin n)).comap f) :
    IsPGroup 2 (D ⧸ A) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let s : D →* ℤˣ := (Equiv.Perm.sign : Equiv.Perm (Fin n) →* ℤˣ).comp f
  have hs : Function.Surjective s := (Equiv.Perm.sign_surjective (Fin n)).comp hf
  have hk : s.ker = A := by
    ext x
    change Equiv.Perm.sign (f x) = 1 ↔ x ∈ A
    rw [hA]
    change Equiv.Perm.sign (f x) = 1 ↔ f x ∈ alternatingGroup (Fin n)
    rw [Equiv.Perm.mem_alternatingGroup]
  have hunits : IsPGroup 2 ℤˣ := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
    norm_num
  have hq : IsPGroup 2 (D ⧸ s.ker) := hunits.of_surjective
    (QuotientGroup.quotientKerEquivOfSurjective s hs).symm.toMonoidHom
    (QuotientGroup.quotientKerEquivOfSurjective s hs).symm.surjective
  exact hq.of_surjective (QuotientGroup.quotientMulEquivOfEq hk).toMonoidHom
    (QuotientGroup.quotientMulEquivOfEq hk).surjective

private theorem symmetric_fitting
    {D : Type u} [Group D] [Finite D] {n : ℕ}
    (hn : 5 ≤ n) (e : D ≃* Equiv.Perm (Fin n))
    (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  let A : Subgroup D := (alternatingGroup (Fin n)).comap e.toMonoidHom
  let : A.Normal := (alternatingGroup.normal.comap e.toMonoidHom)
  let hmap : A.map e.toMonoidHom = alternatingGroup (Fin n) :=
    map_comap_eq_self_of_surjective e.surjective _
  let eA : A ≃* alternatingGroup (Fin n) :=
    (e.subgroupMap A).trans (MulEquiv.subgroupCongr hmap)
  have hA : IsQuasisimple A := by
    let : IsQuasisimple (alternatingGroup (Fin n)) := alternating_quasisimple hn
    exact IsQuasisimple.of_mulEquiv eA.symm
  have hquot : IsPGroup 2 (D ⧸ A) := sign_quotient_isTwo hn e.toMonoidHom e.surjective A rfl
  exact fitting_of_normal_quasisimple A hA hquot hcore

/-- A concrete alternating model has quasisimple generalized Fitting subgroup. -/
theorem alternating_quasisimple_fitting
    {D : Type u} [Group D] [Finite D] {n : ℕ}
    (hn : 5 ≤ n) (e : D ≃* alternatingGroup (Fin n))
    (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  let : IsQuasisimple (alternatingGroup (Fin n)) := alternating_quasisimple hn
  exact fitting_of_whole_quasisimple (IsQuasisimple.of_mulEquiv e.symm) hcore

/-- A concrete symmetric model has quasisimple generalized Fitting subgroup;
the component is the actual alternating preimage. -/
theorem symmetric_quasisimple_fitting
    {D : Type u} [Group D] [Finite D] {n : ℕ}
    (hn : 5 ≤ n) (e : D ≃* Equiv.Perm (Fin n))
    (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) :=
  symmetric_fitting hn e hcore

private theorem triple_symmetric_preimage_quasisimple
    {D : Type u} [Group D] [Finite D] {n : ℕ}
    (hn : 5 ≤ n) (f : D →* Equiv.Perm (Fin n)) (hf : Function.Surjective f)
    (_hker : Nonempty (f.ker ≃* Multiplicative (ZMod 3)))
    (hperf : Group.IsPerfect ((alternatingGroup (Fin n)).comap f))
    (hconj : ∀ g : D, ∀ z : f.ker,
      g * z.val * g⁻¹ = if Equiv.Perm.sign (f g) = 1 then z.val else z.val⁻¹)
    (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  let A : Subgroup D := (alternatingGroup (Fin n)).comap f
  let : A.Normal := (alternatingGroup.normal.comap f)
  let q : A →* alternatingGroup (Fin n) := {
    toFun := fun x => ⟨f x, x.property⟩
    map_one' := by ext; simp
    map_mul' := by intro x y; ext; simp }
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨g, hg⟩ := hf a.val
    refine ⟨⟨g, ?_⟩, ?_⟩
    · change f g ∈ alternatingGroup (Fin n)
      rw [hg]
      exact a.property
    · apply Subtype.ext
      exact hg
  have hker_center : q.ker ≤ center A := by
    intro z hz
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    let zz : f.ker := ⟨z.1, by
      change q z = 1 at hz
      exact Subtype.ext_iff.mp hz⟩
    have hs : Equiv.Perm.sign (f (x : D)) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mpr x.property
    have hc : (x : D) * (z : D) * (x : D)⁻¹ = (z : D) := by
      simpa [hs] using hconj (x : D) zz
    change (x : D) * (z : D) = (z : D) * (x : D)
    calc
      (x : D) * (z : D) = ((x : D) * (z : D) * (x : D)⁻¹) * (x : D) := by simp [mul_assoc]
      _ = (z : D) * (x : D) := by rw [hc]
  let : Group.IsPerfect A := hperf
  let : IsQuasisimple (alternatingGroup (Fin n)) := alternating_quasisimple hn
  let c : PerfectCentralCovering.Cover A (alternatingGroup (Fin n)) := {
    toMonoidHom := q
    surjective := hq
    isPerfect := hperf
    ker_le_center := hker_center }
  have hA : IsQuasisimple A := c.isQuasisimple
  have hquot : IsPGroup 2 (D ⧸ A) := sign_quotient_isTwo hn f hf A rfl
  exact fitting_of_normal_quasisimple A hA hquot hcore

/-- A triple alternating cover in row (6) or (7) has quasisimple F*. -/
theorem triple_alternating_quasisimple_fitting
    {D : Type u} [Group D] [Finite D] {n : ℕ}
    (h : TripleAlternating D n) (hn : 5 ≤ n)
    (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨hperf, _, hquot⟩ := h
  obtain ⟨e⟩ := hquot
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
  have hD : IsQuasisimple D := {
    toIsPerfect := hperf
    simple := e.isSimpleGroup }
  exact fitting_of_whole_quasisimple hD hcore

/-- A triple symmetric cover in row (8) or (9) has quasisimple F*. -/
theorem triple_symmetric_quasisimple_fitting
    {D : Type u} [Group D] [Finite D] {n : ℕ}
    (h : TripleSymmetric D n) (hn : 5 ≤ n)
    (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨f, hf, hker, hperf, hconj⟩ := h
  exact triple_symmetric_preimage_quasisimple hn f hf hker hperf hconj hcore

private theorem m12_perfect : Group.IsPerfect Sporadic.Mathieu.M12 := by
  let : IsSimpleGroup Sporadic.Mathieu.M12 := Sporadic.Mathieu.m12_isSimpleGroup
  have hnoncomm : ¬ IsMulCommutative Sporadic.Mathieu.M12 := by
    intro hc
    let : IsMulCommutative Sporadic.Mathieu.M12 := hc
    have hp := (Group.is_simple_iff_prime_card (α := Sporadic.Mathieu.M12)).mp
      Sporadic.Mathieu.m12_isSimpleGroup
    rw [Sporadic.Mathieu.m12_order] at hp
    norm_num at hp
  have hne : _root_.commutator Sporadic.Mathieu.M12 ≠ ⊥ := by
    intro h
    exact hnoncomm ((commutator_eq_bot_iff Sporadic.Mathieu.M12).mp h)
  exact ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_left hne⟩

private theorem m12_quasisimple : IsQuasisimple Sporadic.Mathieu.M12 := by
  let : IsSimpleGroup Sporadic.Mathieu.M12 := Sporadic.Mathieu.m12_isSimpleGroup
  exact {
    toIsPerfect := m12_perfect
    simple := ((QuotientGroup.quotientMulEquivOfEq Sporadic.Mathieu.m12_center_eq_bot).trans
      QuotientGroup.quotientBot).isSimpleGroup }

private theorem aut_m12_quotient_isTwo :
    IsPGroup 2 (MulAut Sporadic.Mathieu.M12 ⧸
      MulAut.innerSubgroup Sporadic.Mathieu.M12) := by
  have hi : (MulAut.innerSubgroup Sporadic.Mathieu.M12).index ≤ 2 := by
    exact Sporadic.Mathieu.M12A5Fixer.Automorphisms.outerIndexBound
  have hpos : 0 < (MulAut.innerSubgroup Sporadic.Mathieu.M12).index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos
  have hc : (MulAut.innerSubgroup Sporadic.Mathieu.M12).index = 1 ∨
      (MulAut.innerSubgroup Sporadic.Mathieu.M12).index = 2 := by omega
  rcases hc with h1 | h2
  · have ht : MulAut.innerSubgroup Sporadic.Mathieu.M12 = ⊤ :=
      index_eq_one.mp h1
    let : Subsingleton (MulAut Sporadic.Mathieu.M12 ⧸ (⊤ : Subgroup (MulAut Sporadic.Mathieu.M12))) :=
      QuotientGroup.subsingleton_quotient_top
    let : Subsingleton (MulAut Sporadic.Mathieu.M12 ⧸
        MulAut.innerSubgroup Sporadic.Mathieu.M12) :=
      (QuotientGroup.quotientMulEquivOfEq ht).injective.subsingleton
    exact IsPGroup.of_subsingleton 2 _
  · apply IsPGroup.of_card (n := 1)
    rw [← Subgroup.index_eq_card, h2]
    norm_num

/-- The M₁₂ row has quasisimple generalized Fitting subgroup. -/
theorem m12_quasisimple_fitting
    {D : Type u} [Group D] [Finite D]
    (e : Nonempty (D ≃* Sporadic.Mathieu.M12)) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨e⟩ := e
  let : IsQuasisimple Sporadic.Mathieu.M12 := m12_quasisimple
  exact fitting_of_whole_quasisimple (IsQuasisimple.of_mulEquiv e.symm) hcore

/-- The full automorphism row has quasisimple generalized Fitting subgroup;
the normal subgroup is the literal inner automorphism subgroup. -/
theorem aut_m12_quasisimple_fitting
    {D : Type u} [Group D] [Finite D]
    (e : Nonempty (D ≃* MulAut Sporadic.Mathieu.M12)) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨e⟩ := e
  let : IsQuasisimple Sporadic.Mathieu.M12 := m12_quasisimple
  let i : Sporadic.Mathieu.M12 ≃* MulAut.innerSubgroup Sporadic.Mathieu.M12 :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot
      Sporadic.Mathieu.m12_center_eq_bot)
  let : IsQuasisimple (MulAut.innerSubgroup Sporadic.Mathieu.M12) :=
    IsQuasisimple.of_mulEquiv i
  let L : Subgroup D := (MulAut.innerSubgroup Sporadic.Mathieu.M12).comap e.toMonoidHom
  let : L.Normal := (MulAut.innerSubgroup_normal _).comap e.toMonoidHom
  let hmap : L.map e.toMonoidHom = MulAut.innerSubgroup Sporadic.Mathieu.M12 :=
    map_comap_eq_self_of_surjective e.surjective _
  let eL : L ≃* MulAut.innerSubgroup Sporadic.Mathieu.M12 :=
    (e.subgroupMap L).trans (MulEquiv.subgroupCongr hmap)
  have hL : IsQuasisimple L := IsQuasisimple.of_mulEquiv eL.symm
  let q : D →* (MulAut Sporadic.Mathieu.M12 ⧸
      MulAut.innerSubgroup Sporadic.Mathieu.M12) :=
    (QuotientGroup.mk' (MulAut.innerSubgroup Sporadic.Mathieu.M12)).comp e.toMonoidHom
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp e.surjective
  have hk : q.ker = L := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hquot' : IsPGroup 2 (D ⧸ q.ker) :=
    aut_m12_quotient_isTwo.of_surjective
      (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.surjective
  have hquot : IsPGroup 2 (D ⧸ L) :=
    hquot'.of_surjective (QuotientGroup.quotientMulEquivOfEq hk).toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hk).surjective
  exact fitting_of_normal_quasisimple L hL hquot hcore

/-- The literal F.6.18 row (6) triple cover has quasisimple F*. -/
theorem triple_alternating_six_quasisimple_fitting
    {D : Type u} [Group D] [Finite D]
    (h : TripleAlternating D 6) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) :=
  triple_alternating_quasisimple_fitting h (by decide) hcore

/-- The literal F.6.18 row (7) alternating model has quasisimple F*. -/
theorem alternating_seven_quasisimple_fitting
    {D : Type u} [Group D] [Finite D]
    (e : Nonempty (D ≃* alternatingGroup (Fin 7))) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨e⟩ := e
  exact alternating_quasisimple_fitting (by decide) e hcore

/-- The literal F.6.18 row (7) triple cover has quasisimple F*. -/
theorem triple_alternating_seven_quasisimple_fitting
    {D : Type u} [Group D] [Finite D]
    (h : TripleAlternating D 7) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) :=
  triple_alternating_quasisimple_fitting h (by decide) hcore

/-- The literal F.6.18 row (8) triple symmetric cover has quasisimple F*. -/
theorem triple_symmetric_six_quasisimple_fitting
    {D : Type u} [Group D] [Finite D]
    (h : TripleSymmetric D 6) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) :=
  triple_symmetric_quasisimple_fitting h (by decide) hcore

/-- The literal F.6.18 row (9) symmetric model has quasisimple F*. -/
theorem symmetric_seven_quasisimple_fitting
    {D : Type u} [Group D] [Finite D]
    (e : Nonempty (D ≃* Equiv.Perm (Fin 7))) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨e⟩ := e
  exact symmetric_quasisimple_fitting (by decide) e hcore

/-- The literal F.6.18 row (9) triple symmetric cover has quasisimple F*. -/
theorem triple_symmetric_seven_quasisimple_fitting
    {D : Type u} [Group D] [Finite D]
    (h : TripleSymmetric D 7) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) :=
  triple_symmetric_quasisimple_fitting h (by decide) hcore

/-- A checked `ClassifiedAction` cannot coexist with one of the assigned
permutation/covering/Mathieu model rows in a product branch: the model proves
quasisimplicity of the ambient F*, while the literal branch obstruction proves
its negation. -/
theorem classifiedAction_model_contradiction
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {K : GroupClass.{u}} {ρ : Representation (ZMod 2) D V}
    {G₁ G₂ : Subgroup D}
    (_h : ClassifiedAction K ρ G₁ G₂)
    (hb : Branch (ρ.comp (offenderSubgroup ρ).subtype))
    (hm : IsQuasisimple (generalizedFitting D)) : False := by
  exact (branch_not_quasisimple ρ hb) hm

/-- The row (6) covering model discharges the branch obstruction through the
actual `ClassifiedAction` two-core hypothesis. -/
theorem classifiedAction_triple_alternating_six_contradiction
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {K : GroupClass.{u}} {ρ : Representation (ZMod 2) D V}
    {G₁ G₂ : Subgroup D}
    (h : ClassifiedAction K ρ G₁ G₂)
    (hb : Branch (ρ.comp (offenderSubgroup ρ).subtype))
    (hm : TripleAlternating D 6) : False := by
  exact classifiedAction_model_contradiction h hb
    (triple_alternating_six_quasisimple_fitting hm h.twoCore)

end ProductComparison
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

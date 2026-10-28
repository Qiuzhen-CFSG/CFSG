module
public import Theory.SpecificGroups.AlternatingSix.TripleCoverComparison
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.InvariantMaximalGeneration
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Six-coset markings in triple covers of A₆

The coset action of an A₅ times the central cubic identifies the central
quotient with A₆, while retaining the actual stabilizer of the base coset.
A comparison in natural S₆ coordinates can therefore be adjusted by an
inner automorphism to align these stabilizers. Taking derived subgroups
recovers the original A₅ subgroups, removing the central saturation.

The source and ATLAS vertex normalizers use this to align their literal
pointwise edge fixers. No ambient group recognition is assumed.
Source: Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267.
-/

public section
open Subgroup
namespace AlternatingSix.TripleCoverMarking
variable {L : Type*} [Group L] [Finite L]

/-- Six cosets give coordinates preserving their actual base stabilizer. -/
theorem coordinates (Z U : Subgroup L) [Z.Normal]
    (hcore : U.normalCore = Z) (hi : U.index = 6)
    (hquot : Nat.card (L ⧸ Z) = 360) :
    ∃ (e : (L ⧸ Z) ≃* alternatingGroup (Fin 6)) (i : Fin 6),
      ∀ x : L, x ∈ U ↔ (e (QuotientGroup.mk' Z x)).val i = i := by
  let a := MulAction.toPermHom L (L ⧸ U)
  let b := Finite.equivFinOfCardEq hi
  let f : L →* Equiv.Perm (Fin 6) := b.permCongrHom.toMonoidHom.comp a
  have hk : f.ker = Z := by
    have hf : f.ker = a.ker := by
      ext x
      change b.permCongrHom (a x) = 1 ↔ a x = 1
      exact b.permCongrHom.map_eq_one_iff
    rw [hf, ← normalCore_eq_ker, hcore]
  let eR : (L ⧸ Z) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have hr : Nat.card f.range = 360 := (Nat.card_congr eR.toEquiv).symm.trans hquot
  have hind : f.range.index = 2 := by
    have h := f.range.index_mul_card
    rw [hr, Nat.card_perm, Nat.card_fin] at h
    norm_num [Nat.factorial] at h
    omega
  let e := eR.trans (MulEquiv.subgroupCongr
    (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hind))
  refine ⟨e, b (QuotientGroup.mk (1 : L)), fun x => ?_⟩
  have he : (e (QuotientGroup.mk' Z x)).val = f x := by
    simp only [e, eR, MulEquiv.trans_apply, QuotientGroup.mk'_apply,
      QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  rw [he]
  change x ∈ U ↔ b (x • b.symm (b (QuotientGroup.mk (1 : L)))) = b (QuotientGroup.mk (1 : L))
  rw [b.symm_apply_apply]
  change x ∈ U ↔ b (QuotientGroup.mk (x * 1)) = b (QuotientGroup.mk (1 : L))
  rw [b.injective.eq_iff, mul_one]
  simp only [QuotientGroup.eq, mul_one, inv_mem_iff]

omit [Finite L] in
/-- A perfect subgroup is recovered from its product with the centre. -/
theorem derived_saturation (F : Subgroup L) [Group.IsPerfect F] :
    ⁅F ⊔ center L, F ⊔ center L⁆ = F := by
  rw [commutator_eq_of_central_supplement rfl (center_le_centralizer _),
    F.commutator_eq_self]

/-- An A₅ inside a triple cover of A₆ determines six-point quotient
coordinates in which its central saturation is a point stabilizer. -/
theorem five_coordinates [Theory.GroupTheory.IsQuasisimple L]
    (hZ : Nat.card (center L) = 3) (hQ : Nat.card (L ⧸ center L) = 360)
    (F : Subgroup L) (eF : F ≃* alternatingGroup (Fin 5)) :
    ∃ (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6)) (i : Fin 6),
      ∀ x : L, x ∈ F ⊔ center L ↔
        (e (QuotientGroup.mk' (center L) x)).val i = i := by
  have hF : Nat.card F = 60 := by
    rw [Nat.card_congr eF.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hd : Disjoint F (center L) := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    rintro x ⟨hx, hz⟩
    have hc : (⟨x, hx⟩ : F) ∈ center F := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_center_iff.mp hz y)
    have he : eF ⟨x, hx⟩ ∈ center (alternatingGroup (Fin 5)) :=
      (MulEquivClass.apply_mem_center_iff eF).mpr hc
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
    exact congrArg Subtype.val (eF.map_eq_one_iff.mp he)
  let U := F ⊔ center L
  have hU : Nat.card U = 180 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((center_le_centralizer _).trans (centralizer_le_normalizer _)) hd, hF, hZ]
  have hL : Nat.card L = 1080 := by
    have h := (center L).index_mul_card
    change Nat.card (L ⧸ center L) * Nat.card (center L) = _ at h
    rw [hQ, hZ] at h
    exact h.symm
  have hi : U.index = 6 := by
    have h := U.index_mul_card
    rw [hU, hL] at h
    omega
  have hcore : U.normalCore = center L := by
    apply le_antisymm
    · rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top U.normalCore with h | h
      · exact h
      · have ht := top_unique (h ▸ U.normalCore_le)
        rw [ht, card_top, hL] at hU
        omega
    · exact normal_le_normalCore.mpr le_sup_right
  exact coordinates (center L) U hcore hi hQ

omit [Finite L] in
/-- A cover comparison in natural six-point coordinates can be adjusted
by a target inner automorphism to carry the two marked perfect subgroups. -/
theorem align {R : Type*} [Group R]
    (F : Subgroup L) (E : Subgroup R) [Group.IsPerfect F] [Group.IsPerfect E]
    (f : L →* alternatingGroup (Fin 6)) (g : R →* alternatingGroup (Fin 6))
    (hg : Function.Surjective g) (i j : Fin 6)
    (hfmark : ∀ x, x ∈ F ⊔ center L ↔ (f x).val i = i)
    (hgmark : ∀ y, y ∈ E ⊔ center R ↔ (g y).val j = j)
    (a : L ≃* R) (k : MulAut (alternatingGroup (Fin 6)))
    (hk : k ∈ AlternatingSix.ShadowLocal.natural)
    (ha : ∀ x, g (a x) = k (f x)) :
    ∃ t : R, F.map (a.trans (MulAut.conj t)).toMonoidHom = E := by
  obtain ⟨σ, rfl⟩ := hk
  let : MulAction.IsPretransitive (alternatingGroup (Fin 6)) (Fin 6) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 6) (by simp)
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) (σ i) j
  obtain ⟨t, ht⟩ := hg q
  let d := a.trans (MulAut.conj t)
  have hmem (x : L) : x ∈ F ⊔ center L ↔ d x ∈ E ⊔ center R := by
    rw [hfmark, hgmark]
    have hd : g (d x) = q * MulAut.conjNormal σ (f x) * q⁻¹ := by
      change g (t * a x * t⁻¹) = _
      rw [map_mul, map_mul, map_inv, ht, ha]
    rw [hd]
    change (f x).val i = i ↔
      (q.val * (σ * (f x).val * σ⁻¹) * q.val⁻¹) j = j
    have hq' : q.val (σ i) = j := hq
    rw [← hq']
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply,
      q.val.injective.eq_iff, σ.injective.eq_iff]
  have hmap : (F ⊔ center L).map d.toMonoidHom = E ⊔ center R := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).mp hx
    · intro hy
      obtain ⟨x, rfl⟩ := d.surjective y
      exact ⟨x, (hmem x).mpr hy, rfl⟩
  refine ⟨t, ?_⟩
  rw [← derived_saturation F, map_commutator, hmap, derived_saturation E]

end AlternatingSix.TripleCoverMarking

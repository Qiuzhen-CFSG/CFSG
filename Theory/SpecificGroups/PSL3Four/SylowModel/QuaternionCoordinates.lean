module

public import Theory.SpecificGroups.PSL3Four.SylowModel
public import Mathlib.GroupTheory.Index
/-!
# Coordinates and centralizer of the quaternion core

The trace kernel in UT₃(F₄)⋊C₂ has two prime-field coordinates, one arbitrary
field coordinate and one field-automorphism coordinate, hence order 32.
Centralizing its two root involutions and its field involution forces precisely
the marked central involution subgroup. The two root-plane intersections have
order eight. We also choose an F₄ generator for subsequent quaternion factors.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §5.3.7,
printed pp. 660–661 (PDF pp. 677–678).
-/

@[expose] public section
namespace Matrix.PSL3Four.SylowModel
noncomputable section

theorem frobenius_fixed_iff (x : F) : fieldFrobenius x = x ↔ x = 0 ∨ x = 1 := by
  rw [fieldFrobenius_apply]
  constructor
  · intro h
    have hh : x * (x - 1) = 0 := by calc
      x * (x - 1) = x ^ 2 - x := by ring
      _ = 0 := sub_eq_zero.mpr h
    simpa only [sub_eq_zero] using mul_eq_zero.mp hh
  · rintro (rfl | rfl) <;> simp

abbrev PrimeField := {x : F // fieldFrobenius x = x}

theorem card_primeField : Nat.card PrimeField = 2 := by
  apply (Nat.card_eq_two_iff' (⟨0, by simp⟩ : PrimeField)).mpr
  refine ⟨⟨1, by simp⟩, ?_, ?_⟩
  · intro h
    exact one_ne_zero (congrArg Subtype.val h)
  · intro x hx
    apply Subtype.ext
    exact ((frobenius_fixed_iff x.val).mp x.property).resolve_left
      (fun h => hx (Subtype.ext h))

def coreCoordinates : Q ≃ PrimeField × PrimeField × F × C2 where
  toFun q := (⟨q.val.left.x, ((mem_Q _).mp q.property).1⟩,
    ⟨q.val.left.y, ((mem_Q _).mp q.property).2⟩, q.val.left.c, q.val.right)
  invFun p := ⟨⟨⟨p.1.val, p.2.1.val, p.2.2.1⟩, p.2.2.2⟩,
    (mem_Q _).mpr ⟨p.1.property, p.2.1.property⟩⟩

theorem card_Q : Nat.card Q = 32 := by
  rw [Nat.card_congr coreCoordinates, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    card_primeField, card_F, card_C2]

def corePlane₁Coordinates : (V₁ ⊓ Q : Subgroup T) ≃ PrimeField × F where
  toFun q := (⟨q.val.left.x, ((mem_Q _).mp q.property.2).1⟩, q.val.left.c)
  invFun p := ⟨⟨⟨p.1.val, 0, p.2⟩, 1⟩,
    (mem_V₁ _).mpr ⟨rfl, rfl⟩, (mem_Q _).mpr ⟨p.1.property, by simp⟩⟩
  left_inv q := by
    apply Subtype.ext
    exact SemidirectProduct.ext (U.ext rfl ((mem_V₁ _).mp q.property.1).2.symm rfl)
      ((mem_V₁ _).mp q.property.1).1.symm

def corePlane₂Coordinates : (V₂ ⊓ Q : Subgroup T) ≃ PrimeField × F where
  toFun q := (⟨q.val.left.y, ((mem_Q _).mp q.property.2).2⟩, q.val.left.c)
  invFun p := ⟨⟨⟨0, p.1.val, p.2⟩, 1⟩,
    (mem_V₂ _).mpr ⟨rfl, rfl⟩, (mem_Q _).mpr ⟨by simp, p.1.property⟩⟩
  left_inv q := by
    apply Subtype.ext
    exact SemidirectProduct.ext (U.ext ((mem_V₂ _).mp q.property.1).2.symm rfl rfl)
      ((mem_V₂ _).mp q.property.1).1.symm

theorem card_V₁_inf_Q : Nat.card (V₁ ⊓ Q : Subgroup T) = 8 := by
  rw [Nat.card_congr corePlane₁Coordinates, Nat.card_prod, card_primeField, card_F]

theorem card_V₂_inf_Q : Nat.card (V₂ ⊓ Q : Subgroup T) = 8 := by
  rw [Nat.card_congr corePlane₂Coordinates, Nat.card_prod, card_primeField, card_F]

theorem card_C : Nat.card C = 2 := by
  rw [C, Nat.card_zpowers]
  exact orderOf_eq_prime z_sq z_ne_one

def rootA : Q := ⟨inclusion ⟨1, 0, 0⟩, (mem_Q _).mpr ⟨by simp [inclusion], by simp [inclusion]⟩⟩
def rootB : Q := ⟨inclusion ⟨0, 1, 0⟩, (mem_Q _).mpr ⟨by simp [inclusion], by simp [inclusion]⟩⟩
def fieldD : Q := ⟨SemidirectProduct.inr τ, (mem_Q _).mpr ⟨by simp, by simp⟩⟩

theorem mem_C_iff (g : T) : g ∈ C ↔ g = 1 ∨ g = z := by
  have htwo := (Nat.card_eq_two_iff' (1 : C)).mp card_C
  have hz : z ∈ C := Subgroup.mem_zpowers z
  constructor
  · intro hg
    by_cases h : g = 1
    · exact Or.inl h
    · right
      obtain ⟨w, _, hw⟩ := htwo
      exact congrArg Subtype.val ((hw ⟨g,hg⟩ (fun e => h (congrArg Subtype.val e))).trans
        (hw ⟨z,hz⟩ (fun e => z_ne_one (congrArg Subtype.val e))).symm)
  · rintro (rfl | rfl)
    · exact C.one_mem
    · exact hz

theorem centralizer_Q_eq_C : Subgroup.centralizer (Q : Set T) = C := by
  apply le_antisymm
  · intro g hg
    have hs : g ∈ S := by
      rw [← centralizer_Z]
      exact fun a ha => hg a (Z_le_Q ha)
    have hr := (mem_S _).mp hs
    have hb := congrArg (fun t : T => t.left.c) (hg rootB.val rootB.property)
    have ha' := congrArg (fun t : T => t.left.c) (hg rootA.val rootA.property)
    have hx : g.left.x = 0 := by
      simpa [rootB, inclusion, hr] using hb.symm
    have hy : g.left.y = 0 := by
      simpa [rootA, inclusion, hr] using ha'
    have hd := congrArg (fun t : T => t.left.c) (hg fieldD.val fieldD.property)
    have hc : fieldFrobenius g.left.c = g.left.c := by
      simpa [fieldD, hr] using hd
    apply (mem_C_iff g).mpr
    rcases (frobenius_fixed_iff _).mp hc with hc | hc
    · left
      exact SemidirectProduct.ext (U.ext hx hy hc) hr
    · right
      exact SemidirectProduct.ext (U.ext hx hy hc) hr
  · intro g hg a _
    exact Subgroup.mem_center_iff.mp (C_le_center hg) a

theorem centralizer_Q_le_Q : Subgroup.centralizer (Q : Set T) ≤ Q := by
  rw [centralizer_Q_eq_C]
  exact C_le_Q

theorem center_Q_eq : Subgroup.center Q = C.subgroupOf Q := by
  ext q
  rw [Subgroup.mem_center_iff]
  change (∀ r : Q, r * q = q * r) ↔ q.val ∈ C
  rw [← centralizer_Q_eq_C]
  constructor
  · intro h r hr
    exact congrArg Subtype.val (h ⟨r,hr⟩)
  · intro h r
    exact Subtype.ext (h r.val r.property)

theorem card_center_Q : Nat.card (Subgroup.center Q) = 2 := by
  rw [center_Q_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe C_le_Q).toEquiv, card_C]
/-- A non-prime-field element of F₄. -/
def omega : F := Classical.choose exists_fieldFrobenius_ne

theorem omega_not_fixed : fieldFrobenius omega ≠ omega :=
  Classical.choose_spec exists_fieldFrobenius_ne

theorem omega_ne_zero : omega ≠ 0 := by
  intro h
  exact omega_not_fixed (by simp [h])

theorem omega_ne_one : omega ≠ 1 := by
  intro h
  exact omega_not_fixed (by simp [h])

theorem trace_fixed (x : F) : fieldFrobenius (trace x) = trace x := by
  simp only [trace, map_add, fieldFrobenius_involutive, add_comm]

theorem omega_frobenius : fieldFrobenius omega = omega + 1 := by
  have ht : trace omega = 1 := ((frobenius_fixed_iff _).mp (trace_fixed omega)).resolve_left
    (fun h => omega_not_fixed ((trace_eq_zero _).mp h))
  have h := congrArg (omega + ·) ht
  simpa only [trace, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] using h

theorem field_cases (x : F) : x = 0 ∨ x = 1 ∨ x = omega ∨ x = omega + 1 := by
  classical
  let := Fintype.ofFinite F
  have h10 : (1 : F) ≠ 0 := one_ne_zero
  have hw10 : omega + 1 ≠ 0 := by
    intro h
    apply omega_ne_one
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using
      congrArg (· + (1 : F)) h
  have hw11 : omega + 1 ≠ 1 := by simpa using omega_ne_zero
  have hw1w : omega + 1 ≠ omega := by simp
  have hcard : ({0,1,omega,omega+1} : Finset F).card = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, card_F]
    simp [Ne.symm omega_ne_zero, Ne.symm omega_ne_one,
      Ne.symm hw10, Ne.symm hw11, Ne.symm hw1w]
  have h := Finset.eq_univ_of_card _ hcard
  have hx : x ∈ ({0,1,omega,omega+1} : Finset F) := h ▸ Finset.mem_univ x
  simpa using hx

end
end Matrix.PSL3Four.SylowModel

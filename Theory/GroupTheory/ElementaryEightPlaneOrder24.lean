module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Index

/-!
# Order-twenty-four automorphisms preserving an elementary-eight plane

An order-twenty-four automorphism subgroup of an elementary abelian two-group
of order eight is S4 if it preserves a subgroup of order four. This supplies
the plane-stabilizer recognition for the initial local normalizer in
Stellmacher (9.1), Journal of Algebra 190 (1997), p. 48.

The automorphisms act on the four elements outside the invariant subgroup.
This action is faithful: if two automorphisms agree outside the subgroup,
choose one outside element c. For any element w inside the subgroup, wc is
outside too; agreement at c and wc implies agreement at w by cancellation.
The faithful permutation action is surjective because both groups have order
twenty-four. The private faithfulness argument works for any proper subgroup;
no additional transitivity or splitting premise is used.

The same full symmetric action proves uniqueness of the invariant plane.
If another four-element subgroup differed, there would be two points
outside the first plane with different membership in the second. The
available transposition of those points contradicts invariance. This
uniqueness supplies the distinct conjugate plane images in (8.6)(c4).
-/

private def outsideRep {U : Type*} [Group U] (W : Subgroup U)
    (A : Subgroup (MulAut U))
    (hstable : ∀ a : A, ∀ x : U, (a : MulAut U) x ∈ W ↔ x ∈ W) :
    A →* Equiv.Perm {x : U // x ∉ W} where
  toFun a := {
    toFun := fun x => ⟨a.val x.val, fun hx => x.property ((hstable a x.val).mp hx)⟩
    invFun := fun x => ⟨(a⁻¹ : A).val x.val,
      fun hx => x.property ((hstable a⁻¹ x.val).mp hx)⟩
    left_inv := by intro x; apply Subtype.ext; simp
    right_inv := by intro x; apply Subtype.ext; simp }
  map_one' := by ext x; rfl
  map_mul' := by intro a b; ext x; rfl

private theorem outsideRep_injective {U : Type*} [Group U] (W : Subgroup U)
    (c : U) (hc : c ∉ W) (A : Subgroup (MulAut U))
    (hstable : ∀ a : A, ∀ x : U, (a : MulAut U) x ∈ W ↔ x ∈ W) :
    Function.Injective (outsideRep W A hstable) := by
  intro a b hab
  have hout : ∀ x : U, x ∉ W → (a : MulAut U) x = (b : MulAut U) x := by
    intro x hx
    exact congrArg (fun p : Equiv.Perm {x : U // x ∉ W} => (p ⟨x, hx⟩).val) hab
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  by_cases hx : x ∈ W
  · have hxc : x*c ∉ W := by
      intro h
      exact hc (by simpa only [inv_mul_cancel_left] using W.mul_mem (W.inv_mem hx) h)
    have hh := hout (x*c) hxc
    rw [map_mul, map_mul, hout c hc] at hh
    exact mul_right_cancel hh
  · exact hout x hx

/-- An order-twenty-four automorphism subgroup preserving a subgroup of
order four in an elementary group of order eight is `S₄`. -/
public theorem elementaryEight_plane_order24_equiv_S4 {U : Type*} [Group U] [Finite U] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 8) (W : Subgroup U) (hW : Nat.card W = 4)
    (A : Subgroup (MulAut U)) (hA : Nat.card A = 24)
    (hstable : ∀ a : A, ∀ x : U, (a : MulAut U) x ∈ W ↔ x ∈ W) :
    Nonempty (A ≃* Equiv.Perm (Fin 4)) := by
  classical
  let X := {x : U // x ∉ W}
  let : Fintype U := Fintype.ofFinite U
  have hc : Nat.card X = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rw [hU, hW]
  have hn : Nonempty X := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card X)).1
  obtain ⟨c⟩ := hn
  let r := outsideRep W A hstable
  have hr : Function.Injective r := outsideRep_injective W c.val c.property A hstable
  have hrCard : Nat.card A = Nat.card (Equiv.Perm X) := by
    rw [hA, Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hc]
    decide
  exact ⟨(MulEquiv.ofBijective r ((Nat.bijective_iff_injective_and_card r).mpr ⟨hr, hrCard⟩)).trans
    (Equiv.permCongrHom (Finite.equivFinOfCardEq hc))⟩

/-- An order-twenty-four automorphism subgroup has at most one invariant
subgroup of order four in an elementary group of order eight. -/
public theorem elementaryEight_plane_order24_unique
    {U : Type*} [Group U] [Finite U] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 8) (W C : Subgroup U)
    (hW : Nat.card W = 4) (hC : Nat.card C = 4)
    (A : Subgroup (MulAut U)) (hA : Nat.card A = 24)
    (hWstable : ∀ a : A, ∀ x : U, (a : MulAut U) x ∈ W ↔ x ∈ W)
    (hCstable : ∀ a : A, ∀ x : U, (a : MulAut U) x ∈ C ↔ x ∈ C) :
    W = C := by
  classical
  by_contra hne
  have hCW : ¬ C ≤ W := fun hle => hne
    (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  have hWC : ¬ W ≤ C := fun hle => hne
    (Subgroup.eq_of_le_of_card_ge hle (by omega))
  obtain ⟨c,hcC,hcW⟩ := SetLike.not_le_iff_exists.mp hCW
  obtain ⟨w,hwW,hwC⟩ := SetLike.not_le_iff_exists.mp hWC
  let X := {x : U // x ∉ W}
  let _ : Fintype U := Fintype.ofFinite U
  have hX : Nat.card X = 4 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hU,hW]
  let rep := outsideRep W A hWstable
  have hinj : Function.Injective rep := outsideRep_injective W c hcW A hWstable
  have hsurj : Function.Surjective rep :=
    ((Nat.bijective_iff_injective_and_card rep).mpr ⟨hinj,by
      rw [hA,Nat.card_eq_fintype_card,Fintype.card_perm,←Nat.card_eq_fintype_card,hX]
      decide⟩).2
  have hwcW : w*c ∉ W := by
    intro h
    exact hcW (by simpa using W.mul_mem (W.inv_mem hwW) h)
  have hwcC : w*c ∉ C := by
    intro h
    exact hwC (by simpa using C.mul_mem h (C.inv_mem hcC))
  let cX : X := ⟨c,hcW⟩
  let wcX : X := ⟨w*c,hwcW⟩
  obtain ⟨a,ha⟩ := hsurj (Equiv.swap cX wcX)
  have heq : (a : MulAut U) c = w*c := by
    have hh := congrArg Subtype.val (Equiv.congr_fun ha cX)
    simpa [rep,outsideRep,cX,wcX] using hh
  exact hwcC (heq ▸ (hCstable a c).mpr hcC)

/-- A full plane stabilizer fixes no nonidentity element of the elementary
group. Its full symmetric action on the four points outside the plane also
detects every nonidentity translation coming from the plane. -/
public theorem elementaryEight_plane_order24_fixed_eq_one
    {U : Type*} [Group U] [Finite U] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 8) (W : Subgroup U) (hW : Nat.card W = 4)
    (A : Subgroup (MulAut U)) (hA : Nat.card A = 24)
    (hstable : ∀ a : A, ∀ x : U, (a : MulAut U) x ∈ W ↔ x ∈ W)
    (z : U) (hfix : ∀ a : A, (a : MulAut U) z = z) : z = 1 := by
  classical
  let X := {x : U // x ∉ W}
  let _ : Fintype U := Fintype.ofFinite U
  have hX : Fintype.card X = 4 := by
    rw [Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hU, hW]
  obtain ⟨c⟩ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  let rep := outsideRep W A hstable
  have hsurj : Function.Surjective rep :=
    ((Nat.bijective_iff_injective_and_card rep).mpr
      ⟨outsideRep_injective W c.val c.property A hstable, by
        rw [hA, Nat.card_eq_fintype_card, Fintype.card_perm, hX]
        decide⟩).2
  have hWz : z ∈ W := by
    by_contra hz
    let zz : X := ⟨z, hz⟩
    obtain ⟨d, hd⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card X) zz
    obtain ⟨a, ha⟩ := hsurj (Equiv.swap zz d)
    have heq : (a : MulAut U) z = d.val := by
      have hh := congrArg Subtype.val (Equiv.congr_fun ha zz)
      simpa [rep, outsideRep, zz] using hh
    exact hd (Subtype.ext (heq.symm.trans (hfix a)))
  by_contra hz
  have hzc : z * c.val ∉ W := by
    intro h
    exact c.property (by simpa using W.mul_mem (W.inv_mem hWz) h)
  let zc : X := ⟨z * c.val, hzc⟩
  have hzcne : zc ≠ c := by
    intro h
    have hh : z * c.val = c.val := congrArg Subtype.val h
    exact hz (mul_right_cancel (hh.trans (one_mul c.val).symm))
  obtain ⟨d, hdc, hdzc⟩ : ∃ d : X, d ≠ c ∧ d ≠ zc := by
    by_contra! h
    have hsub : (Finset.univ : Finset X) ⊆ {c, zc} := by
      intro x _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hx : x = c
      · exact Or.inl hx
      · exact Or.inr (h x hx)
    have hbound := Finset.card_le_card hsub
    have hpair : ({c, zc} : Finset X).card ≤ 2 := by simp [Ne.symm hzcne]
    rw [Finset.card_univ, hX] at hbound
    omega
  obtain ⟨a, ha⟩ := hsurj (Equiv.swap c d)
  have hac : (a : MulAut U) c.val = d.val := by
    have hh := congrArg Subtype.val (Equiv.congr_fun ha c)
    simpa [rep, outsideRep] using hh
  have hazc : (a : MulAut U) (z * c.val) = z * c.val := by
    have hh := congrArg Subtype.val (Equiv.congr_fun ha zc)
    simpa [rep, outsideRep, Equiv.swap_apply_of_ne_of_ne hzcne hdzc.symm, zc] using hh
  rw [map_mul, hfix, hac] at hazc
  exact hdc (Subtype.ext (mul_left_cancel hazc))

/-- The full plane stabilizer is transitive on the points outside its plane. -/
public theorem elementaryEight_plane_order24_outside_transitive
    {U : Type*} [Group U] [Finite U] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 8) (W : Subgroup U) (hW : Nat.card W = 4)
    (A : Subgroup (MulAut U)) (hA : Nat.card A = 24)
    (hstable : ∀ a : A, ∀ x : U, (a : MulAut U) x ∈ W ↔ x ∈ W)
    (x y : U) (hx : x ∉ W) (hy : y ∉ W) :
    ∃ a : A, (a : MulAut U) x = y := by
  classical
  let X := {u : U // u ∉ W}
  let _ : Fintype U := Fintype.ofFinite U
  have hX : Fintype.card X = 4 := by
    rw [Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hU, hW]
  let rep := outsideRep W A hstable
  have hsurj : Function.Surjective rep :=
    ((Nat.bijective_iff_injective_and_card rep).mpr
      ⟨outsideRep_injective W x hx A hstable, by
        rw [hA, Nat.card_eq_fintype_card, Fintype.card_perm, hX]
        decide⟩).2
  obtain ⟨a, ha⟩ := hsurj (Equiv.swap (⟨x, hx⟩ : X) ⟨y, hy⟩)
  exact ⟨a, by
    have hh := congrArg Subtype.val (Equiv.congr_fun ha ⟨x, hx⟩)
    simpa [rep, outsideRep] using hh⟩

/-- The three nonidentity points of the invariant plane form one orbit. -/
public theorem elementaryEight_plane_order24_plane_transitive
    {U : Type*} [Group U] [Finite U] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 8) (W : Subgroup U) (hW : Nat.card W = 4)
    (A : Subgroup (MulAut U)) (hA : Nat.card A = 24)
    (hstable : ∀ a : A, ∀ x : U, (a : MulAut U) x ∈ W ↔ x ∈ W)
    (x y : U) (hx : x ∈ W) (hy : y ∈ W) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ a : A, (a : MulAut U) x = y := by
  classical
  let X := {u : U // u ∉ W}
  let _ : Fintype U := Fintype.ofFinite U
  have hX : Fintype.card X = 4 := by
    rw [Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hU, hW]
  obtain ⟨c⟩ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  let rep := outsideRep W A hstable
  have hsurj : Function.Surjective rep :=
    ((Nat.bijective_iff_injective_and_card rep).mpr
      ⟨outsideRep_injective W c.val c.property A hstable, by
        rw [hA, Nat.card_eq_fintype_card, Fintype.card_perm, hX]
        decide⟩).2
  have hxc : x * c.val ∉ W := by
    intro h
    exact c.property (by simpa using W.mul_mem (W.inv_mem hx) h)
  have hyc : y * c.val ∉ W := by
    intro h
    exact c.property (by simpa using W.mul_mem (W.inv_mem hy) h)
  let xc : X := ⟨x * c.val, hxc⟩
  let yc : X := ⟨y * c.val, hyc⟩
  have hcxc : c ≠ xc := by
    intro h
    exact hx1 (mul_right_cancel ((congrArg Subtype.val h).symm.trans (one_mul c.val).symm))
  have hcyc : c ≠ yc := by
    intro h
    exact hy1 (mul_right_cancel ((congrArg Subtype.val h).symm.trans (one_mul c.val).symm))
  obtain ⟨a, ha⟩ := hsurj (Equiv.swap xc yc)
  have hac : (a : MulAut U) c.val = c.val := by
    have hh := congrArg Subtype.val (Equiv.congr_fun ha c)
    simpa [rep, outsideRep, Equiv.swap_apply_of_ne_of_ne hcxc hcyc] using hh
  have haxc : (a : MulAut U) (x * c.val) = y * c.val := by
    have hh := congrArg Subtype.val (Equiv.congr_fun ha xc)
    simpa [rep, outsideRep, xc, yc] using hh
  rw [map_mul, hac] at haxc
  exact ⟨a, mul_right_cancel haxc⟩

/-- Each point outside the invariant plane has stabilizer of order six. -/
public theorem elementaryEight_plane_order24_outside_stabilizer_card
    {U : Type*} [Group U] [Finite U] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 8) (W : Subgroup U) (hW : Nat.card W = 4)
    (A : Subgroup (MulAut U)) (hA : Nat.card A = 24)
    (hstable : ∀ a : A, ∀ x : U, (a : MulAut U) x ∈ W ↔ x ∈ W)
    (x : U) (hx : x ∉ W) : Nat.card (MulAction.stabilizer A x) = 6 := by
  classical
  let _ : Fintype U := Fintype.ofFinite U
  have horbit : MulAction.orbit A x = {y : U | y ∉ W} := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact fun h => hx ((hstable a x).mp h)
    · intro hy
      obtain ⟨a, ha⟩ := elementaryEight_plane_order24_outside_transitive
        hU W hW A hA hstable x y hx hy
      exact ⟨a, ha⟩
  have hcard : Nat.card (MulAction.orbit A x) = 4 := by
    rw [horbit, Nat.card_eq_fintype_card]
    change Fintype.card {y : U // y ∉ W} = 4
    rw [Fintype.card_subtype_compl,
      ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hU, hW]
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A x)
  rw [Nat.card_prod, hcard, hA] at h
  omega

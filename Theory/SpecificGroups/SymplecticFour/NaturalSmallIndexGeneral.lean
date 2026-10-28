module
public import Theory.SpecificGroups.SymplecticFour.CentralNaturalDerivedAmbient
public import Theory.ElementaryAbelian.BinaryPairingIsotropic
public import Theory.ElementaryAbelian.BinarySeparatingCharacter
public import Theory.ElementaryAbelian.Quotient

/-!
# Small-index subgroups of central natural symplectic extensions

A subgroup of index at most q retains the full derived group of a central
extension of the natural Sp4(q) module. If it lost derived elements, a
nonzero binary character of the missing quotient would turn the commutator
into a nondegenerate binary pairing on the literal natural quotient.
The subgroup image is isotropic and therefore has order at most q squared,
whereas its index bound forces order at least q cubed.

No field-linearity of the subgroup image or complement to the full central
kernel is assumed. The actor and quotient maps retain their original
equivariance. Source: MS93 (3.10), printed pp.880--881, used in (5.12).
-/

public noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Subgroup.ClassTwo
open Theory.SpecificGroups.SymplecticFour

private theorem full_row_derived_elementary
    {P V : Type*} [Group P] [Group V] [IsElementaryAbelian 2 V]
    (hc : _root_.commutator P ≤ center P)
    (f : P →* V) (hf : Function.Surjective f) (hk : f.ker ≤ center P)
    (x : P) (hrow : _root_.commutator P = ⁅zpowers x,(⊤ : Subgroup P)⁆) :
    IsElementaryAbelian 2 (_root_.commutator P) := by
  let r : P →* _root_.commutator P := (commutatorHom hc x).codRestrict
    (_root_.commutator P) (fun y => commutator_mem_commutator (mem_top x) (mem_top y))
  have hkr : f.ker ≤ r.ker := by
    intro y hy
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hk hy) x)
  let φ : V →* _root_.commutator P := f.liftOfSurjective hf ⟨r,hkr⟩
  have hφ (y : P) : φ (f y)=r y := f.liftOfRightInverse_comp_apply _ _ _ y
  apply IsElementaryAbelian.of_surjective φ
  intro c
  have hmem : c.val ∈ (commutatorHom hc x).range := by
    rw [commutatorHom_range,←hrow]
    exact c.property
  obtain ⟨y,hy⟩ := hmem
  exact ⟨f y,(hφ y).trans (Subtype.ext hy)⟩

private theorem exists_scalar_commutator_pairing
    {P V : Type*} [Group P] [Group V]
    (hc : _root_.commutator P ≤ center P)
    (f : P →* V) (hf : Function.Surjective f) (hk : f.ker ≤ center P)
    (χ : _root_.commutator P →* Multiplicative (ZMod 2)) :
    ∃ b : V →* (V →* Multiplicative (ZMod 2)),
      ∀ x y : P, b (f x) (f y) =
        χ ⟨⁅x,y⁆,commutator_mem_commutator (mem_top x) (mem_top y)⟩ := by
  let r (x : P) : P →* Multiplicative (ZMod 2) := χ.comp
    ((commutatorHom hc x).codRestrict (_root_.commutator P)
      (fun y => commutator_mem_commutator (mem_top x) (mem_top y)))
  have hkr (x : P) : f.ker ≤ (r x).ker := by
    intro y hy
    change χ ⟨⁅x,y⁆,_⟩=1
    have he : (⟨⁅x,y⁆,commutator_mem_commutator (mem_top x) (mem_top y)⟩ :
        _root_.commutator P)=1 := Subtype.ext
      (commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hk hy) x))
    rw [he,map_one]
  let φ (x : P) : V →* Multiplicative (ZMod 2) := f.liftOfSurjective hf ⟨r x,hkr x⟩
  have hφ (x y : P) : φ x (f y)=r x y := f.liftOfRightInverse_comp_apply _ _ _ y
  let b₀ : P →* (V →* Multiplicative (ZMod 2)) := {
    toFun := φ
    map_one' := by
      apply MonoidHom.ext
      intro v
      obtain ⟨y,rfl⟩ := hf v
      rw [hφ]
      change χ ⟨⁅(1:P),y⁆,_⟩=1
      rw [show (⟨⁅(1:P),y⁆,commutator_mem_commutator (mem_top _) (mem_top _)⟩ :
        _root_.commutator P)=1 from Subtype.ext (by simp),map_one]
    map_mul' := by
      intro x y
      apply MonoidHom.ext
      intro v
      obtain ⟨z,rfl⟩ := hf v
      change φ (x*y) (f z)=φ x (f z)*φ y (f z)
      rw [hφ,hφ,hφ]
      change χ ⟨⁅x*y,z⁆,_⟩=χ ⟨⁅x,z⁆,_⟩*χ ⟨⁅y,z⁆,_⟩
      rw [←map_mul]
      apply congrArg χ
      apply Subtype.ext
      change ⁅x*y,z⁆=⁅x,z⁆*⁅y,z⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hz := mem_center_iff.mp
        (hc (commutator_mem_commutator (mem_top y) (mem_top z)))
      rw [hz x,mul_inv_cancel_right]
      exact (hz ⁅x,z⁆).symm }
  have hkb : f.ker ≤ b₀.ker := by
    intro x hx
    apply MonoidHom.ext
    intro v
    obtain ⟨y,rfl⟩ := hf v
    change φ x (f y)=1
    rw [hφ]
    change χ ⟨⁅x,y⁆,_⟩=1
    have he : (⟨⁅x,y⁆,commutator_mem_commutator (mem_top x) (mem_top y)⟩ :
        _root_.commutator P)=1 := Subtype.ext
      (commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hk hx) y).symm)
    rw [he,map_one]
  let b : V →* (V →* Multiplicative (ZMod 2)) := f.liftOfSurjective hf ⟨b₀,hkb⟩
  refine ⟨b,?_⟩
  intro x y
  have hb : b (f x)=b₀ x := f.liftOfRightInverse_comp_apply _ _ _ x
  rw [hb]
  exact hφ x y

variable {P A F : Type*} [Group P] [Finite P] [Group A]
  [Field F] [CharP F 2] [Finite F]

/-- Every subgroup of index at most the field order retains the entire
derived group of the actual central natural symplectic extension. -/
theorem derived_eq_of_symplectic_section_index_le_field
    (hc : _root_.commutator P ≤ center P)
    (α : A →* MulAut P) (π : A →* Sp F) (hπ : Function.Surjective π)
    (f : P →* Multiplicative (Vector F)) (hf : Function.Surjective f)
    (hker : f.ker ≤ center P)
    (hequiv : ∀ a v, (f (α a v)).toAdd = π a • (f v).toAdd)
    (hfix : ∀ a : A, ∀ c ∈ _root_.commutator P, α a c=c)
    (S : Subgroup P) (hi : S.index ≤ Nat.card F) :
    ⁅S,S⁆ = _root_.commutator P := by
  let V := Multiplicative (Vector F)
  let : IsElementaryAbelian 2 V := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro v
      change (2 : ℕ) • v.toAdd=0
      rw [two_nsmul]
      ext i
      exact CharTwo.add_self_eq_zero _) }
  have hrow (x : P) (hx : f x ≠ 1) :
      _root_.commutator P = ⁅zpowers x,(⊤ : Subgroup P)⁆ :=
    commutator_eq_row_of_symplectic_section α π hπ f hker hequiv hfix x hx
  obtain ⟨x,hx⟩ := hf (Multiplicative.ofAdd (e 0))
  have hx0 : f x ≠ 1 := by
    rw [hx]
    intro hh
    have he := congrFun (congrArg Multiplicative.toAdd hh) (.inl 0)
    simp [Theory.SpecificGroups.SymplecticFour.e] at he
  let : IsElementaryAbelian 2 (_root_.commutator P) :=
    full_row_derived_elementary hc f hf hker x (hrow x hx0)
  have hD : ⁅S,S⁆ ≤ _root_.commutator P := commutator_mono le_top le_top
  apply le_antisymm hD
  by_contra hn
  let T := (⁅S,S⁆).subgroupOf (_root_.commutator P)
  have hT : T ≠ ⊤ := by
    intro ht
    apply hn
    intro c hc'
    exact (show (⟨c,hc'⟩ : _root_.commutator P) ∈ T from ht ▸ mem_top _)
  obtain ⟨χ,hχ,hkill⟩ := IsElementaryAbelian.exists_nontrivial_binary_character T hT
  obtain ⟨b,hb⟩ := exists_scalar_commutator_pairing hc f hf hker χ
  have hbinj : Function.Injective b := by
    apply b.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro v hv
    obtain ⟨y,rfl⟩ := hf v
    by_contra hy
    have hy0 : f y ≠ 1 := hy
    apply hχ
    apply MonoidHom.ext
    intro c
    have hmem : c.val ∈ (commutatorHom hc y).range := by
      rw [commutatorHom_range,←hrow y hy0]
      exact c.property
    obtain ⟨z,hz⟩ := hmem
    have he := congrArg (fun φ : V →* Multiplicative (ZMod 2) => φ (f z)) hv
    rw [hb] at he
    have hc' : (⟨⁅y,z⁆,commutator_mem_commutator (mem_top y) (mem_top z)⟩ :
        _root_.commutator P)=c := Subtype.ext hz
    rwa [hc'] at he
  have hiso : ∀ u ∈ S.map f, ∀ v ∈ S.map f, b u v=1 := by
    rintro u ⟨s,hs,rfl⟩ v ⟨t,ht,rfl⟩
    rw [hb]
    exact hkill (commutator_mem_commutator hs ht)
  have hcard : Nat.card V=Nat.card F^4 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    simp [Theory.SpecificGroups.SymplecticFour.Vector,Nat.card_fun]
  have hsq := MonoidHom.binary_pairing_isotropic_card_sq_le b hbinj (S.map f) hiso
  rw [hcard] at hsq
  have hsize : Nat.card (S.map f) ≤ Nat.card F^2 := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    simpa only [←pow_mul] using hsq
  have hindex : (S.map f).index ≤ Nat.card F :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero S.index_ne_zero_of_finite) (S.index_map_dvd hf)).trans hi
  have hbound : Nat.card F^4 ≤ Nat.card F^3 := by
    calc
      Nat.card F^4 = Nat.card (S.map f)*(S.map f).index := by rw [card_mul_index,hcard]
      _ ≤ Nat.card F^2*Nat.card F := Nat.mul_le_mul hsize hindex
      _ = Nat.card F^3 := by ring
  exact (Nat.pow_lt_pow_right (Finite.one_lt_card (α := F)) (by decide : 3<4)).not_ge hbound

variable {G : Type*} [Group G]

/-- The general-field small-index theorem for the literal ambient
intersection, retaining the original conjugation action and full kernel. -/
theorem derived_intersection_eq_of_natural_central_section_index_le_field
    (L V Y : Subgroup G) [Finite V]
    (hVL : V ≤ L) (hLV : L ≤ normalizer (V : Set G))
    (π : L →* Sp F) (hπ : Function.Surjective π)
    (f : V →* Multiplicative (Vector F)) (hf : Function.Surjective f)
    (hker : f.ker ≤ center V)
    (hequiv : ∀ (a : L) (v : V),
      (f ⟨(a : G)*v*(a : G)⁻¹,
        (mem_normalizer_iff.mp (hLV a.property) v).mp v.property⟩).toAdd =
          π a • (f v).toAdd)
    (hfix : ⁅V,V⁆ ≤ centralizer (L : Set G))
    (hi : (Y.subgroupOf V).index ≤ Nat.card F) :
    ⁅V ⊓ Y,V ⊓ Y⁆ = ⁅V,V⁆ := by
  let α : L →* MulAut V := V.normalizerMonoidHom.comp (inclusion hLV)
  have hmap : (_root_.commutator V).map V.subtype=⁅V,V⁆ := by
    rw [map_commutator_eq,range_subtype]
  have hcent : _root_.commutator V ≤ center V := by
    intro c hc
    apply mem_center_iff.mpr
    intro v
    apply Subtype.ext
    exact hfix (hmap ▸ mem_map_of_mem V.subtype hc) v (hVL v.property)
  have hfixed : ∀ a : L, ∀ c ∈ _root_.commutator V, α a c=c := by
    intro a c hc
    apply Subtype.ext
    change (a : G)*(c : G)*(a : G)⁻¹=c
    have he := hfix (hmap ▸ mem_map_of_mem V.subtype hc) a a.property
    change (a : G)*(c : G)=(c : G)*a at he
    rw [he,mul_inv_cancel_right]
  have he := derived_eq_of_symplectic_section_index_le_field hcent α π hπ
    f hf hker hequiv hfixed (Y.subgroupOf V) hi
  have hm := congrArg (Subgroup.map V.subtype) he
  simpa only [map_commutator,subgroupOf_map_subtype,inf_comm,hmap] using hm

end Subgroup.ClassTwo

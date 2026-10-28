module

public import Theory.SpecificGroups.Suzuki.StandardSubgroups

/-!
# The natural Suzuki ovoid and its root groups

The canonical Tits automorphism defines the Suzuki ovoid. We restrict the
projective matrix action to this finite set and transport the coordinate
results of Huppert--Blackburn III, XI.3.3. Root regularity identifies the
normalizer of the root group and gives trivial intersections of distinct
conjugates. The Frobenius action of the Borel gives complement conjugacy and
coverage of elements with a fixed point, as in XI.3.10(b),(e).
-/

namespace BenderSuzuki.MatrixGroups

open PFAppendixIII
open scoped Pointwise LinearAlgebra.Projectivization

/-- The canonical Tits automorphism of the Suzuki field. -/
@[expose] public noncomputable def suzukiTits (m : ℕ) :
    BinaryGaloisField (2 * m + 1) ≃+* BinaryGaloisField (2 * m + 1) :=
  iterateFrobeniusEquiv _ 2 (m + 1)

public theorem suzukiTits_apply (m : ℕ) (x : BinaryGaloisField (2 * m + 1)) :
    suzukiTits m x = x ^ (2 ^ (m + 1)) :=
  iterateFrobeniusEquiv_def _ 2 (m + 1) x

public theorem suzukiTits_sq (m : ℕ) (x : BinaryGaloisField (2 * m + 1)) :
    suzukiTits m (suzukiTits m x) = x ^ 2 :=
  External.binaryGaloisField_tits_formula_sq m (suzukiTits m) (suzukiTits_apply m) x

/-- The ovoid as a set of projective points. -/
@[expose] public noncomputable def suzukiOvoidSet (m : ℕ) :
    Set (ℙ (BinaryGaloisField (2 * m + 1)) (Fin 4 → BinaryGaloisField (2 * m + 1))) :=
  {Projectivization.mk _ ![1, 0, 0, 0] (by simp)} ∪
    Set.range (fun z : BinaryGaloisField (2 * m + 1) × BinaryGaloisField (2 * m + 1) =>
      Projectivization.mk _
        ![z.1 * z.2 + suzukiTits m z.1 * z.1 ^ 2 + suzukiTits m z.2,
          z.2, z.1, 1] (by simp))

/-- The points of the natural Suzuki ovoid. -/
@[expose] public def SuzukiOvoid (m : ℕ) := ↥(suzukiOvoidSet m)

/-- The distinguished point at infinity. -/
@[expose] public noncomputable def suzukiOvoidInfinity (m : ℕ) : SuzukiOvoid m :=
  ⟨Projectivization.mk _ ![1, 0, 0, 0] (by simp), Or.inl rfl⟩

/-- The finite point with both coordinates zero. -/
@[expose] public noncomputable def suzukiOvoidZero (m : ℕ) : SuzukiOvoid m :=
  ⟨_, Or.inr ⟨(0, 0), rfl⟩⟩

public theorem suzukiOvoidInfinity_ne_zero (m : ℕ) :
    suzukiOvoidInfinity m ≠ suzukiOvoidZero m := by
  intro h
  exact External.suzukiOvoidInfinity_not_mem_range m (suzukiTits m)
    ⟨(0, 0), (congrArg Subtype.val h).symm⟩

public noncomputable instance suzukiOvoidMulAction (m : ℕ) :
    MulAction (SuzukiMatrixGroup m) (SuzukiOvoid m) where
  smul g z := ⟨(Matrix.GeneralLinearGroup.toLin g.val).toLinearEquiv • z.val,
    (External.suzukiMatrixGroup_ovoid_action_data m (suzukiTits m)
      (suzukiTits_apply m)).1 g z.val z.property⟩
  one_smul z := by
    apply Subtype.ext
    change (Matrix.GeneralLinearGroup.toLin 1).toLinearEquiv • z.val = z.val
    rw [map_one]
    change (1 : (Fin 4 → BinaryGaloisField (2 * m + 1)) ≃ₗ[BinaryGaloisField (2 * m + 1)] _) • z.val = z.val
    exact one_smul _ _
  mul_smul g h z := by
    apply Subtype.ext
    change (Matrix.GeneralLinearGroup.toLin (g.val * h.val)).toLinearEquiv • z.val = _
    rw [map_mul]
    change ((Matrix.GeneralLinearGroup.toLin g.val).toLinearEquiv *
      (Matrix.GeneralLinearGroup.toLin h.val).toLinearEquiv) • z.val =
      (Matrix.GeneralLinearGroup.toLin g.val).toLinearEquiv •
        ((Matrix.GeneralLinearGroup.toLin h.val).toLinearEquiv • z.val)
    exact mul_smul _ _ _

/-- The named action agrees with the ambient projective matrix action. -/
public theorem suzukiOvoid_smul_val (m : ℕ) (g : SuzukiMatrixGroup m)
    (a : SuzukiOvoid m) :
    (g • a).val = (Matrix.GeneralLinearGroup.toLin g.val).toLinearEquiv • a.val := rfl

public instance suzukiOvoid_faithful (m : ℕ) :
    FaithfulSMul (SuzukiMatrixGroup m) (SuzukiOvoid m) where
  eq_of_smul_eq_smul {g h} heq := by
    have hid : g⁻¹ * h = 1 := by
      apply (External.suzukiMatrixGroup_ovoid_action_data m (suzukiTits m)
        (suzukiTits_apply m)).2.1
      intro a ha
      let z : SuzukiOvoid m := ⟨a, ha⟩
      have hfix : (g⁻¹ * h) • z = z := by
        rw [mul_smul, ← heq, inv_smul_smul]
      exact congrArg Subtype.val hfix
    exact inv_mul_eq_one.mp hid

public theorem suzukiOvoid_card (m : ℕ) :
    Nat.card (SuzukiOvoid m) = (2 ^ (2 * m + 1)) ^ 2 + 1 :=
  (External.suzukiMatrixGroup_ovoid_action_data m (suzukiTits m)
    (suzukiTits_apply m)).2.2.2

public instance suzukiOvoid_finite (m : ℕ) : Finite (SuzukiOvoid m) :=
  Nat.finite_of_card_ne_zero (by rw [suzukiOvoid_card]; omega)

public instance suzukiOvoid_nontrivial (m : ℕ) : Nontrivial (SuzukiOvoid m) :=
  ⟨⟨_, _, suzukiOvoidInfinity_ne_zero m⟩⟩

/-- The Suzuki action is doubly transitive, including for `m = 0`. -/
public instance suzukiOvoid_two_pretransitive (m : ℕ) :
    MulAction.IsMultiplyPretransitive (SuzukiMatrixGroup m) (SuzukiOvoid m) 2 := by
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨g, hga, hgb⟩ := (External.suzukiMatrixGroup_ovoid_action_data m
    (suzukiTits m) (suzukiTits_apply m)).2.2.1
      a.val b.val c.val d.val a.property b.property c.property d.property
      (fun h => hab (Subtype.ext h)) (fun h => hcd (Subtype.ext h))
  exact ⟨g, Subtype.ext hga, Subtype.ext hgb⟩

public instance suzukiOvoid_pretransitive (m : ℕ) :
    MulAction.IsPretransitive (SuzukiMatrixGroup m) (SuzukiOvoid m) :=
  MulAction.isPretransitive_of_is_two_pretransitive

/-- A nonidentity element cannot fix three distinct ovoid points. -/
public theorem suzukiOvoid_at_most_two_fixed (m : ℕ) (hm : 0 < m)
    (g : SuzukiMatrixGroup m) (hg : g ≠ 1)
    (a b c : SuzukiOvoid m) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : g • a = a) (hb : g • b = b) : g • c ≠ c := by
  intro hc
  apply hg
  apply (External.huppert_blackburn_XI_3_3 m hm (suzukiTits m)
    (suzukiTits_apply m)).2.2.2.2.1 g
  exact ⟨a.val, b.val, c.val, a.property, b.property, c.property,
    (fun h => hab (Subtype.ext h)), (fun h => hac (Subtype.ext h)),
    (fun h => hbc (Subtype.ext h)), congrArg Subtype.val ha,
    congrArg Subtype.val hb, congrArg Subtype.val hc⟩

/-- The standard Borel is the infinity stabilizer for the named action. -/
public theorem suzukiBorelSubgroup_eq_stabilizer (m : ℕ) (hm : 0 < m) :
    SuzukiBorelSubgroup m = MulAction.stabilizer (SuzukiMatrixGroup m)
      (suzukiOvoidInfinity m) := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  rw [mem_suzukiBorelSubgroup_iff_fix_infinity m hm g]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- The root group acts regularly on the complement of infinity. -/
public theorem suzukiRootSubgroup_regular (m : ℕ) (a b : SuzukiOvoid m)
    (ha : a ≠ suzukiOvoidInfinity m) (hb : b ≠ suzukiOvoidInfinity m) :
    ∃! r : SuzukiRootSubgroup m, (r : SuzukiMatrixGroup m) • a = b := by
  let e : SuzukiRootSubgroup m ≃* SuzukiRootClosure m :=
    Subgroup.subgroupOfEquivOfLe (suzukiRootClosure_le m)
  obtain ⟨r, hr, hu⟩ := External.suzukiRootClosure_regular_on_ovoid_complement
    m (suzukiTits m) (suzukiTits_apply m) a.val b.val a.property b.property
    (fun h => ha (Subtype.ext h)) (fun h => hb (Subtype.ext h))
  refine ⟨e.symm r, Subtype.ext ?_, ?_⟩
  · exact hr
  · intro s hs
    apply e.injective
    exact (hu (e s) (congrArg Subtype.val hs)).trans (e.apply_symm_apply r).symm

/-- Every root element fixes infinity. -/
public theorem suzukiRootSubgroup_fix_infinity (m : ℕ) (hm : 0 < m)
    (g : SuzukiMatrixGroup m) (hg : g ∈ SuzukiRootSubgroup m) :
    g • suzukiOvoidInfinity m = suzukiOvoidInfinity m := by
  apply MulAction.mem_stabilizer_iff.mp
  rw [← suzukiBorelSubgroup_eq_stabilizer m hm, suzukiBorelSubgroup_eq_sup]
  exact (show SuzukiRootSubgroup m ≤ SuzukiRootSubgroup m ⊔ SuzukiSplitTorus m from le_sup_left) hg

/-- A nonidentity root element fixes precisely infinity. -/
public theorem suzukiRootSubgroup_fixed_iff (m : ℕ) (hm : 0 < m)
    (g : SuzukiMatrixGroup m) (hg : g ∈ SuzukiRootSubgroup m) (hne : g ≠ 1)
    (a : SuzukiOvoid m) : g • a = a ↔ a = suzukiOvoidInfinity m := by
  constructor
  · intro hfix
    by_contra ha
    obtain ⟨r, _, hu⟩ := suzukiRootSubgroup_regular m a a ha ha
    have heq : (⟨g, hg⟩ : SuzukiRootSubgroup m) = 1 :=
      (hu ⟨g, hg⟩ hfix).trans (hu 1 (one_smul _ a)).symm
    exact hne (congrArg Subtype.val heq)
  · rintro rfl
    exact suzukiRootSubgroup_fix_infinity m hm g hg

/-- The full normalizer of the standard root group is the standard Borel. -/
public theorem suzukiRootSubgroup_normalizer (m : ℕ) (hm : 0 < m) :
    Subgroup.normalizer (SuzukiRootSubgroup m) = SuzukiBorelSubgroup m := by
  apply le_antisymm
  · intro g hg
    have hn : Nontrivial (SuzukiRootSubgroup m) := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      rw [suzukiRootSubgroup_card m hm]
      have hq : 1 < 2 ^ (2 * m + 1) := one_lt_pow₀ (by decide) (by omega)
      nlinarith
    obtain ⟨r, hr⟩ := exists_ne (1 : SuzukiRootSubgroup m)
    have hrne : (r : SuzukiMatrixGroup m) ≠ 1 := fun h => hr (Subtype.ext h)
    have hmem : g⁻¹ * (r : SuzukiMatrixGroup m) * g ∈ SuzukiRootSubgroup m :=
      (Subgroup.mem_normalizer_iff''.mp hg (r : SuzukiMatrixGroup m)).mp r.property
    have hfix : (r : SuzukiMatrixGroup m) • (g • suzukiOvoidInfinity m) =
        g • suzukiOvoidInfinity m := by
      have h := suzukiRootSubgroup_fix_infinity m hm _ hmem
      have h' := congrArg (g • ·) h
      simpa only [mul_smul, smul_inv_smul] using h'
    rw [suzukiBorelSubgroup_eq_stabilizer m hm, MulAction.mem_stabilizer_iff]
    exact (suzukiRootSubgroup_fixed_iff m hm r r.property hrne _).mp hfix
  · rw [suzukiBorelSubgroup_eq_sup]
    exact sup_le Subgroup.le_normalizer (suzukiSplitTorus_le_normalizer_root m)

/-- A root group and a conjugate outside its normalizer intersect trivially. -/
public theorem suzukiRootSubgroup_disjoint_conjugate (m : ℕ) (hm : 0 < m)
    (g : SuzukiMatrixGroup m) (hg : g ∉ SuzukiBorelSubgroup m) :
    Disjoint (SuzukiRootSubgroup m)
      ((SuzukiRootSubgroup m).map (MulAut.conj g).toMonoidHom) := by
  apply disjoint_iff.mpr
  apply le_antisymm ?_ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  by_contra hxne
  obtain ⟨r, hr, rfl⟩ := hx.2
  have hfix : (MulAut.conj g) r • (g • suzukiOvoidInfinity m) =
      g • suzukiOvoidInfinity m := by
    simp only [MulAut.conj_apply, mul_smul, inv_smul_smul,
      suzukiRootSubgroup_fix_infinity m hm r hr]
  have heq := (suzukiRootSubgroup_fixed_iff m hm _ hx.1 hxne _).mp hfix
  apply hg
  rw [suzukiBorelSubgroup_eq_stabilizer m hm, MulAction.mem_stabilizer_iff]
  exact heq

/-- Any two distinct conjugates of the root group intersect trivially. -/
public theorem suzukiRootSubgroup_conjugates_disjoint (m : ℕ) (hm : 0 < m)
    (g h : SuzukiMatrixGroup m)
    (hne : (SuzukiRootSubgroup m).map (MulAut.conj g).toMonoidHom ≠
      (SuzukiRootSubgroup m).map (MulAut.conj h).toMonoidHom) :
    Disjoint ((SuzukiRootSubgroup m).map (MulAut.conj g).toMonoidHom)
      ((SuzukiRootSubgroup m).map (MulAut.conj h).toMonoidHom) := by
  have hcomp : (MulAut.conj g).toMonoidHom.comp
      (MulAut.conj (g⁻¹ * h)).toMonoidHom = (MulAut.conj h).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hout : g⁻¹ * h ∉ SuzukiBorelSubgroup m := by
    intro hmem
    rw [← suzukiRootSubgroup_normalizer m hm,
      Subgroup.mem_normalizer_iff_map_conj_eq] at hmem
    apply hne
    calc
      _ = ((SuzukiRootSubgroup m).map
          (MulAut.conj (g⁻¹ * h)).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
        congrArg (fun H : Subgroup (SuzukiMatrixGroup m) =>
          H.map (MulAut.conj g).toMonoidHom) hmem.symm
      _ = _ := by rw [Subgroup.map_map, hcomp]
  have hd := Subgroup.disjoint_map (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective
    (suzukiRootSubgroup_disjoint_conjugate m hm (g⁻¹ * h) hout)
  rw [Subgroup.map_map, hcomp] at hd
  exact hd

/-- Every involution has precisely one fixed point on the ovoid. -/
public theorem suzukiOvoid_involution_unique_fixed (m : ℕ) (hm : 0 < m)
    (g : SuzukiMatrixGroup m) (hg : orderOf g = 2) :
    ∃! a : SuzukiOvoid m, g • a = a := by
  have hp : IsPGroup 2 (Subgroup.zpowers g) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, hg]
    exact dvd_refl 2
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) Q P
  have hgQ : g ∈ Q := hQ (Subgroup.mem_zpowers g)
  have hr : k * g * k⁻¹ ∈ SuzukiRootSubgroup m := by
    rw [← hP, ← hk]
    exact ⟨g, hgQ, rfl⟩
  have hgne : g ≠ 1 := by
    intro he
    simp [he] at hg
  have hrne : k * g * k⁻¹ ≠ 1 := by
    intro h
    apply hgne
    have h' := congrArg (fun x => k⁻¹ * x * k) h
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, one_mul] using h'
  have hiff (a : SuzukiOvoid m) :
      g • a = a ↔ a = k⁻¹ • suzukiOvoidInfinity m := by
    constructor
    · intro ha
      have hf : (k * g * k⁻¹) • (k • a) = k • a := by
        simp only [mul_smul, inv_smul_smul, ha]
      have he := (suzukiRootSubgroup_fixed_iff m hm _ hr hrne _).mp hf
      exact (eq_inv_smul_iff.mpr he)
    · rintro rfl
      have hf := suzukiRootSubgroup_fix_infinity m hm _ hr
      have he := congrArg (k⁻¹ • ·) hf
      simpa only [mul_smul, inv_smul_smul] using he
  exact ⟨_, (hiff _).mpr rfl, fun a ha => (hiff a).mp ha⟩

/-- The standard torus is the pointwise stabilizer of infinity and zero. -/
public theorem mem_suzukiSplitTorus_iff_fix_pair (m : ℕ) (g : SuzukiMatrixGroup m) :
    g ∈ SuzukiSplitTorus m ↔
      g • suzukiOvoidInfinity m = suzukiOvoidInfinity m ∧
      g • suzukiOvoidZero m = suzukiOvoidZero m := by
  constructor
  · intro hg
    obtain ⟨u, hu⟩ := (mem_suzukiSplitTorus_iff m g).mp hg
    constructor
    · apply Subtype.ext
      change (Matrix.GeneralLinearGroup.toLin g.val).toLinearEquiv • _ = _
      rw [hu]
      exact External.suzukiTorus_smul_infinity m u
    · apply Subtype.ext
      change (Matrix.GeneralLinearGroup.toLin g.val).toLinearEquiv • _ = _
      rw [hu]
      simpa only [suzukiOvoidZero, mul_zero] using External.suzukiTorus_smul_finite m
        (suzukiTits m) (suzukiTits_sq m) (suzukiTits_apply m) u 0 0
  · rintro ⟨hi, hz⟩
    exact External.suzukiMatrixGroup_mem_torus_of_fix_infinity_zero m
      (suzukiTits m) (suzukiTits_sq m) (suzukiTits_apply m) g
      (congrArg Subtype.val hi) (congrArg Subtype.val hz)

/-- Nonidentity torus elements act fixed-point-freely by conjugation on the
nonidentity root elements; this is the Frobenius property of the Borel. -/
public theorem suzukiRootSubgroup_eq_one_of_commute_split (m : ℕ) (hm : 0 < m)
    (t r : SuzukiMatrixGroup m) (ht : t ∈ SuzukiSplitTorus m) (htne : t ≠ 1)
    (hr : r ∈ SuzukiRootSubgroup m) (hcomm : Commute t r) : r = 1 := by
  by_contra hrne
  have htfix := (mem_suzukiSplitTorus_iff_fix_pair m t).mp ht
  have hrfix := suzukiRootSubgroup_fix_infinity m hm r hr
  have hthird : t • (r • suzukiOvoidZero m) = r • suzukiOvoidZero m := by
    rw [← mul_smul, hcomm.eq, mul_smul, htfix.2]
  have hzero : suzukiOvoidZero m ≠ r • suzukiOvoidZero m := by
    intro h
    exact (suzukiOvoidInfinity_ne_zero m).symm
      ((suzukiRootSubgroup_fixed_iff m hm r hr hrne _).mp h.symm)
  have hinf : suzukiOvoidInfinity m ≠ r • suzukiOvoidZero m := by
    intro h
    apply suzukiOvoidInfinity_ne_zero m
    apply (MulAction.injective r)
    exact hrfix.trans h
  exact suzukiOvoid_at_most_two_fixed m hm t htne _ _ _
    (suzukiOvoidInfinity_ne_zero m) hinf hzero htfix.1 htfix.2 hthird

/-- Every Borel element outside the root group is conjugate into the standard
split torus by a root element. The proof uses bijectivity of the commutator map
on the finite root group, rather than a classification of Suzuki tori. -/
public theorem suzukiBorelSubgroup_conjugate_into_split (m : ℕ) (hm : 0 < m)
    (b : SuzukiMatrixGroup m) (hb : b ∈ SuzukiBorelSubgroup m)
    (hbn : b ∉ SuzukiRootSubgroup m) :
    ∃ r : SuzukiRootSubgroup m,
      (r : SuzukiMatrixGroup m)⁻¹ * b * r ∈ SuzukiSplitTorus m := by
  have hprod : b ∈ (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) *
      (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (suzukiSplitTorus_le_normalizer_root m), ← suzukiBorelSubgroup_eq_sup]
    exact hb
  obtain ⟨f, hf, t, ht, hft⟩ := hprod
  have htne : t ≠ 1 := by
    intro h
    apply hbn
    have hfb : f = b := by simpa [h] using hft
    exact hfb ▸ hf
  have hn := suzukiSplitTorus_le_normalizer_root m ht
  let comm : SuzukiRootSubgroup m → SuzukiRootSubgroup m := fun r =>
    ⟨(r : SuzukiMatrixGroup m) * (t * (r : SuzukiMatrixGroup m)⁻¹ * t⁻¹),
      (SuzukiRootSubgroup m).mul_mem r.property
        ((Subgroup.mem_normalizer_iff.mp hn _).mp
          ((SuzukiRootSubgroup m).inv_mem r.property))⟩
  have hinj : Function.Injective comm := by
    intro r s hrs
    have heq : (r : SuzukiMatrixGroup m) * t * (r : SuzukiMatrixGroup m)⁻¹ =
        (s : SuzukiMatrixGroup m) * t * (s : SuzukiMatrixGroup m)⁻¹ := by
      apply mul_right_cancel (b := t⁻¹)
      simpa only [comm, mul_assoc] using congrArg Subtype.val hrs
    have hcom : Commute t ((s : SuzukiMatrixGroup m)⁻¹ * r) := by
      show t * ((s : SuzukiMatrixGroup m)⁻¹ * r) =
        ((s : SuzukiMatrixGroup m)⁻¹ * r) * t
      calc
        _ = (s : SuzukiMatrixGroup m)⁻¹ *
            ((s : SuzukiMatrixGroup m) * t * (s : SuzukiMatrixGroup m)⁻¹) * r := by group
        _ = (s : SuzukiMatrixGroup m)⁻¹ *
            ((r : SuzukiMatrixGroup m) * t * (r : SuzukiMatrixGroup m)⁻¹) * r := by rw [heq]
        _ = _ := by group
    have h1 := suzukiRootSubgroup_eq_one_of_commute_split m hm t _ ht htne
      ((SuzukiRootSubgroup m).mul_mem
        ((SuzukiRootSubgroup m).inv_mem s.property) r.property) hcom
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  obtain ⟨r, hr⟩ := (Finite.surjective_of_injective hinj) ⟨f, hf⟩
  have hrt : (r : SuzukiMatrixGroup m) * t * (r : SuzukiMatrixGroup m)⁻¹ = b := by
    calc
      _ = ((r : SuzukiMatrixGroup m) *
          (t * (r : SuzukiMatrixGroup m)⁻¹ * t⁻¹)) * t := by group
      _ = f * t := congrArg (fun x : SuzukiMatrixGroup m => x * t) (congrArg Subtype.val hr)
      _ = b := hft
  refine ⟨r, ?_⟩
  have heq : (r : SuzukiMatrixGroup m)⁻¹ * b * r = t := by
    rw [← hrt]
    group
  rw [heq]
  exact ht

/-- An element with an ovoid fixed point lies in a conjugate of the standard
root group or split torus. -/
public theorem suzukiOvoid_fixed_point_coverage (m : ℕ) (hm : 0 < m)
    (g : SuzukiMatrixGroup m) (hfix : ∃ a : SuzukiOvoid m, g • a = a) :
    ∃ k : SuzukiMatrixGroup m,
      k⁻¹ * g * k ∈ SuzukiRootSubgroup m ∨
      k⁻¹ * g * k ∈ SuzukiSplitTorus m := by
  obtain ⟨a, ha⟩ := hfix
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m)
    (suzukiOvoidInfinity m) a
  have hb : k⁻¹ * g * k ∈ SuzukiBorelSubgroup m := by
    rw [suzukiBorelSubgroup_eq_stabilizer m hm, MulAction.mem_stabilizer_iff]
    rw [mul_smul, mul_smul, hk, ha, ← hk, inv_smul_smul]
  by_cases hr : k⁻¹ * g * k ∈ SuzukiRootSubgroup m
  · exact ⟨k, Or.inl hr⟩
  · obtain ⟨r, hr⟩ := suzukiBorelSubgroup_conjugate_into_split m hm _ hb hr
    refine ⟨k * r, Or.inr ?_⟩
    simpa only [mul_inv_rev, mul_assoc] using hr

end BenderSuzuki.MatrixGroups

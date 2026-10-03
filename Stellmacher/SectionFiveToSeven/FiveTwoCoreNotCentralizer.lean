module

public import Stellmacher.SectionFiveToSeven.FiveTwoVKCentralCore
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer

/-!
# Assertion (7) in Stellmacher (5.2)

This module proves that the ambient image of `O₂(K)` is not contained in
the source centralizer `C₀=C_G(V)`.  Assuming the contrary, assertion (1)
puts `[V,K]` in `Z(O₂(K))`; the imported consequence of (3.5) then makes
the conjugation action of `K` on the elementary abelian two-group `V`
quadratic.

The effective image of a quadratic action on an elementary abelian
two-group is itself elementary abelian.  Hence the image of `K` in the
action of `K⊔B` on `V` is a normal two-group, while the image of the
two-group `B` is also a two-group.  The full action image is therefore a
two-group.  The full commutator identity `K=[K,B]`, applied to the action
kernel through the generic quotient normalizer calculation, forces `K` to
act trivially on `V`.  This contradicts the previously established
`K≰C₀`.

This is the action argument implicit in assertion (7) of Stellmacher (5.2),
Journal of Algebra 190 (1997), p. 29.
-/

namespace Stellmacher.SectionsFiveToSeven

open scoped IsMulCommutative commutatorElement

universe u v

private theorem commutatorAction₂_subgroup_conj_map_eq_52seven
    {X : Type*} [Group X] (N R : Subgroup X)
    (hRnormN : R ≤ Subgroup.normalizer N) :
    have : Subgroup.Normalizes R N := ⟨hRnormN⟩
    (commutatorAction₂ (A := R) (G := N)).map N.subtype =
      ⁅⁅N, R⁆, R⁆ := by
  classical
  let _ : Subgroup.Normalizes R N := ⟨hRnormN⟩
  let C : Subgroup N := commutatorAction (A := R) (G := N)
  let SC : Set N :=
    {x : N | ∃ r : R, ∃ n : N, n ∈ C ∧ x = n⁻¹ * (r • n)}
  let SX : Set X :=
    {x : X | ∃ r : R, ∃ n : N, n ∈ C ∧
      x = ⁅((n : X))⁻¹, (r : X)⁆}
  let SK : Set X :=
    {x : X | ∃ k ∈ ⁅N, R⁆, ∃ r ∈ R, ⁅k, r⁆ = x}
  have hCmap : C.map N.subtype = ⁅N, R⁆ := by
    simpa [C] using commutatorAction_subgroup_conj_map_eq_commutator N R hRnormN
  have himage : N.subtype '' SC = SX := by
    ext x
    constructor
    · rintro ⟨y, ⟨r, n, hn, rfl⟩, rfl⟩
      refine ⟨r, n, hn, ?_⟩
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        commutatorElement_def, mul_assoc]
    · rintro ⟨r, n, hn, rfl⟩
      refine ⟨n⁻¹ * (r • n), ⟨r, n, hn, rfl⟩, ?_⟩
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        commutatorElement_def, mul_assoc]
  have hsets : SX = SK := by
    ext x
    constructor
    · rintro ⟨r, n, hn, rfl⟩
      have hnmap : (n : X) ∈ ⁅N, R⁆ := by
        rw [← hCmap]
        exact Subgroup.mem_map_of_mem N.subtype hn
      exact ⟨(n : X)⁻¹, (⁅N, R⁆).inv_mem hnmap,
        (r : X), r.2, by simp⟩
    · rintro ⟨k, hk, r, hr, rfl⟩
      rw [← hCmap] at hk
      obtain ⟨n, hn, hnk⟩ := hk
      refine ⟨⟨r, hr⟩, n⁻¹, C.inv_mem hn, ?_⟩
      have hnk' : (n : X) = k := hnk
      subst k
      simp
  calc
    (commutatorAction₂ (A := R) (G := N)).map N.subtype
        = (Subgroup.closure SC).map N.subtype := by rfl
    _ = Subgroup.closure (N.subtype '' SC) := by
      simpa using MonoidHom.map_closure N.subtype SC
    _ = Subgroup.closure SX := by rw [himage]
    _ = Subgroup.closure SK := by rw [hsets]
    _ = ⁅⁅N, R⁆, R⁆ := by
      simp [SK, Subgroup.commutator_def]

private theorem range_toMulAut_elementary_two_of_quadratic_52seven
    {A : Type u} {V : Type v} [Group A] [Group V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]
    (hquadratic : commutatorAction₂ A V = ⊥) :
    IsElementaryAbelian 2 (MulDistribMulAction.toMulAut A V).range := by
  let _ : CommGroup V := IsMulCommutative.instCommGroup
  let rho : A →* MulAut V := MulDistribMulAction.toMulAut A V
  have hdelta_mem (a : A) (x : V) :
      x⁻¹ * (a • x) ∈ commutatorAction A V := by
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨a, x, rfl⟩
  have hfix_delta (a b : A) (x : V) :
      b • (x⁻¹ * (a • x)) = x⁻¹ * (a • x) := by
    let d : V := x⁻¹ * (a • x)
    have hd : d ∈ commutatorAction A V := hdelta_mem a x
    have hiter : d⁻¹ * (b • d) ∈ commutatorAction₂ A V :=
      Subgroup.subset_closure ⟨b, d, hd, rfl⟩
    have hiter_bot : d⁻¹ * (b • d) ∈ (⊥ : Subgroup V) := by
      rw [← hquadratic]
      exact hiter
    have hone : d⁻¹ * (b • d) = 1 := by simpa using hiter_bot
    have hd_eq : d = b • d := eq_of_inv_mul_eq_one hone
    simpa [d] using hd_eq.symm
  have hformula (a b : A) (x : V) :
      (b * a) • x = (b • x) * x⁻¹ * (a • x) := by
    have hfix := hfix_delta a b x
    have hmul := congrArg (fun z : V ↦ (b • x) * z) hfix
    simpa [smul_mul', smul_smul, mul_assoc] using hmul
  refine
    { toIsMulCommutative := ⟨⟨fun a b ↦ ?_⟩⟩
      exponent_dvd_p := ?_ }
  · rcases a with ⟨_, a, rfl⟩
    rcases b with ⟨_, b, rfl⟩
    apply Subtype.ext
    change rho a * rho b = rho b * rho a
    rw [← map_mul, ← map_mul]
    apply MulEquiv.ext
    intro x
    simp only [rho, MulDistribMulAction.toMulAut_apply]
    change (a * b) • x = (b * a) • x
    rw [hformula b a x, hformula a b x]
    ac_rfl
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro s
    rcases s with ⟨_, s, rfl⟩
    apply Subtype.ext
    change (rho s) ^ 2 = 1
    rw [← map_pow]
    apply MulEquiv.ext
    intro x
    simp only [rho, MulDistribMulAction.toMulAut_apply, MulAut.one_apply]
    change (s ^ 2) • x = x
    rw [pow_two, hformula s s x]
    have hsx2 : (s • x) ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) (s • x)
    have hx2 : x ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) x
    have hxinv : x⁻¹ = x :=
      inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hx2)
    calc
      (s • x) * x⁻¹ * (s • x) = (s • x) * (s • x) * x⁻¹ := by ac_rfl
      _ = x⁻¹ := by rw [← pow_two, hsx2, one_mul]
      _ = x := hxinv

/-- Under the source hypotheses of Stellmacher (5.2), the two-core of `K`
is not contained in the centralizer of the normal elementary subgroup `V`.
This is assertion (7). -/
public theorem five_two_twoCore_not_le_centralizer
    {G : Type u} [Group G] [Finite G]
    (B K M V C0 : Subgroup G)
    (hBKM : B ⊔ K ≤ M)
    (hVM : V ≤ M) (hVnormal : (V.subgroupOf M).Normal)
    (hVelem : IsElementaryAbelian 2 V)
    (hBp : IsPGroup 2 B)
    (hC0 : C0 = Subgroup.centralizer (V : Set G))
    (hKnotC0 : ¬ K ≤ C0)
    (hnorm : ∀ D : Subgroup G, IsPGroup 2 D →
      B ⊔ K ≤ Subgroup.normalizer (D : Set G) →
      D ≤ Subgroup.normalizer (K : Set G))
    (hcenterComm :
      ⁅(Subgroup.center (twoCoreIn K)).map (twoCoreIn K).subtype, K⁆ = ⊥)
    (hcomm : ⁅K, B⁆ = K) :
    ¬ twoCoreIn K ≤ C0 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcoreC0
  let _ : IsElementaryAbelian 2 V := hVelem
  have hVKcenter :
      ⁅V, K⁆ ≤ (Subgroup.center (twoCoreIn K)).map (twoCoreIn K).subtype :=
    five_two_commutator_le_twoCore_center B K M V C0 hBKM hVM hVnormal
      (IsElementaryAbelian.isPGroup 2 V) hC0 hcoreC0 hnorm
  have hquadraticAmbient : ⁅⁅V, K⁆, K⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hVKcenter le_rfl).trans hcenterComm.le
  have hMnormV : M ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mp hVnormal
  let L : Subgroup G := K ⊔ B
  have hLM : L ≤ M := by simpa [L, sup_comm] using hBKM
  have hLnormV : L ≤ Subgroup.normalizer (V : Set G) := hLM.trans hMnormV
  let _ : Subgroup.Normalizes L V := ⟨hLnormV⟩
  let phi : L →* MulAut V := MulDistribMulAction.toMulAut L V
  let KL : Subgroup L := K.subgroupOf L
  let BL : Subgroup L := B.subgroupOf L
  have hKLmap : KL.map L.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le (show K ≤ L from le_sup_left)
  have hBLmap : BL.map L.subtype = B :=
    Subgroup.map_subgroupOf_eq_of_le (show B ≤ L from le_sup_right)
  have hcommL : ⁅KL, BL⁆ = KL := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, hKLmap, hBLmap, hcomm]
  have hgen : KL ⊔ BL = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, hKLmap, hBLmap]
    have htopmap : (⊤ : Subgroup L).map L.subtype = L := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simpa [L] using htopmap.symm
  have hKLnormal : KL.Normal := by
    have htopNorm : (⊤ : Subgroup L) ≤ Subgroup.normalizer (KL : Set L) := by
      rw [← hgen]
      exact sup_le KL.le_normalizer
        (Subgroup.le_normalizer_iff_commutator_le_left.mpr hcommL.le)
    refine ⟨?_⟩
    intro n hn g
    exact (Subgroup.mem_normalizer_iff.mp (htopNorm (Subgroup.mem_top g)) n).mp hn
  let _ : KL.Normal := hKLnormal
  have hKnormV : K ≤ Subgroup.normalizer (V : Set G) :=
    le_sup_left.trans hLnormV
  let _ : Subgroup.Normalizes K V := ⟨hKnormV⟩
  let rhoK : K →* MulAut V := MulDistribMulAction.toMulAut K V
  have hquadraticK : commutatorAction₂ K V = ⊥ := by
    apply Subgroup.map_injective V.subtype_injective
    rw [commutatorAction₂_subgroup_conj_map_eq_52seven V K hKnormV]
    rw [hquadraticAmbient, Subgroup.map_bot]
  have hrhoKelem : IsElementaryAbelian 2 rhoK.range :=
    range_toMulAut_elementary_two_of_quadratic_52seven hquadraticK
  have hKLimage : KL.map phi = rhoK.range := by
    ext a
    constructor
    · rintro ⟨l, hl, rfl⟩
      let k : K := ⟨(l : G), hl⟩
      refine ⟨k, ?_⟩
      ext x
      rfl
    · rintro ⟨k, rfl⟩
      let l : L := ⟨(k : G), (show K ≤ L from le_sup_left) k.property⟩
      refine ⟨l, k.property, ?_⟩
      ext x
      rfl
  have hKLimageTwo : IsPGroup 2 (KL.map phi) := by
    rw [hKLimage]
    exact IsElementaryAbelian.isPGroup 2 rhoK.range
  have hBLtwo : IsPGroup 2 BL :=
    hBp.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
  have hBLimageTwo : IsPGroup 2 (BL.map phi) := hBLtwo.map phi
  have hBLnormKLimage :
      BL.map phi ≤ Subgroup.normalizer (KL.map phi : Set (MulAut V)) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    rw [← Subgroup.map_commutator, hcommL]
  have hImageTwo : IsPGroup 2 phi.range := by
    have hsupTwo : IsPGroup 2
        (KL.map phi ⊔ BL.map phi : Subgroup (MulAut V)) :=
      IsPGroup.to_sup_of_normal_left' (p := 2)
        hKLimageTwo hBLimageTwo hBLnormKLimage
    have himage : phi.range = KL.map phi ⊔ BL.map phi := by
      rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_sup]
    rwa [himage]
  have hquotientTwo : IsPGroup 2 (L ⧸ phi.ker) :=
    hImageTwo.of_equiv (QuotientGroup.quotientKerEquivRange phi).symm
  have hKLker : KL ≤ phi.ker :=
    Subgroup.le_normal_of_quotient_isPGroup_of_eq_commutator
      KL BL phi.ker hquotientTwo hcommL
  have hKcentralV : K ≤ Subgroup.centralizer (V : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    let kL : L := ⟨k, (show K ≤ L from le_sup_left) hk⟩
    have hkker : kL ∈ phi.ker := hKLker (show kL ∈ KL from hk)
    have hfix : phi kL = 1 := MonoidHom.mem_ker.mp hkker
    have hfixx := DFunLike.congr_fun hfix ⟨x, hx⟩
    have hconj : k * x * k⁻¹ = x := by
      simpa [phi, kL,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit]
        using congrArg Subtype.val hfixx
    have hmul := congrArg (fun y : G ↦ y * k) hconj
    simpa [mul_assoc] using hmul.symm
  exact hKnotC0 (by simpa [hC0] using hKcentralV)

end Stellmacher.SectionsFiveToSeven

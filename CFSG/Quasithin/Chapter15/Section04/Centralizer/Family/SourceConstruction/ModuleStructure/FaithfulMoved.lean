module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.BinaryNormalizer.SourcePair
public import Theory.ElementaryAbelian.GeneratorRank
/-!
# The faithful moved module and intrinsic double factors

For a member X of the source Y-family, the original image of X in M/O₂(M)
acts faithfully on [V(M),X]. The kernel argument is elementary: a cubic
binary automorphism fixing its own displacement is both quadratic and of odd
order, hence trivial. The centralizer equality of 15.4.11 then identifies
its kernel with that of the original projection.

Transporting the family's irreducibility to the same quotient allows the
faithful nine-on-sixteen calculation to construct its intrinsic cubic factors.
Their moved planes have order four, M permutes the quotient factors, and an
actual T-element exchanges their actual residual lifts. The marked version
retains the faithful action and planes for subsequent Baumann calculations.

These are the factor-construction and permutation parts of 15.4.12(6) and
15.4.18. Sylow-Baumann invariance and the reduced-module decompositions are
separate source obligations.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
15.4.12 and 15.4.18, printed pp.1160--1162.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure
open BinaryNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- The original ambient moved subgroup in source 15.4.12. -/
def movedModule (T M X : Subgroup G) : Subgroup G := ⁅localV T M,X⁆

private theorem cubic_binary_quadratic_trivial {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (a : MulAut V) (hcube : a ^ 3 = 1)
    (hfix : ∀ v, a (v⁻¹ * a v) = v⁻¹ * a v) : a = 1 := by
  have hsquare (v : V) : v * v = 1 := by
    simpa only [pow_two] using (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) v)
  have hinv (v : V) : v⁻¹ = v := inv_eq_of_mul_eq_one_left (hsquare v)
  have htwo (v : V) : a (a v) = v := by
    have hv := hfix v
    rw [map_mul, map_inv, hinv, hinv] at hv
    calc
      a (a v) = a v * (a v * a (a v)) := by rw [←mul_assoc, hsquare, one_mul]
      _ = a v * (v * a v) := by rw [hv]
      _ = v * (a v * a v) := by ac_rfl
      _ = v := by rw [hsquare, mul_one]
  ext v
  have hc := congrArg (fun b : MulAut V => b v) hcube
  change a (a (a v)) = v at hc
  rwa [htwo] at hc

theorem Input.moved_normalized {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) :
    M ≤ normalizer ((movedModule T M X : Subgroup G) : Set G) := by
  have hnX := (normal_subgroupOf_iff_le_normalizer h.member_le).mp h.normal
  intro m hm
  unfold movedModule
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (localV_normalized T M hm),
    mem_normalizer_iff_map_conj_eq.mp (hnX hm)]

theorem Input.moved_le {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) :
    movedModule T M X ≤ localV T M := by
  change ⁅localV T M,X⁆ ≤ localV T M
  have hh : X ≤ normalizer (localV T M : Set G) := fun x hx =>
    localV_normalized (T : Subgroup G) M (h.member_le hx)
  exact (le_normalizer_iff_commutator_le_left (H := X) (K := localV T M)).mp hh

omit [Finite G] in
private theorem elementary_of_le {V W : Subgroup G} [IsElementaryAbelian 2 V]
    (hWV : W ≤ V) : IsElementaryAbelian 2 W := by
  refine { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (show (x : G) * (y : G) = (y : G) * (x : G) from ?_)⟩⟩, exponent_dvd_p := ?_ }
  · exact congrArg Subtype.val (mul_comm (⟨x, hWV x.property⟩ : V) ⟨y, hWV y.property⟩)
  · exact (Monoid.exponent_dvd_of_monoidHom (inclusion hWV)
      (inclusion_injective hWV)).trans (IsElementaryAbelian.exponent_dvd_p 2 V)

theorem Input.moved_elementary {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) :
    IsElementaryAbelian 2 (movedModule T M X : Subgroup G) := by
  let : IsElementaryAbelian 2 (localV T M) := localV_elementary T M h.sylow_le
    (h.ambient.evenCharacteristic T M h.maximal h.sylow_le)
  exact elementary_of_le h.moved_le

private theorem Input.projection_kernel_centralizes {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) (x : X)
    (hx : memberProjection M X h.member_le x = 1) :
    (x : G) ∈ centralizer (localV T M : Set G) := by
  have hxq : quotientMap M (inclusion h.member_le x) = 1 := congrArg Subtype.val hx
  have hxcore : (x : G) ∈ M.pCoreIn 2 :=
    mem_map.mpr ⟨inclusion h.member_le x, (QuotientGroup.eq_one_iff _).mp hxq, rfl⟩
  rw [←localV_centralizer T M h.sylow_le h.center_centralizer] at hxcore
  exact hxcore.2

private theorem Input.moved_action_kernel {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) :
    (moduleConjugation X (movedModule T M X) (fun _x hx => h.moved_normalized (h.member_le hx))).ker =
      (memberProjection M X h.member_le).ker := by
  let V := localV T M
  let W : Subgroup G := movedModule T M X
  let a := moduleConjugation X V (fun _x hx => localV_normalized (T : Subgroup G) M (h.member_le hx))
  let b := moduleConjugation X W (fun _x hx => h.moved_normalized (h.member_le hx))
  let : IsElementaryAbelian 2 V := localV_elementary T M h.sylow_le
    (h.ambient.evenCharacteristic T M h.maximal h.sylow_le)
  let : IsElementaryAbelian 3 (image M X) := h.image_structure.1
  ext x
  change b x = 1 ↔ memberProjection M X h.member_le x = 1
  constructor
  · intro hb
    have hc : a x ^ 3 = 1 := by
      rw [←map_pow]
      ext v
      rw [moduleConjugation_val]
      have hp : memberProjection M X h.member_le (x ^ 3) = 1 := by
        rw [map_pow]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 3 (image M X)) _
      exact (mul_inv_eq_iff_eq_mul.mpr
        ((h.projection_kernel_centralizes (x ^ 3) hp) v v.property).symm)
    have ha : a x = 1 := by
      apply cubic_binary_quadratic_trivial _ hc
      intro v
      let d : W := ⟨(v : G)⁻¹ * ((x : G) * (v : G) * (x : G)⁻¹), by
        change (v : G)⁻¹ * ((x : G) * (v : G) * (x : G)⁻¹) ∈ ⁅V,X⁆
        simpa only [commutatorElement_def, inv_inv, mul_assoc] using
          (commutator_mem_commutator (V.inv_mem v.property) x.property)⟩
      have hd : b x d = d := by rw [hb]; rfl
      apply Subtype.ext
      change (x : G) * ((v : G)⁻¹ * ((x : G) * (v : G) * (x : G)⁻¹)) * (x : G)⁻¹ = _
      exact congrArg Subtype.val hd
    have hxC : (x : G) ∈ centralizer (V : Set G) := by
      intro v hv
      have hv' := congrArg (fun c : MulAut V => ((c ⟨v,hv⟩ : V) : G)) ha
      change (x : G) * v * (x : G)⁻¹ = v at hv'
      exact (mul_inv_eq_iff_eq_mul.mp hv').symm
    have hxcore := (localV_centralizer T M h.sylow_le h.center_centralizer).le
      ⟨h.member_le x.property,hxC⟩
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨c,hc,hcx⟩ := hxcore
    have he : c = inclusion h.member_le x := Subtype.ext hcx
    change inclusion h.member_le x ∈ pCore 2 M
    exact he ▸ hc
  · intro hx
    ext w
    rw [moduleConjugation_val]
    exact mul_inv_eq_iff_eq_mul.mpr
      (((h.projection_kernel_centralizes x hx) w (h.moved_le w.property)).symm)

/-- The actual odd image acts faithfully on its moved subgroup, with the
original quotient projection and the original conjugation action retained. -/
theorem Input.faithful_moved_action {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) :
    ∃ ρ : image M X →* MulAut (movedModule T M X : Subgroup G),
      Function.Injective ρ ∧ ∀ (x : X) (w : (movedModule T M X : Subgroup G)),
        (ρ (memberProjection M X h.member_le x) w : G) =
          (x : G) * (w : G) * (x : G)⁻¹ := by
  let b := moduleConjugation X (movedModule T M X) (fun _x hx => h.moved_normalized (h.member_le hx))
  let q := memberProjection M X h.member_le
  have hk : q.ker ≤ b.ker := h.moved_action_kernel.ge
  let ρ := q.liftOfSurjective (memberProjection_surjective M X h.member_le) ⟨b,hk⟩
  have he (x : X) : ρ (q x) = b x := by
    simp only [ρ, MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply]
  refine ⟨ρ, ?_, fun x w => ?_⟩
  · apply (MonoidHom.ker_eq_bot_iff ρ).mp
    apply eq_bot_iff.mpr
    intro z hz
    obtain ⟨x,rfl⟩ := memberProjection_surjective M X h.member_le z
    change ρ (q x) = 1 at hz
    rw [he] at hz
    exact h.moved_action_kernel.le hz
  · rw [he]
    rfl
/-- The source rank fixes the cardinality of the moved binary subgroup. -/
theorem Input.moved_card {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) :
    Nat.card (movedModule T M X : Subgroup G) = 2 ^ (2 * s) := by
  let W : Subgroup G := movedModule T M X
  let : IsElementaryAbelian 2 W := h.moved_elementary
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
  have hrn := IsElementaryAbelian.rank_le_of_card_le (p := 2) W hn.le
  have hnr : n ≤ Group.rank W := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [←hn]
    exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' W
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W)))
  have he : n = 2 * s := (Nat.le_antisymm hnr hrn).trans h.moved_rank
  exact hn.trans (congrArg (fun n => 2 ^ n) he)

/-- The family irreducibility is transported to the literal image in M/O₂(M),
using its actual conjugation by T. -/
theorem Input.image_irreducible {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input K T M X s) :
    ∀ D : Subgroup (image M X),
      (∀ t : (T : Subgroup G), D.map (imageConjugation M X
        ((normal_subgroupOf_iff_le_normalizer h.member_le).mp h.normal)
          (inclusion h.sylow_le t)).toMonoidHom = D) → D = ⊥ ∨ D = ⊤ := by
  intro D hD
  obtain ⟨e,he⟩ := member_quotient_compatible h.member_le h.normal
  have he' (x : X) : e (QuotientGroup.mk' (pCore 2 X) x) =
      memberProjection M X h.member_le x := Subtype.ext (he x)
  let A := D.comap e.toMonoidHom
  have hirr := member_quotient_irreducible T h.member h.quotient_elementary A
  have hstable : (T : Subgroup G) ≤ normalizer
      ((A.comap (QuotientGroup.mk' (pCore 2 X))).map X.subtype : Set G) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro z
    constructor
    · rintro ⟨x,hx,rfl⟩
      let tx : X := ⟨t * (x : G) * t⁻¹,
        (mem_normalizer_iff.mp (YFamily.invariant h.member ht) x).mp x.property⟩
      refine ⟨tx, ?_, rfl⟩
      change e (QuotientGroup.mk' (pCore 2 X) tx) ∈ D
      rw [he']
      have hxD : memberProjection M X h.member_le x ∈ D := by
        rw [←he']; exact hx
      have hmem := mem_map_of_mem (imageConjugation M X
        ((normal_subgroupOf_iff_le_normalizer h.member_le).mp h.normal)
          (inclusion h.sylow_le ⟨t,ht⟩)).toMonoidHom hxD
      rw [hD ⟨t,ht⟩] at hmem
      convert hmem using 1
      apply Subtype.ext
      change quotientMap M (inclusion h.member_le tx) =
        quotientMap M (⟨t,h.sylow_le ht⟩ : M) *
          quotientMap M (inclusion h.member_le x) *
          (quotientMap M (⟨t,h.sylow_le ht⟩ : M))⁻¹
      rw [←map_inv, ←map_mul, ←map_mul]
      rfl
    · intro hz
      obtain ⟨x,hx,hxz⟩ := hz
      let tx : X := ⟨t⁻¹ * (x : G) * t,
        by simpa only [inv_inv] using
          (mem_normalizer_iff.mp (YFamily.invariant h.member (T.inv_mem ht)) x).mp x.property⟩
      have htx : (tx : G) = z := by
        change (x : G) = t * z * t⁻¹ at hxz
        dsimp [tx]; rw [hxz]; group
      refine ⟨tx, ?_, htx⟩
      change e (QuotientGroup.mk' (pCore 2 X) tx) ∈ D
      rw [he']
      have hxD : memberProjection M X h.member_le x ∈ D := by
        rw [←he']; exact hx
      have hmem := mem_map_of_mem (imageConjugation M X
        ((normal_subgroupOf_iff_le_normalizer h.member_le).mp h.normal)
          (inclusion h.sylow_le ⟨t⁻¹,T.inv_mem ht⟩)).toMonoidHom hxD
      rw [hD ⟨t⁻¹,T.inv_mem ht⟩] at hmem
      convert hmem using 1
      apply Subtype.ext
      change quotientMap M (inclusion h.member_le tx) =
        quotientMap M (⟨t⁻¹,h.sylow_le (T.inv_mem ht)⟩ : M) *
          quotientMap M (inclusion h.member_le x) *
          (quotientMap M (⟨t⁻¹,h.sylow_le (T.inv_mem ht)⟩ : M))⁻¹
      rw [←map_inv, ←map_mul, ←map_mul]
      apply congrArg (quotientMap M)
      apply Subtype.ext
      simp only [coe_mul, coe_inv, inv_inv]
      rfl
  have hmap : A.map e.toMonoidHom = D := map_comap_eq_self_of_surjective e.surjective D
  rcases hirr hstable with ha | ha
  · left; rw [ha,Subgroup.map_bot] at hmap; exact hmap.symm
  · right; rw [ha,map_top_of_surjective e.toMonoidHom e.surjective] at hmap
    exact hmap.symm

/-- The marked factor pair on the actual moved module. No faithfulness,
irreducibility, factor-invariance or interchange premise is added to Input. -/
private theorem marked_double_factors_of_action
    (M X V T : Subgroup G) (hXM : X ≤ M) (hVM : V ≤ M) (hTM : T ≤ M)
    (hnX : (X.subgroupOf M).Normal) (hnV : (V.subgroupOf M).Normal)
    [IsElementaryAbelian 3 (image M X)] [IsElementaryAbelian 2 (⁅V,X⁆ : Subgroup G)]
    (hA : Nat.card (image M X) = 9) (hW : Nat.card (⁅V,X⁆ : Subgroup G) = 16)
    (hact : ∃ ρ : image M X →* MulAut (⁅V,X⁆ : Subgroup G),
      Function.Injective ρ ∧ ∀ (x : X) (w : (⁅V,X⁆ : Subgroup G)),
        (ρ (memberProjection M X hXM x) w : G) = (x : G) * (w : G) * (x : G)⁻¹)
    (hirr : ∀ D : Subgroup (image M X),
      (∀ t : T, D.map (imageConjugation M X
        ((normal_subgroupOf_iff_le_normalizer hXM).mp hnX)
          (inclusion hTM t)).toMonoidHom = D) → D = ⊥ ∨ D = ⊤) :
    ∃ ρ : image M X →* MulAut (⁅V,X⁆ : Subgroup G),
      Function.Injective ρ ∧
      (∀ (x : X) (w : (⁅V,X⁆ : Subgroup G)),
        (ρ (memberProjection M X hXM x) w : G) =
          (x : G) * (w : G) * (x : G)⁻¹) ∧
      letI := MulDistribMulAction.compHom (⁅V,X⁆ : Subgroup G) ρ
      ∃ P : FactorPair (A := image M X) (W := (⁅V,X⁆ : Subgroup G)),
        (∀ i, Nat.card (commutatorAction (P.line i) (⁅V,X⁆ : Subgroup G)) = 4) ∧
        IsCompl (commutatorAction (P.line false) (⁅V,X⁆ : Subgroup G))
          (commutatorAction (P.line true) (⁅V,X⁆ : Subgroup G)) ∧
        (∀ (g : M) i, ∃ j,
          (quotientFactors M X (⁅V,X⁆) P i).map
            (MulAut.conj (quotientMap M g)).toMonoidHom =
          quotientFactors M X (⁅V,X⁆) P j) ∧
        ∃ t ∈ (T : Subgroup G),
          (LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M
            (quotientMap M) (quotientFactors M X (⁅V,X⁆) P) false).map
            (MulAut.conj t).toMonoidHom =
          LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M
            (quotientMap M) (quotientFactors M X (⁅V,X⁆) P) true ∧
          (LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M
            (quotientMap M) (quotientFactors M X (⁅V,X⁆) P) true).map
            (MulAut.conj t).toMonoidHom =
          LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M
            (quotientMap M) (quotientFactors M X (⁅V,X⁆) P) false ∧
          t ∉ normalizer (LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M
            (quotientMap M) (quotientFactors M X (⁅V,X⁆) P) false : Set G) := by
  obtain ⟨ρ,hfaith,hρ⟩ := hact
  exact ⟨ρ,hfaith,hρ,source_residual_pair M X V T hXM hVM hTM hnX hnV
    hA hW ρ hfaith hρ hirr⟩

/-- The marked factor pair on the actual moved module. No faithfulness,
irreducibility, factor-invariance or interchange premise is added to Input. -/
theorem Input.marked_double_factors {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} (h : Input K T M X 2) :
    ∃ ρ : image M X →* MulAut (movedModule T M X : Subgroup G),
      Function.Injective ρ ∧
      (∀ (x : X) (w : (movedModule T M X : Subgroup G)),
        (ρ (memberProjection M X h.member_le x) w : G) =
          (x : G) * (w : G) * (x : G)⁻¹) ∧
      letI := MulDistribMulAction.compHom (movedModule T M X : Subgroup G) ρ
      ∃ P : FactorPair (A := image M X) (W := (movedModule T M X : Subgroup G)),
        (∀ i, Nat.card (commutatorAction (P.line i) (movedModule T M X : Subgroup G)) = 4) ∧
        IsCompl (commutatorAction (P.line false) (movedModule T M X : Subgroup G))
          (commutatorAction (P.line true) (movedModule T M X : Subgroup G)) ∧
        (∀ (g : M) i, ∃ j,
          (quotientFactors M X (movedModule T M X) P i).map
            (MulAut.conj (quotientMap M g)).toMonoidHom =
          quotientFactors M X (movedModule T M X) P j) ∧
        ∃ t ∈ (T : Subgroup G),
          (LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M
            (quotientMap M) (quotientFactors M X (movedModule T M X) P) false).map
            (MulAut.conj t).toMonoidHom =
          LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M
            (quotientMap M) (quotientFactors M X (movedModule T M X) P) true ∧
          (LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M
            (quotientMap M) (quotientFactors M X (movedModule T M X) P) true).map
            (MulAut.conj t).toMonoidHom =
          LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M
            (quotientMap M) (quotientFactors M X (movedModule T M X) P) false ∧
          t ∉ normalizer (LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M
            (quotientMap M) (quotientFactors M X (movedModule T M X) P) false : Set G) := by
  let : IsElementaryAbelian 3 (image M X) := h.image_structure.1
  let : IsElementaryAbelian 2 (⁅localV T M,X⁆ : Subgroup G) := h.moved_elementary
  have hVM : localV T M ≤ M := localV_le (T : Subgroup G) M
  have hnV : ((localV T M).subgroupOf M).Normal :=
    normal_subgroupOf_of_le_normalizer (localV_normalized (T : Subgroup G) M)
  have hA : Nat.card (image M X) = 9 := by simpa using h.image_structure.2
  have hW : Nat.card (⁅localV T M,X⁆ : Subgroup G) = 16 := by simpa [movedModule] using h.moved_card
  exact marked_double_factors_of_action M X (localV T M) (T : Subgroup G)
    h.member_le hVM h.sylow_le h.normal hnV hA hW
    h.faithful_moved_action h.image_irreducible

/-- The quotient factors, their M-permutation and the actual T-interchange,
ready for the residual-lift consumer. -/
theorem Input.double_quotient_factors {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} (h : Input K T M X 2) :
    ∃ A : Bool → Subgroup (CoreQuotient M),
      (∀ i, Nat.card (A i) = 3) ∧ Function.Injective A ∧
      A false ⊔ A true = image M X ∧
      (∀ (g : M) i, ∃ j,
        (A i).map (MulAut.conj (quotientMap M g)).toMonoidHom = A j) ∧
      ∃ t ∈ (T : Subgroup G),
        (LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M
          (quotientMap M) A false).map (MulAut.conj t).toMonoidHom =
        LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M (quotientMap M) A true ∧
        (LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M
          (quotientMap M) A true).map (MulAut.conj t).toMonoidHom =
        LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M (quotientMap M) A false ∧
        t ∉ normalizer (LocalSetup.TwoFactors.SourceFactors.Permutation.liftedFactors M
          (quotientMap M) A false : Set G) := by
  obtain ⟨ρ,_,_,P,_,_,hperm,hswap⟩ := h.marked_double_factors
  let _ := MulDistribMulAction.compHom (movedModule T M X : Subgroup G) ρ
  obtain ⟨hcard,hinj,hgen⟩ := quotientFactors_structure M X (movedModule T M X) P
  exact ⟨quotientFactors M X (movedModule T M X) P,hcard,hinj,hgen,hperm,hswap⟩

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure

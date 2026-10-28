module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.MarkedPairedRadicals
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CoreMatrixAction
public import Theory.LinearAlgebra.ZModFourDeterminantObstruction

/-!
# Rank-two action of the actual paired radicals

The determinant-one action on the original cyclic-four core rules out a
commuting pair outside the common plane. No involution-class catalogue or
replacement model is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private noncomputable def coordinates (h : TypeAt z V) :
    (normalizer (V : Set G)).pCoreIn 2 ≃* (Fin 3 → Multiplicative (ZMod 4)) :=
  ((pCore 2 (normalizer (V : Set G))).equivMapOfInjective
    (normalizer (V : Set G)).subtype (normalizer (V : Set G)).subtype_injective).symm.trans
    ((MulEquiv.subgroupCongr h.normalizer_fitting.symm).trans h.normalizer_core.some)

private theorem core_abelian (h : TypeAt z V) :
    IsMulCommutative ((normalizer (V : Set G)).pCoreIn 2) :=
  ⟨⟨fun a b => (coordinates h).injective (by simp only [map_mul, mul_comm])⟩⟩

private theorem ambient_seed_le_core (h : TypeAt z V) :
    V ≤ (normalizer (V : Set G)).pCoreIn 2 := by
  change V ≤ (pCore 2 (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype
  rw [← h.normalizer_fitting]
  exact h.seed_le_normalizer_core

private theorem core_square_one (h : TypeAt z V) (q : G)
    (hq : q ∈ (normalizer (V : Set G)).pCoreIn 2) (hq2 : q ^ 2 = 1) : q ∈ V := by
  obtain ⟨qM, hqM, heq⟩ := hq
  have hqV : qM ∈ V.subgroupOf (normalizer (V : Set G)) := by
    rw [h.seed_eq_omega_normalizer_core]
    refine ⟨⟨qM, hqM⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    change (qM : G) ^ 2 = 1
    rwa [show (qM : G) = q from heq]
  exact heq ▸ hqV

private theorem core_square_seed (h : TypeAt z V) (q : G)
    (hq : q ∈ (normalizer (V : Set G)).pCoreIn 2) : q ^ 2 ∈ V := by
  apply core_square_one h _ (pow_mem hq 2)
  have he : ∀ t : Multiplicative (ZMod 4), (t ^ 2) ^ 2 = 1 := by decide +kernel
  have hh : ((⟨q, hq⟩ : (normalizer (V : Set G)).pCoreIn 2) ^ 2) ^ 2 = 1 := by
    apply (coordinates h).injective
    simp only [map_pow, map_one]
    exact funext fun i => he (coordinates h ⟨q, hq⟩ i)
  exact congrArg Subtype.val hh

private theorem core_normalized (_h : TypeAt z V) :
    normalizer (V : Set G) ≤ normalizer ((normalizer (V : Set G)).pCoreIn 2 : Set G) := by
  have hh := (pCore 2 (normalizer (V : Set G))).le_normalizer_map
    (normalizer (V : Set G)).subtype
  rw [(pCore 2 (normalizer (V : Set G))).normalizer_eq_top,
    ← MonoidHom.range_eq_map, range_subtype] at hh
  exact hh

private theorem fixed_seed (h : TypeAt z V) (W : Subgroup G)
    (hWV : W ≤ V) (hW4 : Nat.card W = 4) (a : G)
    (haC : a ∈ centralizer (W : Set G))
    (haP : a ∉ (normalizer (V : Set G)).pCoreIn 2)
    (v : G) (hv : v ∈ V) : Commute a v ↔ v ∈ W := by
  let := h.elementary
  constructor
  · intro hav
    by_contra hvW
    have hvN : v ∈ normalizer (W : Set G) := centralizer_le_normalizer _
      (fun w hw => setLike_mul_comm (hWV hw) hv)
    have he : W ⊔ zpowers v = V := by
      apply eq_of_le_of_card_ge (sup_le hWV (zpowers_le.mpr hv))
      rw [card_sup_zpowers_of_normalizing_involution W v
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv) hvW hvN, hW4, h.seed_card]
    apply haP
    change a ∈ (pCore 2 (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype
    rw [← h.seed_centralizer]
    have hh : W ⊔ zpowers v ≤ involutionCentralizer a :=
      sup_le (fun w hw => mem_centralizer_singleton_iff.mpr (haC w hw))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hav.eq.symm))
    intro w hw
    exact mem_centralizer_singleton_iff.mp (hh (he.symm ▸ hw))
  · exact fun hvW => (haC v hvW).symm

private theorem displacement_core (h : TypeAt z V) (a d : G)
    (ha : a ∈ normalizer (V : Set G))
    (hd : d ∈ (normalizer (V : Set G)).pCoreIn 2) :
    ⁅a, d⁆ ∈ (normalizer (V : Set G)).pCoreIn 2 := by
  exact mul_mem ((mem_normalizer_iff.mp (core_normalized h ha) d).mp hd) (inv_mem hd)

private theorem displacement_square (h : TypeAt z V) (a d : G)
    (ha : a ∈ normalizer (V : Set G))
    (hd : d ∈ (normalizer (V : Set G)).pCoreIn 2) :
    ⁅a, d⁆ ^ 2 = ⁅a, d ^ 2⁆ := by
  let := core_abelian h
  have hc : Commute (a * d * a⁻¹) d⁻¹ := setLike_mul_comm
    ((mem_normalizer_iff.mp (core_normalized h ha) d).mp hd) (inv_mem hd)
  rw [commutatorElement_def, hc.mul_pow]
  simp only [commutatorElement_def, pow_two]
  group

omit [Finite G] in
private theorem displacement_fixed (a d : G) (ha2 : a ^ 2 = 1)
    (hd2 : ⁅a, d⁆ ^ 2 = 1) : Commute a ⁅a, d⁆ := by
  have ha : a * a = 1 := by simpa only [pow_two] using ha2
  have hd : ⁅a, d⁆⁻¹ = ⁅a, d⁆ := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hd2)
  apply mul_inv_eq_iff_eq_mul.mp
  calc
    a * ⁅a, d⁆ * a⁻¹ = ⁅a, d⁆⁻¹ := by
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
      simp only [commutatorElement_def, mul_inv_rev, inv_inv, hai]
      simp only [← mul_assoc, ha, one_mul]
    _ = ⁅a, d⁆ := hd

private theorem plane_displacement (h : TypeAt z V) (W : Subgroup G)
    (hWV : W ≤ V) (hW4 : Nat.card W = 4) (a d : G)
    (haC : a ∈ centralizer (W : Set G)) (ha2 : a ^ 2 = 1)
    (hd : d ∈ (normalizer (V : Set G)).pCoreIn 2) (hdW : d ^ 2 ∈ W) :
    ⁅a, d⁆ ∈ W := by
  have haM := h.plane_centralizer_le_normalizer W hWV hW4 haC
  by_cases haP : a ∈ (normalizer (V : Set G)).pCoreIn 2
  · let := core_abelian h
    rw [(show Commute a d from setLike_mul_comm haP hd).commutator_eq]
    exact one_mem _
  have hds : ⁅a, d⁆ ^ 2 = 1 := by
    rw [displacement_square h a d haM hd]
    exact (show Commute a (d ^ 2) from (haC _ hdW).symm).commutator_eq
  exact (fixed_seed h W hWV hW4 a haC haP _
    (core_square_one h _ (displacement_core h a d haM hd) hds)).mp
      (displacement_fixed a d ha2 hds)

private theorem ambient_matrix (h : TypeAt z V) (a : G)
    (ha : a ∈ normalizer (V : Set G)) :
    ∃ e : (normalizer (V : Set G)).pCoreIn 2 ≃* Multiplicative (Fin 3 → ZMod 4),
    ∃ X : Matrix (Fin 3) (Fin 3) (ZMod 4), X.det = 1 ∧
      ∀ q r : (normalizer (V : Set G)).pCoreIn 2,
        a * (q : G) * a⁻¹ = r → X.mulVec (e q).toAdd = (e r).toAdd := by
  let M := normalizer (V : Set G)
  let P := pCore 2 M
  let d : P ≃* M.pCoreIn 2 := P.equivMapOfInjective M.subtype M.subtype_injective
  let e : P ≃* Multiplicative (Fin 3 → ZMod 4) :=
    (MulEquiv.subgroupCongr h.normalizer_fitting.symm).trans
      (h.normalizer_core.some.trans (MulEquiv.funMultiplicative (Fin 3) (ZMod 4)).symm)
  let aM : M := ⟨a, ha⟩
  refine ⟨d.symm.trans e, h.coreMatrixAction e aM, h.coreMatrixAction_det e aM, ?_⟩
  intro q r hqr
  have hd (x : M.pCoreIn 2) : (((d.symm x : P) : M) : G) = x :=
    congrArg Subtype.val (d.apply_symm_apply x)
  have heq : MulAut.conjNormal aM (d.symm q) = d.symm r := by
    apply Subtype.ext
    apply Subtype.ext
    change a * (((d.symm q : P) : M) : G) * a⁻¹ = (((d.symm r : P) : M) : G)
    rw [hd, hd]
    exact hqr
  exact (h.coreMatrixAction_apply e aM (d.symm q)).trans (congrArg (fun x => (e x).toAdd) heq)

private theorem outside_pair_not_commute (h : TypeAt z V) (W A : Subgroup G)
    [IsElementaryAbelian 2 A] (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (p : G) (hp : p ∈ (normalizer (V : Set G)).pCoreIn 2) (hpW : p ^ 2 ∉ W)
    (a b : G) (ha : a ∈ A) (hb : b ∈ A) (haW : a ∉ W) (hbW : b ∉ W) :
    ¬ Commute a (p * b * p⁻¹) := by
  let P := (normalizer (V : Set G)).pCoreIn 2
  let := core_abelian h
  have hAM := hAC.trans (h.plane_centralizer_le_normalizer W hWV hW4)
  have haP : a ∉ P := fun hh => haW (hAP ▸ (show a ∈ A ⊓ P from ⟨ha, hh⟩))
  have hbP : b ∉ P := fun hh => hbW (hAP ▸ (show b ∈ A ⊓ P from ⟨hb, hh⟩))
  have ha2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have hb2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
  have hab : Commute a b := setLike_mul_comm ha hb
  let u : P := ⟨⁅a,p⁆, displacement_core h a p (hAM ha) hp⟩
  let v : P := ⟨⁅b,p⁆, displacement_core h b p (hAM hb) hp⟩
  let q : P := ⟨p, hp⟩
  have hsW (s : G) (hs : s ∈ A) : ⁅s,p⁆ ^ 2 ∈ W := by
    rw [displacement_square h s p (hAM hs) hp]
    apply plane_displacement h W hWV hW4 s (p ^ 2) (hAC hs)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) s hs) (pow_mem hp 2)
    let := h.elementary
    rw [elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (core_square_seed h p hp)]
    exact one_mem _
  have huW : (u : G) ^ 2 ∈ W := hsW a ha
  have hvW : (v : G) ^ 2 ∈ W := hsW b hb
  have hs1 (s : G) (hs : s ∈ A) (hsP : s ∉ P) : ⁅s,p⁆ ^ 2 ≠ 1 := by
    intro he
    rw [displacement_square h s p (hAM hs) hp] at he
    exact hpW ((fixed_seed h W hWV hW4 s (hAC hs) hsP _ (core_square_seed h p hp)).mp
      (commutatorElement_eq_one_iff_commute.mp he))
  have hu1 : u ^ 2 ≠ 1 := fun he => hs1 a ha haP (congrArg Subtype.val he)
  have hv1 : v ^ 2 ≠ 1 := fun he => hs1 b hb hbP (congrArg Subtype.val he)
  intro hac
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha2)
  have hau : a * (u : G) * a⁻¹ = (u : G)⁻¹ := by
    change a * ⁅a,p⁆ * a⁻¹ = ⁅a,p⁆⁻¹
    simp only [commutatorElement_def, mul_inv_rev, inv_inv, hai]
    have haa : a * a = 1 := by simpa only [pow_two] using ha2
    simp only [← mul_assoc, haa, one_mul]
  have hav : a * (v : G) * a⁻¹ = v := by
    have hc : Commute a (⁅b,p⁆⁻¹) := by
      rw [commutatorElement_inv]
      have hh := hac.mul_right hab.inv_right
      simpa only [commutatorElement_def, mul_assoc] using hh
    exact mul_inv_eq_iff_eq_mul.mpr (by simpa only [v, inv_inv] using hc.inv_right.eq)
  have hap : a * p * a⁻¹ = (u : G) * p := by
    simp only [u, commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
  have huv : u ^ 2 ≠ v ^ 2 := by
    intro he
    have heG : ⁅a,p⁆ ^ 2 = ⁅b,p⁆ ^ 2 := congrArg Subtype.val he
    rw [displacement_square h a p (hAM ha) hp,
      displacement_square h b p (hAM hb) hp] at heG
    have habp : Commute (a * b) (p ^ 2) := by
      have hec : a * p ^ 2 * a⁻¹ = b * p ^ 2 * b⁻¹ :=
        mul_right_cancel (show a * p ^ 2 * a⁻¹ * (p ^ 2)⁻¹ =
          b * p ^ 2 * b⁻¹ * (p ^ 2)⁻¹ from heG)
      apply mul_inv_eq_iff_eq_mul.mp
      calc
        (a * b) * p ^ 2 * (a * b)⁻¹ = a * (b * p ^ 2 * b⁻¹) * a⁻¹ := by group
        _ = a * (a * p ^ 2 * a⁻¹) * a⁻¹ := by rw [← hec]
        _ = p ^ 2 := by
          rw [hai]
          have haa : a * a = 1 := by simpa only [pow_two] using ha2
          calc
            a * (a * p ^ 2 * a) * a = (a*a) * p^2 * (a*a) := by group
            _ = p^2 := by rw [haa, one_mul, mul_one]
    have habP : a * b ∈ P := by
      by_contra hn
      exact hpW ((fixed_seed h W hWV hW4 (a*b) (hAC (mul_mem ha hb)) hn _
        (core_square_seed h p hp)).mp habp)
    have hec : Commute (a * b) p := setLike_mul_comm habP hp
    have heuv : u = v := by
      apply Subtype.ext
      change ⁅a,p⁆ = ⁅b,p⁆
      have h := hec.eq
      have hh : b * p * b⁻¹ = a * p * a⁻¹ := by
        calc
          b * p * b⁻¹ = a⁻¹ * ((a*b)*p*(a*b)⁻¹) * a := by group
          _ = a⁻¹ * p * a := by rw [h, mul_inv_cancel_right]
          _ = a * p * a⁻¹ := by rw [hai]
      simp only [commutatorElement_def]
      rw [hh]
    have hvu : a * (u : G) * a⁻¹ = u := by simpa only [← heuv] using hav
    have hueq : (u : G) = (u : G)⁻¹ := hvu.symm.trans hau
    apply hu1
    apply Subtype.ext
    change (u : G) ^ 2 = 1
    rw [pow_two]
    calc
      (u : G) * u = (u : G)⁻¹ * u := congrArg (fun x : G => x * u) hueq
      _ = 1 := inv_mul_cancel _
  obtain ⟨e, X, hX, hact⟩ := ambient_matrix h a (hAM ha)
  have huX : X.mulVec (e u).toAdd = -(e u).toAdd := by
    simpa only [map_inv, toAdd_inv] using hact u u⁻¹ hau
  have hvX : X.mulVec (e v).toAdd = (e v).toAdd := hact v v hav
  have hpX : X.mulVec (e q).toAdd = (e q).toAdd + (e u).toAdd := by
    have hh := hact q (u*q) hap
    simpa only [map_mul, toAdd_mul, add_comm] using hh
  have hinj : Function.Injective (fun r : P => (e r).toAdd) :=
    fun _ _ hh => e.injective (congrArg Multiplicative.ofAdd hh)
  have hd (r : P) : (e (r ^ 2)).toAdd = (e r).toAdd + (e r).toAdd := by
    simp only [pow_two, map_mul, toAdd_mul]
  have h1 : (e 1).toAdd = 0 := by rw [map_one]; rfl
  apply ZModFourDeterminantObstruction.no_negated_fixed_shear X (e u).toAdd (e v).toAdd
    (e q).toAdd hX huX hvX hpX
  · exact fun he => hu1 (hinj (by change (e (_^2)).toAdd = (e 1).toAdd; rwa [hd, h1]))
  · exact fun he => hv1 (hinj (by change (e (_^2)).toAdd = (e 1).toAdd; rwa [hd, h1]))
  · exact fun he => huv (hinj (by change (e (u^2)).toAdd = (e (v^2)).toAdd; rwa [hd, hd]))
  · intro he
    have hh := hinj (show (e (q^2)).toAdd = (e 1).toAdd by rwa [hd, h1])
    apply hpW
    have hhG : p ^ 2 = 1 := congrArg Subtype.val hh
    rw [hhG]
    exact W.one_mem
  · intro he
    have hh := hinj (show (e (q^2)).toAdd = (e (u^2)).toAdd by rwa [hd, hd])
    apply hpW
    have hhG : p ^ 2 = (u : G) ^ 2 := congrArg Subtype.val hh
    rwa [hhG]
  · intro he
    have hh := hinj (show (e (q^2)).toAdd = (e (v^2)).toAdd by rwa [hd, hd])
    apply hpW
    have hhG : p ^ 2 = (v : G) ^ 2 := congrArg Subtype.val hh
    rwa [hhG]
  · intro he
    have hh := hinj (show (e (q^2)).toAdd = (e (u^2*v^2)).toAdd by
      simpa only [hd, map_mul, toAdd_mul] using he)
    apply hpW
    have hhG : p ^ 2 = (u : G) ^ 2 * (v : G) ^ 2 := congrArg Subtype.val hh
    rw [hhG]
    exact W.mul_mem huW hvW

/-- Every element of the conjugate radical outside the common plane fixes
exactly that plane in the original radical. -/
theorem TypeAt.paired_plane_radical_centralizer (h : TypeAt z V) (W A : Subgroup G)
    [IsElementaryAbelian 2 A] (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hWA : W ≤ A) (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (p : G) (hp : p ∈ (normalizer (V : Set G)).pCoreIn 2) (hpW : p ^ 2 ∉ W)
    (b : G) (hb : b ∈ A.map (MulAut.conj p).toMonoidHom) (hbW : b ∉ W) :
    A ⊓ involutionCentralizer b = W := by
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  have hWP : W ≤ (normalizer (V : Set G)).pCoreIn 2 := hWV.trans (ambient_seed_le_core h)
  have hpfix (w : G) (hw : w ∈ W) : Commute p w := by
    let := core_abelian h
    exact setLike_mul_comm hp (hWP hw)
  have hb₀W : b₀ ∉ W := by
    intro hh
    apply hbW
    change p * b₀ * p⁻¹ ∈ W
    rwa [(hpfix b₀ hh).eq, mul_inv_cancel_right]
  apply le_antisymm
  · rintro a ⟨ha, hab⟩
    by_contra haW
    exact outside_pair_not_commute h W A hWV hW4 hAC hAP p hp hpW a b₀ ha hb₀ haW hb₀W
      (show Commute a (p * b₀ * p⁻¹) from mem_centralizer_singleton_iff.mp hab)
  · intro w hw
    refine ⟨hWA hw, mem_centralizer_singleton_iff.mpr ?_⟩
    change w * (p * b₀ * p⁻¹) = (p * b₀ * p⁻¹) * w
    exact (((hpfix w hw).mul_left (show Commute b₀ w from (hAC hb₀ w hw).symm)).mul_left
      (hpfix w hw).inv_left).eq.symm

/-- The original paired-radical construction retains exact rank-two fixed
spaces, together with its point-core and common-normalizer markings. -/
theorem TypeAt.exists_rank_two_paired_plane_radicals (h : TypeAt z V) :
    ∃ (W A B : Subgroup G) (p : G), W ≤ V ∧ Nat.card W = 4 ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 16 ∧
      p ∈ (normalizer (V : Set G)).pCoreIn 2 ∧ p ^ 2 ∉ W ∧
      B = A.map (MulAut.conj p).toMonoidHom ∧
      A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      centralizer (A : Set G) = A ∧ centralizer (B : Set G) = B ∧
      A ⊓ B = W ∧ ⁅A, B⁆ ≤ W ∧
      A ≤ normalizer (B : Set G) ∧ B ≤ normalizer (A : Set G) ∧
      Nat.card (A ⊔ B : Subgroup G) = 64 ∧
      A ⊔ B ≤ centralizer (W : Set G) ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ B, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ A, x ≠ 1 → Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      (∀ x ∈ B, x ≠ 1 → Nat.card (B ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      normalizer (A : Set G) ⊓ normalizer (B : Set G) =
        normalizer (A : Set G) ⊓ normalizer (W : Set G) ∧
      (∀ b ∈ B, b ∉ W → A ⊓ involutionCentralizer b = W) := by
  obtain ⟨W, A, B, p, hWV, hW4, hAE, hA16, hBE, hB16, hp, hpW, hB,
    hAP, hBP, hCA, hCB, hi, hcomm, hAB, hBA, h64, hC, hpureA, hpureB,
    hpointsA, hpointsB, hpairN⟩ := h.exists_point_marked_paired_plane_radicals
  let := hAE
  have hWA : W ≤ A := hi ▸ (show A ⊓ B ≤ A from inf_le_left)
  have hAC : A ≤ centralizer (W : Set G) := le_sup_left.trans hC
  refine ⟨W, A, B, p, hWV, hW4, hAE, hA16, hBE, hB16, hp, hpW, hB,
    hAP, hBP, hCA, hCB, hi, hcomm, hAB, hBA, h64, hC, hpureA, hpureB,
    hpointsA, hpointsB, hpairN, ?_⟩
  intro b hb hbW
  exact h.paired_plane_radical_centralizer W A hWV hW4 hWA hAC hAP p hp hpW b
    (hB ▸ hb) hbW

end CFSG.Quasithin.HigmanSims

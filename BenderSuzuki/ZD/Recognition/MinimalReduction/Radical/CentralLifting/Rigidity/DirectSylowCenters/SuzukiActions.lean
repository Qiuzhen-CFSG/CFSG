module

public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry
public import Mathlib.GroupTheory.Abelianization.Defs
public import BenderSuzuki.PFAppendixIII.FrobeniusBilinear
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.Module.ZMod
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.DirectSylowCenters.ModelActions

/-!
# Actual Suzuki torus actions for perfect central covers

The standard root Sylow of Sz(2^(2m+1)), m ≥ 1, satisfies the intrinsic
Sylow-center action criterion. The actual torus acts by
(a,b) ↦ (ka,kθ(k)b). Bijectivity of the twisted norm gives transitivity
on the nonidentity center; a primitive torus element has odd period and
fixes no nonidentity central element.

The root derived subgroup equals its center, so every binary bihomomorphism
factors through the first coordinate in both arguments. After embedding its
values into the coordinate field, the Frobenius expansion would require
2^(2m+1)-1 to divide 2^i+2^j. The elementary bound and parity argument below
exclude this for all i,j < 2m+1, including m = 1 and without alternation.

The final application uses the original perfect central double cover, model
isomorphism and arbitrary covering Sylow, via the generic transfer criterion.
No multiplier or cover classification is an input.

Sources: Huppert--Blackburn, Finite Groups III, XI.3.1 and XI.3.3;
an alternative proof of the Sylow-center conclusion of GLS4, Chapter 4,
Lemma 2.8(c), `refs/KGroup/GLS4/Chapter4.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.DirectSylowCenters.SuzukiActions
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII Subgroup

abbrev Field (m : ℕ) := BinaryGaloisField (2 * m + 1)

def rootPoint (m : ℕ) (a b : Field m) : SuzukiRootSubgroup m :=
  ⟨⟨SuzukiRootGL m a b, suzukiRootClosure_le m (subset_closure ⟨a,b,rfl⟩)⟩,
    subset_closure ⟨a,b,rfl⟩⟩

theorem rootPoint_mul (m : ℕ) (hm : 0 < m) (a b c d : Field m) :
    rootPoint m a b * rootPoint m c d =
      rootPoint m (a + c) (b + d + a * suzukiTits m c) := by
  apply Subtype.ext
  apply Subtype.ext
  exact (External.huppert_blackburn_XI_3_1 m hm (suzukiTits m)
    (suzukiTits_sq m)).2.2.2.2.2.2.2.2.1 a b c d

theorem rootPoint_zero (m : ℕ) : rootPoint m 0 0 = 1 :=
  Subtype.ext (Subtype.ext (External.suzukiRootGL_zero_zero m))

theorem rootPoint_surjective (m : ℕ) (x : SuzukiRootSubgroup m) :
    ∃ a b, x = rootPoint m a b := by
  obtain ⟨a,b,h⟩ := (mem_suzukiRootSubgroup_iff m x.val).mp x.property
  exact ⟨a,b,Subtype.ext (Subtype.ext h)⟩

theorem root_commutator_eq_center (m : ℕ) (hm : 0 < m) :
    commutator (SuzukiRootSubgroup m) = center (SuzukiRootSubgroup m) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hc,_⟩ :=
    External.huppert_blackburn_XI_3_1 m hm (suzukiTits m) (suzukiTits_sq m)
  change commutator (SuzukiRootClosure m) = center (SuzukiRootClosure m) at hc
  let e : SuzukiRootSubgroup m ≃* SuzukiRootClosure m :=
    subgroupOfEquivOfLe (suzukiRootClosure_le m)
  have he : (commutator (SuzukiRootSubgroup m)).map e.toMonoidHom =
      center (SuzukiRootClosure m) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    exact hc
  ext x
  constructor
  · intro hx
    have hz : e x ∈ center (SuzukiRootClosure m) := he ▸ mem_map_of_mem e.toMonoidHom hx
    exact (centerCongr e).symm ⟨e x,hz⟩ |>.property
  · intro hx
    have hz : e x ∈ center (SuzukiRootClosure m) := (centerCongr e ⟨x,hx⟩).property
    rw [← he] at hz
    obtain ⟨y,hy,hyx⟩ := hz
    exact e.injective hyx ▸ hy

theorem mem_center_iff (m : ℕ) (hm : 0 < m) (x : SuzukiRootSubgroup m) :
    x ∈ center (SuzukiRootSubgroup m) ↔ ∃ b, x = rootPoint m 0 b := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hc,hz,_⟩ :=
    External.huppert_blackburn_XI_3_1 m hm (suzukiTits m) (suzukiTits_sq m)
  change commutator (SuzukiRootClosure m) = center (SuzukiRootClosure m) at hc
  change ∀ x : SuzukiRootClosure m, x ∈ commutator (SuzukiRootClosure m) ↔
    ∃ b : Field m, (x : GL (Fin 4) (Field m)) = SuzukiRootGL m 0 b at hz
  rw [hc] at hz
  let e : SuzukiRootSubgroup m ≃* SuzukiRootClosure m :=
    subgroupOfEquivOfLe (suzukiRootClosure_le m)
  constructor
  · intro hx
    obtain ⟨b,hb⟩ := (hz (e x)).mp (centerCongr e ⟨x,hx⟩).property
    exact ⟨b,Subtype.ext (Subtype.ext hb)⟩
  · rintro ⟨b,rfl⟩
    have hh : e (rootPoint m 0 b) ∈ center (SuzukiRootClosure m) :=
      (hz _).mpr ⟨b,rfl⟩
    exact (centerCongr e).symm ⟨_,hh⟩ |>.property

/-- Every homomorphism to an abelian group factors through the first coordinate. -/
theorem hom_rootPoint_eq_first {A : Type*} [CommGroup A] (m : ℕ) (hm : 0 < m)
    (f : SuzukiRootSubgroup m →* A) (a b : Field m) :
    f (rootPoint m a b) = f (rootPoint m a 0) := by
  have hz : rootPoint m 0 b ∈ commutator (SuzukiRootSubgroup m) := by
    rw [root_commutator_eq_center m hm, mem_center_iff m hm]
    exact ⟨b,rfl⟩
  have hk := Abelianization.commutator_subset_ker f hz
  have he : rootPoint m a b = rootPoint m a 0 * rootPoint m 0 b := by
    simp only [rootPoint_mul m hm, add_zero, zero_add, map_zero, mul_zero]
  rw [he, map_mul, show f (rootPoint m 0 b) = 1 from hk, mul_one]

def torusPoint (m : ℕ) (k : (Field m)ˣ) : SuzukiMatrixGroup m :=
  ⟨SuzukiTorusGL m k, suzukiSplitTorusClosure_le m (subset_closure ⟨k,rfl⟩)⟩

def torusNormalizer (m : ℕ) (k : (Field m)ˣ) :
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) :=
  ⟨torusPoint m k, suzukiSplitTorus_le_normalizer_root m (subset_closure ⟨k,rfl⟩)⟩

theorem torusNormalizer_apply (m : ℕ) (k : (Field m)ˣ) (a b : Field m) :
    (SuzukiRootSubgroup m).normalizerMonoidHom (torusNormalizer m k) (rootPoint m a b) =
      rootPoint m ((k : Field m) * a) ((k : Field m) * suzukiTits m k * b) := by
  apply Subtype.ext
  apply Subtype.ext
  exact External.suzukiTorusGL_conj_root m (suzukiTits m) (suzukiTits_sq m)
    (suzukiTits_apply m) a b k

theorem torusNormalizer_pow (m : ℕ) (hm : 0 < m) (k : (Field m)ˣ)
    (r : ℕ) (hr : k ^ r = 1) : torusNormalizer m k ^ r = 1 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,⟨e,he⟩,_⟩ :=
    External.huppert_blackburn_XI_3_1 m hm (suzukiTits m) (suzukiTits_sq m)
  apply Subtype.ext
  apply Subtype.ext
  have hp : e k ^ r = 1 := by rw [← map_pow, hr, map_one]
  have hp' := congrArg Subtype.val hp
  change (e k : GL (Fin 4) (Field m)) ^ r = 1 at hp'
  rw [he] at hp'
  exact hp'

theorem norm_bijective (m : ℕ) :
    Function.Bijective (fun a : Field m => a * suzukiTits m a) := by
  have hn (x : Field m) :
      suzukiTits m (x * suzukiTits m x) = x * (x * suzukiTits m x) := by
    rw [map_mul, suzukiTits_sq]
    ring
  have hi : Function.Injective (fun a : Field m => a * suzukiTits m a) := by
    intro a b hab
    change a * suzukiTits m a = b * suzukiTits m b at hab
    by_cases ha : a = 0
    · subst a
      have hb : b = 0 := (mul_eq_zero.mp (show b * suzukiTits m b = 0 by
        simpa only [zero_mul] using hab.symm)).elim id
        (fun h => (suzukiTits m).injective (by simpa using h))
      exact hb.symm
    · apply mul_right_cancel₀ (mul_ne_zero ha ((map_ne_zero (suzukiTits m)).mpr ha))
      calc
        a * (a * suzukiTits m a) = suzukiTits m (a * suzukiTits m a) := (hn a).symm
        _ = suzukiTits m (b * suzukiTits m b) := congrArg (suzukiTits m) hab
        _ = b * (a * suzukiTits m a) := by rw [hn, hab]
  exact ⟨hi, Finite.surjective_of_injective hi⟩

theorem torus_center_transitive (m : ℕ) (hm : 0 < m)
    (z w : center (SuzukiRootSubgroup m)) (hz : z ≠ 1) (hw : w ≠ 1) :
    ∃ h : normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)),
      centerCongr ((SuzukiRootSubgroup m).normalizerMonoidHom h) z = w := by
  obtain ⟨b,hb⟩ := (mem_center_iff m hm z.val).mp z.property
  obtain ⟨d,hd⟩ := (mem_center_iff m hm w.val).mp w.property
  have hb0 : b ≠ 0 := by
    intro h; apply hz; apply Subtype.ext; change z.val = 1; simpa only [h, rootPoint_zero] using hb
  have hd0 : d ≠ 0 := by
    intro h; apply hw; apply Subtype.ext; change w.val = 1; simpa only [h, rootPoint_zero] using hd
  obtain ⟨k,hk⟩ := (norm_bijective m).surjective (d / b)
  have hk0 : k ≠ 0 := by
    intro h
    have : d / b = 0 := by simpa only [h, zero_mul] using hk.symm
    exact (div_ne_zero hd0 hb0) this
  refine ⟨torusNormalizer m (Units.mk0 k hk0), ?_⟩
  apply Subtype.ext
  change (SuzukiRootSubgroup m).normalizerMonoidHom _ z.val = w.val
  rw [hb, hd, torusNormalizer_apply]
  simp only [Units.val_mk0, mul_zero, hk, div_mul_cancel₀ _ hb0]

theorem torus_center_fixed (m : ℕ) (hm : 0 < m) (k : (Field m)ˣ) (hk : k ≠ 1)
    (z : SuzukiRootSubgroup m) (hz : z ∈ center (SuzukiRootSubgroup m))
    (hf : (SuzukiRootSubgroup m).normalizerMonoidHom (torusNormalizer m k) z = z) :
    z = 1 := by
  obtain ⟨b,rfl⟩ := (mem_center_iff m hm z).mp hz
  rw [torusNormalizer_apply] at hf
  have hb : (k : Field m) * suzukiTits m k * b = b :=
    congrArg (fun x : SuzukiRootSubgroup m => x.val.val (0 : Fin 4) (2 : Fin 4)) hf
  have hb0 : b = 0 := by
    by_contra hb0
    have hnorm : (k : Field m) * suzukiTits m k = 1 :=
      mul_right_cancel₀ hb0 (hb.trans (one_mul b).symm)
    exact hk ((External.binaryGaloisField_tits_norm_eq_one_iff m (suzukiTits m)
      (suzukiTits_sq m) k).mp hnorm)
  rw [hb0, rootPoint_zero]


theorem scalar_obstruction (n i j : ℕ) (hn : 3 ≤ n) (hi : i < n) (hj : j < n) :
    ¬ (2 ^ n - 1) ∣ 2 ^ i + 2 ^ j := by
  have hp : 4 ≤ 2 ^ (n - 1) := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ n - 1 by omega)
    exact this
  have hnexp : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) (by omega)
      _ = 2 * 2 ^ (n - 1) := by rw [pow_succ, Nat.mul_comm]
  have hpi : 2 ^ i ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpj : 2 ^ j ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0 < 2 ^ i + 2 ^ j := by positivity
  intro hd
  have he : 2 ^ i + 2 ^ j = 2 ^ n - 1 := by
    obtain ⟨k,hk⟩ := hd
    have hkpos : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0, Nat.mul_zero] at hk
      omega
    have hsub : 2 ^ n - 1 + 1 = 2 ^ n := by omega
    have hklt : k < 2 := by nlinarith
    have : k = 1 := by omega
    simpa [this] using hk
  have hi0 : i ≠ 0 := by intro h; subst i; simp only [pow_zero] at he; omega
  have hj0 : j ≠ 0 := by intro h; subst j; simp only [pow_zero] at he; omega
  have heven : Even (2 ^ i + 2 ^ j) :=
    (even_two.pow_of_ne_zero hi0).add (even_two.pow_of_ne_zero hj0)
  have hodd := Nat.Even.sub_odd (show 1 ≤ 2 ^ n by omega)
    (even_two.pow_of_ne_zero (by omega : n ≠ 0)) odd_one
  exact (Nat.not_even_iff_odd.mpr hodd) (he ▸ heven)

theorem field_bilinear_zero (n : ℕ) (hn : 3 ≤ n)
    (k : (BinaryGaloisField n)ˣ) (hk : orderOf k = 2 ^ n - 1)
    (B : BinaryGaloisField n →ₗ[ZMod 2] BinaryGaloisField n →ₗ[ZMod 2] BinaryGaloisField n)
    (hB : ∀ a b, B ((k : BinaryGaloisField n) * a) ((k : BinaryGaloisField n) * b) = B a b) :
    B = 0 := by
  obtain ⟨c, hc, hs⟩ := frobeniusBilinear_expansion_with_support_of_equivariant n
    (by omega) B k k 1 (by simpa only [one_mul] using hB)
  have hz (i j : Fin n) : c i j = 0 := by
    by_contra h
    have he := hs i j h
    have he' : k ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) = 1 := by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, ← pow_add] using he
    have hd := orderOf_dvd_of_pow_eq_one he'
    rw [hk] at hd
    exact scalar_obstruction n i j hn i.isLt j.isLt hd
  ext a b
  simp only [hc, hz, zero_mul, Finset.sum_const_zero, LinearMap.zero_apply]


private theorem hom_first_add {A : Type*} [CommGroup A] (m : ℕ) (hm : 0 < m)
    (f : SuzukiRootSubgroup m →* A) (a b : Field m) :
    f (rootPoint m (a + b) 0) = f (rootPoint m a 0) * f (rootPoint m b 0) := by
  rw [← map_mul, rootPoint_mul m hm]
  exact (hom_rootPoint_eq_first m hm f _ _).symm

private abbrev Pairing (m : ℕ) :=
  SuzukiRootSubgroup m →* (SuzukiRootSubgroup m →* Multiplicative (ZMod 2))

private def pairingValue (m : ℕ) (c : Pairing m) (a b : Field m) : Field m :=
  algebraMap (ZMod 2) (Field m) ((c (rootPoint m a 0) (rootPoint m b 0)).toAdd)

private theorem pairingValue_zero_right (m : ℕ) (c : Pairing m) (a : Field m) :
    pairingValue m c a 0 = 0 := by
  simp [pairingValue, rootPoint_zero]

private theorem pairingValue_zero_left (m : ℕ) (c : Pairing m) (b : Field m) :
    pairingValue m c 0 b = 0 := by
  simp [pairingValue, rootPoint_zero]

private theorem pairingValue_add_right (m : ℕ) (hm : 0 < m)
    (c : Pairing m) (a b d : Field m) :
    pairingValue m c a (b + d) = pairingValue m c a b + pairingValue m c a d := by
  dsimp [pairingValue]
  rw [hom_first_add m hm (c (rootPoint m a 0)), toAdd_mul, map_add]

private theorem pairingValue_add_left (m : ℕ) (hm : 0 < m)
    (c : Pairing m) (a b d : Field m) :
    pairingValue m c (a + b) d = pairingValue m c a d + pairingValue m c b d := by
  dsimp [pairingValue]
  rw [hom_first_add m hm c, MonoidHom.mul_apply, toAdd_mul, map_add]

private def pairingInner (m : ℕ) (hm : 0 < m) (c : Pairing m) (a : Field m) :
    Field m →ₗ[ZMod 2] Field m :=
  ({toFun := pairingValue m c a,
    map_zero' := pairingValue_zero_right m c a,
    map_add' := pairingValue_add_right m hm c a} : Field m →+ Field m).toZModLinearMap 2

private theorem pairingInner_apply (m : ℕ) (hm : 0 < m) (c : Pairing m) (a b : Field m) :
    pairingInner m hm c a b = pairingValue m c a b := rfl

private def pairingBilinear (m : ℕ) (hm : 0 < m) (c : Pairing m) :
    Field m →ₗ[ZMod 2] Field m →ₗ[ZMod 2] Field m :=
  ({toFun := pairingInner m hm c,
    map_zero' := by ext b; exact pairingValue_zero_left m c b,
    map_add' := by intro a b; ext d; exact pairingValue_add_left m hm c a b d} :
    Field m →+ (Field m →ₗ[ZMod 2] Field m)).toZModLinearMap 2

private theorem pairingBilinear_apply (m : ℕ) (hm : 0 < m) (c : Pairing m) (a b : Field m) :
    pairingBilinear m hm c a b = pairingValue m c a b := rfl

private theorem pairingBilinear_equivariant (m : ℕ) (hm : 0 < m)
    (k : (Field m)ˣ) (c : Pairing m)
    (hc : ∀ x y, c ((SuzukiRootSubgroup m).normalizerMonoidHom (torusNormalizer m k) x)
      ((SuzukiRootSubgroup m).normalizerMonoidHom (torusNormalizer m k) y) = c x y)
    (a b : Field m) :
    pairingBilinear m hm c ((k : Field m) * a) ((k : Field m) * b) =
      pairingBilinear m hm c a b := by
  have h := hc (rootPoint m a 0) (rootPoint m b 0)
  simp only [torusNormalizer_apply, mul_zero] at h
  exact congrArg (fun z : Multiplicative (ZMod 2) =>
    algebraMap (ZMod 2) (Field m) z.toAdd) h

/-- All binary bihomomorphisms invariant under a primitive split-torus element vanish.
No alternating hypothesis is needed. Both arguments factor through the actual
root derived subgroup before Frobenius coordinates are used. -/
theorem invariant_pairing_trivial (m : ℕ) (hm : 0 < m)
    (k : (Field m)ˣ) (hk : orderOf k = 2 ^ (2 * m + 1) - 1)
    (c : Pairing m)
    (hc : ∀ x y, c ((SuzukiRootSubgroup m).normalizerMonoidHom (torusNormalizer m k) x)
      ((SuzukiRootSubgroup m).normalizerMonoidHom (torusNormalizer m k) y) = c x y) :
    c = 1 := by
  have hB : pairingBilinear m hm c = 0 :=
    field_bilinear_zero (2 * m + 1) (by omega) k hk _
      (pairingBilinear_equivariant m hm k c hc)
  apply MonoidHom.ext
  intro x
  apply MonoidHom.ext
  intro y
  obtain ⟨a,b,rfl⟩ := rootPoint_surjective m x
  obtain ⟨d,e,rfl⟩ := rootPoint_surjective m y
  change c (rootPoint m a b) (rootPoint m d e) = 1
  rw [hom_rootPoint_eq_first m hm c a b,
    hom_rootPoint_eq_first m hm (c (rootPoint m a 0)) d e]
  have he : pairingValue m c a d = 0 := congrArg (fun f : Field m →ₗ[ZMod 2]
    Field m →ₗ[ZMod 2] Field m => f a d) hB
  have hz : (c (rootPoint m a 0) (rootPoint m d 0)).toAdd = 0 :=
    (algebraMap (ZMod 2) (Field m)).injective (he.trans (map_zero _).symm)
  exact congrArg Multiplicative.ofAdd hz

/-- The standard root Sylow has every intrinsic action property needed by the
perfect central double-cover criterion, uniformly including Sz(8). -/
public theorem root_sylow_center_action (m : ℕ) (hm : 0 < m) :
    PerfectCentralCovering.SylowCenterAction (SuzukiRootSubgroup m) := by
  obtain ⟨k,hk⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (Field m)ˣ)
  have hk' : orderOf k = 2 ^ (2 * m + 1) - 1 := by
    rw [hk, Nat.card_units, GaloisField.card 2 (2 * m + 1) (by omega)]
  have hbound : 8 ≤ 2 ^ (2 * m + 1) :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 3 ≤ 2 * m + 1)
  have hkne : k ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hk'
    omega
  refine ⟨torus_center_transitive m hm, Or.inr ⟨(root_commutator_eq_center m hm).le,
    torusNormalizer m k, 2 ^ (2 * m + 1) - 1, ?_, ?_,
    torus_center_fixed m hm k hkne, invariant_pairing_trivial m hm k hk'⟩⟩
  · exact Nat.Even.sub_odd (by omega)
      (even_two.pow_of_ne_zero (by omega : 2 * m + 1 ≠ 0)) odd_one
  · exact torusNormalizer_pow m hm k _ (hk' ▸ pow_orderOf_eq_one k)

end BenderSuzuki.ZD.DirectSylowCenters.SuzukiActions

namespace BenderSuzuki.ZD.DirectSylowCenters
open BenderSuzuki.MatrixGroups PerfectCentralCovering Subgroup

/-- Actual Suzuki root Sylows discharge the Suzuki action contract for direct
cover rigidity at every parameter m ≥ 1. -/
public theorem suzuki_center_actions : SuzukiCenterActions := by
  intro m hm
  obtain ⟨Q,hQ⟩ := suzukiRootSubgroup_isSylow m (by omega)
  refine ⟨Q, ?_⟩
  rw [hQ]
  exact SuzukiActions.root_sylow_center_action m (by omega)

/-- The Suzuki case of GLS4, Chapter 4, Lemma 2.8(c), for the original perfect
central double cover and any prescribed Sylow subgroup of its domain. -/
public theorem suzuki_sylow_center_eq_kernel
    {E B : Type*} [Group E] [Finite E] [Group B]
    (f : Cover E B) (hcard : Nat.card f.toMonoidHom.ker = 2)
    (m : ℕ) (hm : 1 ≤ m) (e : B ≃* SuzukiMatrixGroup m) (P : Sylow 2 E) :
    (center P).map (P : Subgroup E).subtype = f.toMonoidHom.ker := by
  obtain ⟨Q,hQ⟩ := suzuki_center_actions m hm
  exact f.sylow_center_eq_kernel_of_model_sylow hcard e Q hQ P

end BenderSuzuki.ZD.DirectSylowCenters

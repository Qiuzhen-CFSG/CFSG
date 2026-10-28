module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.LongRootModule
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanWeights

/-!
# The actual source Cartan action from the DC pairing

The normalized DC pairing already determines both Cartan cross actions,
without the full positive table. The long-root module calculation gives
EB. Applying the actual long rank-one word to B then shows that its torus
acts on A and B by a and a⁻¹. It centralizes C, so conjugating FC and
cancelling forces its action on F to be a⁻¹.

The existing rank-one Cartan-reflection formula now gives
s H_long(a) s⁻¹ = H_long(a) H_short(a). Acting on E, and using the
parameter-preserving E/B interchange, forces H_short(a) to act on E by
a⁻³. The existing reflection transports supply all six weights of the
actual two-parameter source torus. This argument includes q=2 and q=4;
it does not use FD, FE, a representation-classification assumption, or
ForcedCartanWeights, which requires the full positive relations.

MixedEquations therefore needs no auxiliary torus. PairingCartanApplication
feeds these three remaining equations to the existing full marked,
original and geometric consumers. The compatible whole-pinning labels
and DC, FD and lower FE equations still must be constructed from 6E(a).
In particular normalized DC is not asserted for arbitrary independent
local field labels.

Source: Fong--Seitz II §7, p.192, and (9.8)--(9.21), pp.212--217.
This is a direct rank-one-word proof of the required Cartan actions;
all products use the consumer's left-conjugation convention.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition

private theorem long_word_action {K Y : Type*} [Field K] [CharP K 2] [Group Y]
    (L : PositiveRoots K Y) (R : L.CommutingRelations)
    (heb : ∀ e b, L.x 4 e * L.x 1 b = L.x 0 (b*e) * L.x 1 b * L.x 4 e)
    (r t : Y) (hrA : ∀ a, MulAut.conj r (L.x 0 a) = L.x 1 a)
    (hrB : ∀ a, MulAut.conj r (L.x 1 a) = L.x 0 a) (hrInv : r⁻¹ = r)
    (a : Kˣ)
    (hword : L.x 4 (a : K) * (r*L.x 4 (↑a⁻¹ : K)*r⁻¹) * L.x 4 (a : K) = t*r)
    (b : K) : MulAut.conj t (L.x 0 b) = L.x 0 ((a : K)*b) := by
  have hfix (e c : K) : MulAut.conj (L.x 4 e) (L.x 0 c) = L.x 0 c := by
    change L.x 4 e * L.x 0 c * (L.x 4 e)⁻¹ = _
    rw [R.ea,mul_assoc,mul_inv_cancel,mul_one]
  have hact (e c : K) : MulAut.conj (L.x 4 e) (L.x 1 c) = L.x 0 (c*e)*L.x 1 c := by
    change L.x 4 e * L.x 1 c * (L.x 4 e)⁻¹ = _
    rw [heb,mul_assoc,mul_inv_cancel,mul_one]
  have he := congrArg (fun v : Y => MulAut.conj v (L.x 1 b)) hword
  simp only [hrInv,map_mul,MulAut.mul_apply,hact,hrA,hrB,hfix] at he
  have hb : b * (a : K) * (↑a⁻¹ : K) = b := by
    rw [mul_assoc,Units.mul_inv,mul_one]
  rw [hb] at he
  have hba (x y : K) (z : Y) : L.x 1 x * (L.x 0 y * z) = L.x 0 y * (L.x 1 x * z) := by
    rw [← mul_assoc,R.ba,mul_assoc]
  have hcollect (i : Fin 6) (x y : K) (z : Y) :
      L.x i x * (L.x i y * z) = L.x i (x+y)*z := by
    rw [← mul_assoc,← L.x_add]
  simpa only [mul_assoc,hba,hcollect,← L.x_add,CharTwo.add_self_eq_zero,L.x_zero,
    one_mul,mul_one,zero_add,mul_comm b (a : K)] using he.symm

variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (hm : rotationOrder Q = 6)
  (hdc : ∀ d c : F, (alignedSourceRoots Q split hK μ n short).x 3 d *
    (alignedSourceRoots Q split hK μ n short).x 2 c =
      (alignedSourceRoots Q split hK μ n short).x 0 (c*d) *
        (alignedSourceRoots Q split hK μ n short).x 2 c *
          (alignedSourceRoots Q split hK μ n short).x 3 d)

include hm hdc in
/-- The long rank-one word determines its action on the highest root. -/
theorem alignedTorus_long_A_of_dc (a : Fˣ) (b : F) :
    MulAut.conj (alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a)
      ((alignedSourceRoots Q split hK μ n short).x 0 b) =
        (alignedSourceRoots Q split hK μ n short).x 0 ((a : F)*b) := by
  apply long_word_action _ (aligned_commuting_of_dc Q split hK μ n short hm hdc)
    (aligned_eb_of_dc Q split hK μ n short hm hdc) ((n (1-short)).val) _
    (sourceBorelWeyl_rA Q split hK μ n short split.abelian)
    (sourceBorelWeyl_rB Q split hK μ n short split.abelian)
    (inv_eq_of_mul_eq_one_right (sourceReflection_sq Q split (1-short)
      (hK (1-short)) (μ (1-short)) (n (1-short)))) a
  have hh := sourceBorelWeyl_long_word Q split hK μ n short split.abelian a
  change _ = alignedPairTorus Q split hK μ n short split.abelian (1,a) * (n (1-short)).val at hh
  rwa [alignedPairTorus_long] at hh

include hm hdc in
/-- The long reflection transports the highest-root scalar to B. -/
theorem alignedTorus_long_B_of_dc (a : Fˣ) (b : F) :
    MulAut.conj (alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a)
      ((alignedSourceRoots Q split hK μ n short).x 1 b) =
        (alignedSourceRoots Q split hK μ n short).x 1 ((a : F)⁻¹*b) := by
  let T := alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))
  let r : X ⧸ Q.D := (n (1-short)).val
  let L := alignedSourceRoots Q split hK μ n short
  have hr (c : F) : MulAut.conj r (L.x 0 c) = L.x 1 c :=
    sourceBorelWeyl_rA Q split hK μ n short split.abelian c
  have ht : MulAut.conj r (T a⁻¹) = T a := by
    change (n (1-short)).val * alignedTorus Q split (1-short) (hK (1-short))
      (μ (1-short)) (n (1-short)) a⁻¹ * ((n (1-short)).val : X ⧸ Q.D)⁻¹ =
        alignedTorus Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a
    simpa only [inv_inv] using
      reflection_alignedTorus Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a⁻¹
  have he := congrArg (MulAut.conj r) (alignedTorus_long_A_of_dc Q split hK μ n short hm hdc a⁻¹ b)
  change MulAut.conj r (T a⁻¹ * L.x 0 b * (T a⁻¹)⁻¹) =
    MulAut.conj r (L.x 0 ((↑a⁻¹ : F)*b)) at he
  rw [map_mul,map_mul,ht,hr,hr,map_inv,ht] at he
  change T a * L.x 1 b * (T a)⁻¹ = L.x 1 ((a : F)⁻¹*b)
  simpa only [Units.val_inv_eq_inv_val] using he

include hm hdc in
/-- Comparing FC after conjugation determines the long coroot action on F. -/
theorem alignedTorus_long_cross_action_of_dc (a : Fˣ) (b : F) :
    alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a *
      (alignedSourceRoots Q split hK μ n short).x 5 b *
      (alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a)⁻¹ =
        (alignedSourceRoots Q split hK μ n short).x 5 ((a : F)⁻¹*b) := by
  let L := alignedSourceRoots Q split hK μ n short
  let t := alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a
  have ht : t ∈ Q.tits.B ⊓ Q.tits.N := alignedTorus_mem_cartan Q split _ _ _ _ a
  have hx (i : Fin 6) (c : F) : L.x i c ∈ positiveCarrier Q split short i := by
    rw [← alignedSourceRoots_range Q split hK μ n short i]
    exact ⟨.ofAdd c,rfl⟩
  have hmem := (mem_normalizer_iff.mp (positiveCarrier_torus_normalizes Q split short 5 ht) _).mp (hx 5 b)
  rw [← alignedSourceRoots_range Q split hK μ n short 5] at hmem
  obtain ⟨v,hv⟩ := hmem
  have hv' : MulAut.conj t (L.x 5 b) = L.x 5 v.toAdd := hv.symm
  have hc : MulAut.conj t (L.x 2 1) = L.x 2 1 := by
    have hh := aligned_long_centralizes Q split hK μ n short hm
      (aligned_commuting_of_dc Q split hK μ n short hm hdc)
      (show t ∈ rankOne Q split (1-short) from
        (show t ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split (1-short) from
          (alignedTorusHom_range Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))) ▸ ⟨a,rfl⟩).2)
    change t * L.x 2 1 * t⁻¹ = L.x 2 1
    rw [← mem_centralizer_iff.mp hh _ (hx 2 1),mul_assoc,mul_inv_cancel,mul_one]
  have hfc := aligned_fc_of_dc Q split hK μ n short hm
    (aligned_ec_of_dc Q split hK μ n short hm hdc) hdc
  change ∀ z c, L.x 5 z * L.x 2 c = L.x 1 (c*z) * L.x 2 c * L.x 5 z at hfc
  have he := congrArg (MulAut.conj t) (hfc b 1)
  simp only [map_mul,hv',hc,one_mul] at he
  rw [alignedTorus_long_B_of_dc Q split hK μ n short hm hdc] at he
  rw [hfc,one_mul] at he
  have heq : v.toAdd = (a : F)⁻¹*b :=
    Multiplicative.ofAdd.injective (alignedSourceRoots_injective Q split hK μ n short 1
      (mul_right_cancel (mul_right_cancel he)))
  exact hv'.trans (congrArg (L.x 5) heq)

include hm hdc in
/-- The long-coroot/short-reflection commutator determines the short coroot
action on E, without any FE equation. -/
theorem alignedTorus_short_cross_action_of_dc (a : Fˣ) (b : F) :
    alignedTorusHom Q split short (hK short) (μ short) (n short) a *
      (alignedSourceRoots Q split hK μ n short).x 4 b *
      (alignedTorusHom Q split short (hK short) (μ short) (n short) a)⁻¹ =
        (alignedSourceRoots Q split hK μ n short).x 4 ((a : F)⁻¹^3*b) := by
  let L := alignedSourceRoots Q split hK μ n short
  let T := alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))
  let S := alignedTorusHom Q split short (hK short) (μ short) (n short)
  let s : X ⧸ Q.D := (n short).val
  have hsInv : s⁻¹ = s := inv_eq_of_mul_eq_one_right
    (sourceReflection_sq Q split short (hK short) (μ short) (n short))
  have hsE (c : F) : MulAut.conj s (L.x 4 c) = L.x 1 c :=
    sourceBorelWeyl_sE Q split hK μ n short split.abelian c
  have hsB (c : F) : MulAut.conj s (L.x 1 c) = L.x 4 c :=
    sourceBorelWeyl_sB Q split hK μ n short split.abelian c
  have hB (c : F) : MulAut.conj (T a) (L.x 1 c) = L.x 1 ((a : F)⁻¹*c) :=
    alignedTorus_long_B_of_dc Q split hK μ n short hm hdc a c
  have hE (c : F) : MulAut.conj (T a) (L.x 4 c) = L.x 4 ((a : F)^2*c) :=
    alignedTorus_root Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a c
  have hst : s*T a*s⁻¹ = T a*S a := by
    have he := reflection_cartan_of_simple_weight Q split hK μ n short
      (alignedTorus_mem_cartan Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a)
      a⁻¹ (by
        change T a * L.x 5 1 * (T a)⁻¹ = L.x 5 (↑a⁻¹ : F)
        simpa only [mul_one,Units.val_inv_eq_inv_val] using
          alignedTorus_long_cross_action_of_dc Q split hK μ n short hm hdc a 1)
    simpa only [s,T,S,alignedTorusHom_apply,inv_inv] using he
  change MulAut.conj (S a) (L.x 4 b) = L.x 4 ((a : F)⁻¹^3*b)
  apply (MulAut.conj (T a)).injective
  have he : MulAut.conj (T a) (MulAut.conj (S a) (L.x 4 b)) = L.x 4 ((a : F)⁻¹*b) := by
    calc
      _ = MulAut.conj (T a*S a) (L.x 4 b) := by rw [map_mul,MulAut.mul_apply]
      _ = _ := by
        rw [← hst]
        simp only [map_mul,MulAut.mul_apply,hsInv,hsE,hB,hsB]
  rw [he,hE]
  congr 1
  field_simp

include hm hdc in
/-- All six weights hold for the actual source torus before constructing FD or FE. -/
theorem sourceBorelWeyl_torus_root_of_dc (l m : Fˣ) (i : Fin 6) (b : F) :
    (sourceBorelWeyl Q split hK μ n short split.abelian).torus (l,m) *
      (alignedSourceRoots Q split hK μ n short).x i b *
      ((sourceBorelWeyl Q split hK μ n short split.abelian).torus (l,m))⁻¹ =
        (alignedSourceRoots Q split hK μ n short).x i (BorelWeylData.weight l m i*b) := by
  obtain ⟨hE,hF⟩ := sourceBorelWeyl_simple_weights_of_cross_actions
    Q split hK μ n short split.abelian
    (alignedTorus_short_cross_action_of_dc Q split hK μ n short hm hdc)
    (alignedTorus_long_cross_action_of_dc Q split hK μ n short hm hdc)
  exact sourceBorelWeyl_torus_root_of_simple_weights Q split hK μ n short split.abelian hE hF l m i b

/-- The remaining mixed equations. No torus or Cartan-action data are inputs.
Constructing these equations with compatible whole-pinning field labels from
6E(a), including the binary case, remains a source obligation. -/
structure MixedEquations {K Y : Type*} [Field K] [Group Y]
    (roots : PositiveRoots K Y) where
  dc : ∀ d c, roots.x 3 d * roots.x 2 c = roots.x 0 (c*d) * roots.x 2 c * roots.x 3 d
  fd : ∀ z d, roots.x 5 z * roots.x 3 d =
    roots.x 0 (d^2*z) * roots.x 1 (d*z^2) * roots.x 3 d * roots.x 5 z
  fe_mem : ∀ z e, ∃ a, roots.x 5 z * roots.x 4 e =
    roots.x 0 a * roots.x 1 (e*z^3) * roots.x 2 (e*z^2) * roots.x 3 (e*z) * roots.x 4 e * roots.x 5 z

/-- Supply the former auxiliary torus from the actual source Cartan, using only DC. -/
def aligned_reduced_of_mixed (d : MixedEquations (alignedSourceRoots Q split hK μ n short)) :
    ReducedMixedData (alignedSourceRoots Q split hK μ n short) where
  dc := d.dc
  fd := d.fd
  fe_mem := d.fe_mem
  torus := (sourceBorelWeyl Q split hK μ n short split.abelian).torus
  torus_root := sourceBorelWeyl_torus_root_of_dc Q split hK μ n short hm d.dc

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource

module
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer
public import Theory.GroupTheory.OddCentralInvolutionLifting.Centralizers
public import Theory.GroupTheory.CentralExtensionPartialInversion
public import Theory.GroupTheory.TwoLocalSurjective
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.FieldTheory.Finite.Basic
/-!
# Split symplectic tori in odd central covers

Over a finite field of characteristic two with more than two elements,
choose an odd prime dividing the multiplicative field order. Three diagonal
coordinates of that prime order lie in the actual root normalizer of PSp6.
The coordinate Weyl involutions invert those parameters independently.
Lifting the involutions through an odd central kernel produces commuting
lifts of the same prime order, retaining their marked projective images.

A two-local lift of the root normalizer contains the central kernel, hence
contains all these lifts. Its odd-prime rank is at least three, contradicting
quasithinness of the original covering group. This avoids assuming that
quasithinness descends through an odd central quotient.
Source: Aschbacher--Smith A.2.18, printed p.40, Case II symplectic branch.
-/

noncomputable section
open Matrix Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticRoot.OddCentral
variable {F : Type*} [Field F] [CharP F 2]

private def weyl (i : Fin 3) : Sp 3 F :=
  ⟨fromBlocks (diagonal (fun j => if j = i then 0 else 1))
    (diagonal (fun j => if j = i then 1 else 0))
    (diagonal (fun j => if j = i then 1 else 0))
    (diagonal (fun j => if j = i then 0 else 1)), by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp only [diagonal_transpose, diagonal_mul_diagonal]
    refine ⟨?_, ?_, ?_⟩ <;> ext a b <;>
      by_cases ha : a = i <;> by_cases hb : a = b <;>
      simp_all [Matrix.diagonal, Matrix.one_apply, CharTwo.neg_eq]⟩

private theorem weyl_square (i : Fin 3) : weyl (F := F) i ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  change (weyl (F := F) i).val * (weyl i).val = (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
  change fromBlocks _ _ _ _ * fromBlocks _ _ _ _ = _
  rw [fromBlocks_multiply]
  simp only [diagonal_mul_diagonal, ← fromBlocks_one]
  congr 1 <;> ext a b <;> by_cases ha : a = i <;> by_cases hb : a = b <;>
    simp_all [Matrix.diagonal, Matrix.one_apply]

private def scalar (i : Fin 3) (u : Fˣ) : Sp 3 F := diagonalSp (Pi.mulSingle i u)

private theorem weyl_scalar_relation (i j : Fin 3) (u : Fˣ) :
    weyl i * scalar j u = scalar j (if i = j then u⁻¹ else u) * weyl i := by
  apply Subtype.ext
  change fromBlocks _ _ _ _ * fromBlocks _ _ _ _ = fromBlocks _ _ _ _ * fromBlocks _ _ _ _
  simp only [fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add, diagonal_mul_diagonal]
  congr 1 <;> ext a b <;> by_cases hi : i = j <;> by_cases ha : a = i <;>
    by_cases hj : a = j <;> by_cases hb : a = b <;>
    simp_all [Matrix.diagonal,Pi.mulSingle]


private def scalarHom (i : Fin 3) : Fˣ →* Sp 3 F := diagonalHom.comp (MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) i)

omit [CharP F 2] in
private theorem scalar_inverse (i : Fin 3) (u : Fˣ) : scalar i u⁻¹ = (scalar i u)⁻¹ :=
  map_inv (scalarHom i) u

omit [CharP F 2] in
private theorem scalar_commute (i j : Fin 3) (u : Fˣ) : Commute (scalar i u) (scalar j u) := by
  change diagonalHom (Pi.mulSingle i u) * diagonalHom (Pi.mulSingle j u) =
    diagonalHom (Pi.mulSingle j u) * diagonalHom (Pi.mulSingle i u)
  rw [← map_mul, ← map_mul, mul_comm]

private def gamma (i : Fin 3) (u : Fˣ) : PSp 3 F := project (scalar i u)
private def inverter (i : Fin 3) : PSp 3 F := project (weyl i)

private theorem inverter_square (i : Fin 3) : inverter (F := F) i ^ 2 = 1 := by
  rw [inverter, ← map_pow, weyl_square, map_one]

private theorem inverter_relation (i j : Fin 3) (u : Fˣ) :
    inverter i * gamma j u = gamma j (if i = j then u⁻¹ else u) * inverter i := by
  exact (map_mul project _ _).symm.trans ((congrArg project
    (weyl_scalar_relation i j u)).trans (map_mul project _ _))

omit [CharP F 2] in
private theorem gamma_inverse (i : Fin 3) (u : Fˣ) : gamma i u⁻¹ = (gamma i u)⁻¹ := by
  simp only [gamma, scalar_inverse, map_inv]

private theorem inverter_inverts (i : Fin 3) (u : Fˣ) :
    inverter i * gamma i u * (inverter i)⁻¹ = (gamma i u)⁻¹ := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  simpa only [ite_true, gamma_inverse] using inverter_relation i i u

private theorem inverter_commutes (i j : Fin 3) (hij : i ≠ j) (u : Fˣ) :
    Commute (inverter i) (gamma j u) := by
  change inverter i * gamma j u = gamma j u * inverter i
  simpa only [if_neg hij] using inverter_relation i j u

private theorem second_square (i : Fin 3) (u : Fˣ) : (inverter i * gamma i u) ^ 2 = 1 := by
  have hw := inverter_square (F := F) i
  have hr : inverter i * gamma i u = (gamma i u)⁻¹ * inverter i := by
    simpa only [ite_true, gamma_inverse] using inverter_relation i i u
  rw [pow_two]
  calc
    _ = ((gamma i u)⁻¹ * inverter i) * (inverter i * gamma i u) := by nth_rw 1 [hr]
    _ = 1 := by rw [mul_assoc, ← mul_assoc (inverter i), ← pow_two, hw]; simp

section Torus
variable {p : ℕ} [NeZero p] (u : Fˣ) (hu : u ^ p = 1)

private def parameters : (Fin 3 → Multiplicative (ZMod p)) →* (Fin 3 → Fˣ) where
  toFun a i := u ^ (a i).toAdd.val
  map_one' := by funext i; change u ^ (0 : ZMod p).val = 1; simp
  map_mul' a b := by
    funext i
    change u ^ ((a i).toAdd + (b i).toAdd).val = u ^ (a i).toAdd.val * u ^ (b i).toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact pow_eq_pow_of_modEq (Nat.mod_mod _ _) hu

private def originalEmbedding : (Fin 3 → Multiplicative (ZMod p)) →* PSp 3 F :=
  project.comp (diagonalHom.comp (parameters u hu))

omit [CharP F 2] in
private theorem originalEmbedding_injective (horder : orderOf u = p) (hodd : Odd p) :
    Function.Injective (originalEmbedding u hu) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  change QuotientGroup.mk (diagonalSp (parameters u hu a)) = 1 at ha
  rw [QuotientGroup.eq_one_iff] at ha
  funext i
  have hi := diagonalSp_eq_inv_of_central _ ha i
  have he : (u ^ (a i).toAdd.val) ^ 2 = 1 := by
    simpa only [parameters, MonoidHom.coe_mk, OneHom.coe_mk, pow_two] using
      eq_inv_iff_mul_eq_one.mp hi
  have hp : (u ^ (a i).toAdd.val) ^ p = 1 := by rw [pow_right_comm,hu,one_pow]
  have ho : u ^ (a i).toAdd.val = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    rw [← hodd.coprime_two_right.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp) (orderOf_dvd_of_pow_eq_one he)
  change (a i).toAdd = (0 : ZMod p)
  apply ZMod.val_injective
  apply pow_injOn_Iio_orderOf (x := u)
  · simpa only [Set.mem_Iio,horder] using ZMod.val_lt (a i).toAdd
  · simp only [Set.mem_Iio,horder,ZMod.val_zero]; exact NeZero.pos p
  · simpa using ho

omit [CharP F 2] in
private theorem originalEmbedding_mem_normalizer (a : Fin 3 → Multiplicative (ZMod p)) :
    originalEmbedding u hu a ∈ normalizer (rootSubgroup (F := F) (0 : Fin 3) : Set (PSp 3 F)) := by
  have he : originalEmbedding u hu a = torusProjective 0 (⊤ : Subgroup Fˣ)
      (fun i => ⟨parameters u hu a i, mem_top _⟩) := by
    apply congrArg project
    apply congrArg diagonalSp
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact torusProjective_mem_normalizer 0 ⊤ _ 0

section Lift
variable {G : Type*} [Group G] (q : G →* PSp 3 F) (hq : Function.Surjective q)
  (hk : q.ker ≤ center G) (ho : Odd (Nat.card q.ker))

private def firstLift (i : Fin 3) : G :=
  OddCentralLifting.involutionLift q hq ho (inverter i) (inverter_square i)
private def secondLift (i : Fin 3) : G :=
  OddCentralLifting.involutionLift q hq ho (inverter i * gamma i u) (second_square i u)
private def liftedGenerator (i : Fin 3) : G := firstLift q hq ho i * secondLift u q hq ho i

private theorem liftedGenerator_image (i : Fin 3) : q (liftedGenerator u q hq ho i) = gamma i u := by
  rw [liftedGenerator,map_mul,firstLift,secondLift,
    OddCentralLifting.involutionLift_image,OddCentralLifting.involutionLift_image,
    ← mul_assoc, ← pow_two,inverter_square,one_mul]

include hu hk in
omit [NeZero p] in
private theorem liftedGenerator_power (i : Fin 3) : liftedGenerator u q hq ho i ^ p = 1 := by
  apply OddCentralLifting.involution_product_relation q ho hk
    (OddCentralLifting.involutionLift_square q hq ho _ _)
    (OddCentralLifting.involutionLift_square q hq ho _ _)
  rw [← map_mul]
  change q (liftedGenerator u q hq ho i) ^ p = 1
  rw [liftedGenerator_image,gamma,← map_pow]
  change project (scalarHom i u ^ p) = 1
  rw [← map_pow,hu,map_one,map_one]

include hu hk in
omit [NeZero p] in
private theorem liftedGenerators_commute (hp : Odd p) (i j : Fin 3) :
    Commute (liftedGenerator u q hq ho i) (liftedGenerator u q hq ho j) := by
  by_cases hij : i = j
  · subst j; exact Commute.refl _
  · apply CentralExtension.commute_lifts_of_partial_inversion q hq hk
      (gamma i u) (gamma j u) (inverter i) hp.coprime_two_right
      _ ((scalar_commute i j u).map project) (inverter_inverts i u)
      (inverter_commutes i j hij u) _ _
      (liftedGenerator_image _ _ _ _ _) (liftedGenerator_image _ _ _ _ _)
    change project (scalarHom i u) ^ p = 1
    rw [← map_pow, ← map_pow,hu,map_one,map_one]

private def liftedCycle (i : Fin 3) : Multiplicative (ZMod p) →* G where
  toFun a := liftedGenerator u q hq ho i ^ a.toAdd.val
  map_one' := by change liftedGenerator u q hq ho i ^ (0 : ZMod p).val = 1; simp
  map_mul' a b := by
    change liftedGenerator u q hq ho i ^ (a.toAdd+b.toAdd).val = _
    rw [ZMod.val_add, ← pow_add]
    exact pow_eq_pow_of_modEq (Nat.mod_mod _ _) (liftedGenerator_power u hu q hq hk ho i)

variable (hp : Odd p)

include hp in
private theorem liftedCycles_commute : Pairwise (fun i j => ∀ a b,
    Commute (liftedCycle u hu q hq hk ho i a) (liftedCycle u hu q hq hk ho j b)) := by
  intro i j _ a b
  exact (liftedGenerators_commute u hu q hq hk ho hp i j).pow_pow a.toAdd.val b.toAdd.val

private def liftedEmbedding : (Fin 3 → Multiplicative (ZMod p)) →* G :=
  MonoidHom.noncommPiCoprod (liftedCycle u hu q hq hk ho)
    (liftedCycles_commute u hu q hq hk ho hp)

private theorem liftedEmbedding_image (a : Fin 3 → Multiplicative (ZMod p)) :
    q (liftedEmbedding u hu q hq hk ho hp a) = originalEmbedding u hu a := by
  rw [liftedEmbedding,MonoidHom.noncommPiCoprod_apply]
  have he : (Finset.univ : Finset (Fin 3)) = [0,1,2].toFinset := by decide
  rw [he, Finset.noncommProd_toFinset _ _ _ (by decide)]
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  change q (liftedGenerator u q hq ho 0 ^ (a 0).toAdd.val *
    (liftedGenerator u q hq ho 1 ^ (a 1).toAdd.val *
      liftedGenerator u q hq ho 2 ^ (a 2).toAdd.val)) = _
  simp only [map_mul,map_pow,liftedGenerator_image,gamma]
  rw [← map_pow,← map_pow,← map_pow,← map_mul,← map_mul]
  apply congrArg project
  change scalarHom 0 u ^ (a 0).toAdd.val *
    (scalarHom 1 u ^ (a 1).toAdd.val * scalarHom 2 u ^ (a 2).toAdd.val) = _
  simp only [scalarHom,MonoidHom.comp_apply,← map_pow,← map_mul]
  apply congrArg diagonalHom
  funext i
  fin_cases i <;> simp [parameters]

end Lift

variable {G : Type*} [Group G] [Finite G]

include hu in
/-- The original two-local lift contains all three lifted torus directions. -/
private theorem rank_three_in_local (q : G →* PSp 3 F) (hq : Function.Surjective q)
    (hk : q.ker ≤ center G) (ho : Odd (Nat.card q.ker))
    (hp : p.Prime) (hop : Odd p) (horder : orderOf u = p) :
    ∃ L : Subgroup G, IsTwoLocal L ∧ 3 ≤ primeRank p L := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨L,hL,hmap⟩ :=
    (rootNormalizer_isTwoLocal (F := F) (0 : Fin 3)).exists_map_eq_of_surjective q hq
  have hkL : q.ker ≤ L := by
    obtain ⟨Q,_,_,rfl⟩ := hL
    exact hk.trans (center_le_normalizer _)
  have hcomap : (normalizer (rootSubgroup (F := F) (0 : Fin 3) : Set (PSp 3 F))).comap q = L := by
    rw [← hmap]
    exact comap_map_eq_self hkL
  let f := liftedEmbedding u hu q hq hk ho hop
  have hf (a) : f a ∈ L := by
    rw [← hcomap]
    change q (f a) ∈ normalizer (rootSubgroup (F := F) (0 : Fin 3) : Set (PSp 3 F))
    rw [liftedEmbedding_image]
    exact originalEmbedding_mem_normalizer u hu a
  let fL := f.codRestrict L hf
  have hfi : Function.Injective fL := by
    intro a b hab
    apply originalEmbedding_injective u hu horder hop
    rw [← liftedEmbedding_image u hu q hq hk ho hop a,
      ← liftedEmbedding_image u hu q hq hk ho hop b]
    exact congrArg q (congrArg (fun x : L => (x : G)) hab)
  refine ⟨L,hL,?_⟩
  apply primeRank_ge_of_elementary_embedding
    (A := Fin 3 → Multiplicative (ZMod p)) _ _ fL hfi
  · intro a
    funext i
    change Multiplicative.ofAdd (p • (a i).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero p (a i).toAdd)
  · simp [Nat.card_eq_fintype_card]

end Torus

variable {G : Type*} [Group G] [Finite G] [Finite F]

/-- The actual split torus lifts through every odd central cover of nonbinary PSp6. -/
public theorem not_quasithin_of_odd_central_cover
    (hcard : 2 < Nat.card F) (q : G →* PSp 3 F) (hq : Function.Surjective q)
    (hk : q.ker ≤ center G) (ho : Odd (Nat.card q.ker)) : ¬ IsQuasithin G := by
  intro hG
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show Nat.card F - 1 ≠ 1 by omega)
  have heven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card,even_iff_two_dvd,Nat.dvd_iff_mod_eq_zero]
    exact FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2)
  have hop : Odd p := hp.odd_of_ne_two (by
    intro he
    subst p
    obtain ⟨a,ha⟩ := heven
    obtain ⟨b,hb⟩ := hd
    omega)
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hd' : p ∣ Nat.card Fˣ := by simpa only [Nat.card_units] using hd
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hd'
  have hup : u ^ p = 1 := hu ▸ pow_orderOf_eq_one u
  obtain ⟨L,hL,hr⟩ := rank_three_in_local u hup q hq hk ho hp hop hu
  have hh := isQuasithin_iff_twoLocal.mp hG L hL p hp hop
  omega

/-- The obstruction on the original group's actual central quotient. -/
public theorem not_quasithin_of_odd_center
    (hcard : 2 < Nat.card F) (ho : Odd (Nat.card (center G)))
    (e : G ⧸ center G ≃* PSp 3 F) : ¬ IsQuasithin G := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have he : q.ker = center G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  exact not_quasithin_of_odd_central_cover hcard q hq (by rw [he]) (by rwa [he])

end Theory.SpecificGroups.SymplecticRoot.OddCentral


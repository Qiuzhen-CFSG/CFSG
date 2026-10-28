module

public import Stellmacher.Recognition.Parrott.CentralizerCoreOrientationSeed
public import Theory.GroupAction.BinaryFourTripleOrientation

/-!
# Coordinates and triple commutators for a supplied Parrott core frame

The coordinate interface below refers to the literal ambient image of O₂(C_G(z))
and has kernel exactly its derived subgroup. Its four named values retain the
supplied a,b,c,d. Constructing this interface and evaluating the triple
commutator in these coordinates are separate mathematical obligations.

The elementary calculations here establish the five actual triple commutators
needed for orientation. Conjugation transports their values because it fixes z.
No coordinate model or existence of coordinates is assumed by these calculations.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.678–681, equations (2), (3), (5), (10)–(15), and (23).
-/

open Subgroup

namespace Stellmacher.Recognition

namespace ParrottCore

/-- The two-core, as a subgroup of the original ambient group. -/
public abbrev Core {G : Type*} [Group G] (z : G) : Subgroup G :=
  (pCore 2 (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype

/-- The derived two-core, as a subgroup of the original ambient group. -/
public abbrev Derived {G : Type*} [Group G] (z : G) : Subgroup G :=
  (commutator (pCore 2 (centralizer ({z} : Set G)))).map
    ((centralizer ({z} : Set G)).subtype.comp
      (pCore 2 (centralizer ({z} : Set G))).subtype)

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Binary coordinates on the actual core, with the exact derived kernel and
with the supplied ordered generators, rather than a newly chosen frame. -/
public structure Coordinates (f : ParrottSylowGeneratorData n) where
  toHom : Core z →* Multiplicative Theory.GroupAction.BinaryFourTripleOrientation.V
  ker_iff : ∀ g : Core z, toHom g = 1 ↔ (g : G) ∈ Derived z
  map_a : ∀ g : Core z, (g : G) = f.a → (toHom g).toAdd = ![1,0,0,0]
  map_b : ∀ g : Core z, (g : G) = f.b → (toHom g).toAdd = ![0,1,0,0]
  map_c : ∀ g : Core z, (g : G) = f.c → (toHom g).toAdd = ![0,0,1,0]
  map_d : ∀ g : Core z, (g : G) = f.d → (toHom g).toAdd = ![0,0,0,1]

/-- Equality of coordinates is exactly equality modulo the actual derived core. -/
public theorem Coordinates.eq_iff {f : ParrottSylowGeneratorData n}
    (q : Coordinates f) (x y : Core z) :
    (q.toHom x).toAdd = (q.toHom y).toAdd ↔ (x : G)⁻¹ * (y : G) ∈ Derived z := by
  change q.toHom x = q.toHom y ↔ ((x⁻¹ * y : Core z) : G) ∈ Derived z
  rw [← q.ker_iff (x⁻¹ * y), map_mul, map_inv, inv_mul_eq_one]

/-- Conjugation by C_G(z) preserves the literal ambient core. -/
public theorem conjugate_mem (r g : G) (hr : r ∈ centralizer ({z} : Set G))
    (hg : g ∈ Core z) : r⁻¹ * g * r ∈ Core z := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  obtain ⟨gH, hgJ, rfl⟩ := hg
  have hh := (inferInstance : J.Normal).conj_mem gH hgJ (⟨r, hr⟩ : H)⁻¹
  simp only [inv_inv] at hh
  exact mem_map_of_mem H.subtype hh

/-- The chosen commutator convention commutes with any group homomorphism. -/
public theorem map_parrottCommutator {L : Type*} [Group L] (φ : G →* L) (x y : G) :
    φ (Tits.parrottCommutator x y) = Tits.parrottCommutator (φ x) (φ y) := by
  simp only [Tits.parrottCommutator, map_mul, map_inv]

/-- A literal triple commutator with value z or 1 retains that value under
conjugation by the centralizer of z. -/
public theorem conjugate_triple (r x y w : G)
    (hr : r ∈ centralizer ({z} : Set G)) (i : ℕ)
    (hval : Tits.parrottCommutator (Tits.parrottCommutator x y) w = z ^ i) :
    Tits.parrottCommutator
      (Tits.parrottCommutator (r⁻¹ * x * r) (r⁻¹ * y * r))
      (r⁻¹ * w * r) = z ^ i := by
  let φ : G →* G := (MulAut.conj r⁻¹).toMonoidHom
  have hfix : φ z = z := by
    change r⁻¹ * z * (r⁻¹)⁻¹ = z
    have hc : Commute r z := mem_centralizer_singleton_iff.mp hr
    rw [inv_inv, hc.inv_left.eq]
    group
  have hh := congrArg φ hval
  rw [map_parrottCommutator, map_parrottCommutator, map_pow, hfix] at hh
  simpa only [φ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hh

end ParrottCore

namespace ParrottSylowGeneratorData
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
variable (f : ParrottSylowGeneratorData n)

/-- The missing zero entry in the d-row of the derived pairing follows from
involutivity of d and v and the equation [d,b]=v. -/
public theorem core_commute_d_v : Commute f.d n.v := by
  have hd : f.d⁻¹ = f.d := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using f.d_sq)
  have hv : n.v⁻¹ = n.v := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using f.v_sq)
  have heq : f.d * n.v = f.b⁻¹ * f.d * f.b := by
    rw [← f.eq03_db]
    simp only [Tits.parrottCommutator]
    group
  have heq' := congrArg Inv.inv heq
  simp only [mul_inv_rev, hd, hv, inv_inv] at heq'
  exact heq.trans (by simpa only [mul_assoc] using heq'.symm)

/-- The five group-valued entries underlying the binary orientation certificate. -/
public theorem core_orientation_triple_entries :
    Tits.parrottCommutator (Tits.parrottCommutator f.a f.b) f.c = 1 ∧
    Tits.parrottCommutator (Tits.parrottCommutator f.a f.c) f.b = 1 ∧
    Tits.parrottCommutator (Tits.parrottCommutator f.a f.d) f.c = 1 ∧
    Tits.parrottCommutator (Tits.parrottCommutator f.b f.c) f.c = z ∧
    Tits.parrottCommutator (Tits.parrottCommutator f.b f.c) f.d = 1 := by
  have hcu := (Tits.parrottCommutator_eq_one_iff _ _).mp f.eq09_cu
  have hct := (Tits.parrottCommutator_eq_one_iff _ _).mp f.eq10_ct
  have hdu := (Tits.parrottCommutator_eq_one_iff _ _).mp f.eq08_du
  have hbv : Commute f.b n.v := by
    rw [← f.eq03_b]
    exact Commute.self_pow _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [f.eq05_ab]
    exact (Tits.parrottCommutator_eq_one_iff _ _).mpr hct.symm
  · rw [f.eq12_ac]
    exact (Tits.parrottCommutator_eq_one_iff _ _).mpr (hbv.mul_right f.comm_bt).symm
  · rw [f.eq11_ad]
    exact (Tits.parrottCommutator_eq_one_iff _ _).mpr hcu.symm
  · rw [f.eq15_bc]
    apply (Tits.parrottCommutator_eq_iff _ _ _).mpr
    have hcv := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq10_cv
    have hvc : n.v * f.c = f.c * n.v * z := by
      calc
        _ = (n.v * f.c * z) * z := by rw [mul_assoc, ← pow_two, f.z_sq]; simp
        _ = _ := by rw [← hcv]
    calc
      (f.u * n.v) * f.c = f.u * (n.v * f.c) := by group
      _ = f.u * (f.c * n.v * z) := by rw [hvc]
      _ = f.c * (f.u * n.v) * z := by simp only [← mul_assoc]; rw [hcu.symm.eq]
  · rw [f.eq15_bc]
    exact (Tits.parrottCommutator_eq_one_iff _ _).mpr
      (hdu.mul_right f.core_commute_d_v).symm

/-- The complete pairing of the supplied core and derived generators is
antidiagonal, with its four nonidentity entries equal to the original z. -/
public theorem core_derived_pairing_entries (i j : Fin 4) :
    Tits.parrottCommutator (![f.a,f.b,f.c,f.d] i) (![n.t,n.v,f.u,f.w] j) =
      z ^ (if i.val + j.val = 3 then 1 else 0) := by
  have hat := (Tits.parrottCommutator_eq_one_iff _ _).mpr f.comm_at
  have hav := (Tits.parrottCommutator_eq_one_iff _ _).mpr f.comm_av
  have hau := (Tits.parrottCommutator_eq_one_iff _ _).mpr f.comm_au
  have hbt := (Tits.parrottCommutator_eq_one_iff _ _).mpr f.comm_bt
  have hbv := (Tits.parrottCommutator_eq_one_iff _ _).mpr
    (show Commute f.b n.v by rw [← f.eq03_b]; exact Commute.self_pow _ _)
  have hdv := (Tits.parrottCommutator_eq_one_iff _ _).mpr f.core_commute_d_v
  fin_cases i <;> fin_cases j <;>
    simp [hat, hav, hau, hbt, hbv, hdv, f.eq02_aw, f.eq02_bu, f.eq02_bw,
      f.eq10_ct, f.eq10_cv, f.eq09_cu, f.eq09_cw, f.eq03_dt, f.eq08_du, f.eq07_dw]

private theorem reverse_commutator_of_square_one {a b c : G} (heq : Tits.parrottCommutator a b = c)
    (hc : c ^ 2 = 1) : Tits.parrottCommutator b a = c := by
  have hi : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hc)
  rw [← hi, ← heq]
  simp only [Tits.parrottCommutator, mul_inv_rev, inv_inv]
  group

/-- The complete commutator table of a,b,c,d, as actual ambient group
equalities before passage to any quotient. -/
public theorem core_bracket_entries (i j : Fin 4) :
    Tits.parrottCommutator (![f.a,f.b,f.c,f.d] i) (![f.a,f.b,f.c,f.d] j) =
      (![![1,n.t,n.v*n.t,f.u], ![n.t,1,f.u*n.v,n.v],
         ![n.v*n.t,f.u*n.v,1,f.w*f.u], ![f.u,n.v,f.w*f.u,1]] i j) := by
  have hba := reverse_commutator_of_square_one f.eq05_ab f.t_sq
  have hca := reverse_commutator_of_square_one f.eq12_ac (by rw [f.comm_tv.symm.mul_pow, f.v_sq, f.t_sq, mul_one])
  have hda := reverse_commutator_of_square_one f.eq11_ad f.u_sq
  have hcb := reverse_commutator_of_square_one f.eq15_bc (by rw [f.comm_vu.symm.mul_pow, f.u_sq, f.v_sq, mul_one])
  have hbd := reverse_commutator_of_square_one f.eq03_db f.v_sq
  have hdc := reverse_commutator_of_square_one f.eq14_cd (by rw [f.comm_uw.symm.mul_pow, f.w_sq, f.u_sq, mul_one])
  have hself (x : G) : Tits.parrottCommutator x x = 1 := by
    exact (Tits.parrottCommutator_eq_one_iff _ _).mpr (Commute.refl x)
  fin_cases i <;> fin_cases j <;>
    simp [f.eq05_ab, f.eq12_ac, f.eq11_ad, f.eq15_bc, f.eq03_db, f.eq14_cd,
      hba, hca, hda, hcb, hbd, hdc, hself]

end ParrottSylowGeneratorData
end Stellmacher.Recognition

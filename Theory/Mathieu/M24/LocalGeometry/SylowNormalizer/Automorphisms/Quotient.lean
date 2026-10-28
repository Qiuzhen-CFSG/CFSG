module

public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Automorphisms.Coordinates
public import Theory.GroupTheory.PGroup.FrattiniProfile

/-!
# Binary model of the Frattini quotient

The four marked generators identify the quotient with four binary bits.
The power-profile coloring permits only automorphisms whose square is the
identity. The finite certificate concerns this quotient of order sixteen.

Source context: Aschbacher–Smith, printed p.511; GLS3, Table 5.3e.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.AutomorphismData
open Theory.GroupTheory

/-- Binary masks with their own group structure, separate from arithmetic on `Fin 16`. -/
structure Binary where
  val : Fin 16
  deriving DecidableEq

def binaryEquivFin : Binary ≃ Fin 16 where
  toFun := Binary.val
  invFun := Binary.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Binary := Fintype.ofEquiv (Fin 16) binaryEquivFin.symm

instance : CommGroup Binary where
  mul i j := ⟨xor i.val j.val⟩
  one := ⟨0⟩
  inv := id
  mul_assoc := by decide +kernel
  one_mul := by decide +kernel
  mul_one := by decide +kernel
  inv_mul_cancel := by decide +kernel
  mul_comm := by decide +kernel

noncomputable def quotientHom (hcard : Nat.card candidate = 1024) :
    Binary →* candidate ⧸ frattini candidate where
  toFun i := QuotientGroup.mk' _ (outer i.val)
  map_one' := by change QuotientGroup.mk' _ (outer 0) = 1; rw [outer_zero, map_one]
  map_mul' i j := by
    change QuotientGroup.mk' _ (outer (xor i.val j.val)) = _
    rw [← map_mul, outer_mul, map_mul]
    have hp : QuotientGroup.mk' (frattini candidate) (phi (factor i.val j.val)) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [← phiSubgroup_eq_frattini hcard]
      exact phi_mem _
    rw [hp, mul_one]

theorem phi_mk (hcard : Nat.card candidate = 1024) (j : Fin 64) :
    QuotientGroup.mk' (frattini candidate) (phi j) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [← phiSubgroup_eq_frattini hcard]
  exact phi_mem _

theorem quotientHom_bijective (hcard : Nat.card candidate = 1024) :
    Function.Bijective (quotientHom hcard) := by
  constructor
  · intro i j hij
    have hh : (outer i.val)⁻¹ * outer j.val ∈ phiSubgroup := by
      rw [phiSubgroup_eq_frattini hcard]
      exact QuotientGroup.eq.mp hij
    obtain ⟨k,hk⟩ := (mem_phiSubgroup _).mp hh
    have he : full (i.val,k) = full (j.val,0) := by
      simp only [full]
      rw [hk, phi_zero]
      simp
    exact congrArg Binary.mk (congrArg Prod.fst (full_injective he))
  · intro z
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (frattini candidate) z
    obtain ⟨⟨i,j⟩,rfl⟩ := (full_bijective hcard).surjective g
    refine ⟨⟨i⟩, ?_⟩
    change QuotientGroup.mk' _ (outer i) = QuotientGroup.mk' _ (outer i * phi j)
    rw [map_mul, phi_mk hcard, mul_one]

noncomputable def quotientEquiv (hcard : Nat.card candidate = 1024) :
    (candidate ⧸ frattini candidate) ≃* Binary :=
  (MulEquiv.ofBijective (quotientHom hcard) (quotientHom_bijective hcard)).symm

theorem quotientEquiv_full (hcard : Nat.card candidate = 1024) (i : Fin 16) (j : Fin 64) :
    quotientEquiv hcard (QuotientGroup.mk' _ (full (i,j))) = (⟨i⟩ : Binary) := by
  apply (quotientEquiv hcard).symm.injective
  rw [MulEquiv.symm_apply_apply]
  change QuotientGroup.mk' _ (outer i * phi j) = QuotientGroup.mk' _ (outer i)
  rw [map_mul, phi_mk hcard, mul_one]

def binaryGen (i : Fin 4) : Binary := ⟨(![1,2,4,8] : Fin 4 → Fin 16) i⟩
def binaryWord (x : Binary) : List (Fin 4) := outerWord x.val
def binaryColor (x : Binary) : Fin 5 := color x.val

theorem binaryWord_eval : ∀ x, evalWord binaryGen (binaryWord x) = x := by
  decide +kernel

def classA (i : Fin 7) : Binary := ⟨(![1,6,7,9,12,13,14] : Fin 7 → Fin 16) i⟩
def classB (i : Fin 2) : Binary := ⟨(![2,4] : Fin 2 → Fin 16) i⟩
def classC (i : Fin 5) : Binary := ⟨(![5,8,10,11,15] : Fin 5 → Fin 16) i⟩
def restrictedImages (a : Fin 7) (b c : Fin 2) (d : Fin 5) : Fin 4 → Binary :=
  ![classA a, classB b, classB c, classC d]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem restricted_certificate : ∀ a b c d,
    let v := restrictedImages a b c d
    (∀ x, binaryColor (evalWord v (binaryWord x)) = binaryColor x) →
    (∀ x, evalWord v (binaryWord x) = 1 ↔ x = 1) →
    ∀ j, (fun x => evalWord v (binaryWord x))^[2] (binaryGen j) = binaryGen j := by
  decide +kernel

theorem binary_certificate : ProfileWordCertificate binaryGen binaryWord binaryColor 2 := by
  intro v hc hi
  have he (j : Fin 4) : evalWord v (binaryWord (binaryGen j)) = v j := by
    fin_cases j <;> exact mul_one _
  have h0 := hc (binaryGen 0)
  have h1 := hc (binaryGen 1)
  have h2 := hc (binaryGen 2)
  have h3 := hc (binaryGen 3)
  rw [he] at h0 h1 h2 h3
  have ha : ∀ x : Binary, binaryColor x = binaryColor (binaryGen 0) →
      ∃ a, classA a = x := by decide +kernel
  have hb : ∀ x : Binary, binaryColor x = binaryColor (binaryGen 1) →
      ∃ a, classB a = x := by decide +kernel
  have hd : ∀ x : Binary, binaryColor x = binaryColor (binaryGen 3) →
      ∃ a, classC a = x := by decide +kernel
  obtain ⟨a,ha⟩ := ha _ h0
  obtain ⟨b,hb'⟩ := hb _ h1
  obtain ⟨c,hc'⟩ := hb _ h2
  obtain ⟨d,hd⟩ := hd _ h3
  have hv : v = restrictedImages a b c d := by
    funext j
    fin_cases j
    · exact ha.symm
    · exact hb'.symm
    · exact hc'.symm
    · exact hd.symm
  subst v
  exact restricted_certificate a b c d hc hi

end Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.AutomorphismData

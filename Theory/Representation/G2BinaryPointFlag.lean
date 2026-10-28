module
public import Theory.Representation.G2.RestrictedModules.NaturalCoordinates
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Restriction
public import Mathlib.LinearAlgebra.Pi

/-!
# The invariant flag of the binary derived point parabolic

On the literal natural six-space for G₂(2), the derived point parabolic has
exactly three invariant subspaces containing the marked three-space: that
three-space, the marked hyperplane, and the whole module. Three actual root
and Weyl elements already force this interval. The proof passes to the last
three coordinates, where two shears and a swap force its unique proper plane.

This is the point parabolic (the native `derivedSecondAmbient`), as required
in Aschbacher–Smith, Lemma 13.3.18, printed pp.894–895. The other native
parabolic is the plane parabolic and does not have this invariant interval.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.Restricted.NaturalCoordinates
open Atlas.G2.Explicit
abbrev F := ZMod 2
abbrev W := Fin 6 → F
abbrev Q := Fin 3 → F

def tail : W →ₗ[F] Q := LinearMap.pi ![LinearMap.proj 3,LinearMap.proj 4,LinearMap.proj 5]
def seed : Submodule F W := tail.ker
def hyperplane : Submodule F W := (LinearMap.proj (5 : Fin 6)).ker

@[simp] theorem mem_seed (v : W) : v∈seed ↔ v 3=0 ∧ v 4=0 ∧ v 5=0 := by
  change tail v=0 ↔ _
  constructor
  · intro h
    exact ⟨congrFun h 0,congrFun h 1,congrFun h 2⟩
  · rintro ⟨h3,h4,h5⟩
    ext i
    fin_cases i <;> simp [tail,h3,h4,h5]

@[simp] theorem mem_hyperplane (v : W) : v∈hyperplane ↔ v 5=0 := Iff.rfl

def qPlane : Submodule F Q := (LinearMap.proj (2 : Fin 3)).ker
def e (i : Fin 3) : Q := Pi.single i 1

def shear (v : Q) : Q := ![v 0+v 1,v 1,v 2]
def swap (v : Q) : Q := ![v 1,v 0,v 2]
def shift (v : Q) : Q := ![v 0+v 2,v 1,v 2]

private theorem vector_decomposition (v : Q) : v = v 0 • e 0 + v 1 • e 1 + v 2 • e 2 := by
  ext i
  fin_cases i <;> simp [e]

private theorem one_mem_of_nonzero (S : Submodule F Q)
    (hE : ∀v∈S,shear v∈S) (hR : ∀v∈S,swap v∈S) (hD : ∀v∈S,shift v∈S)
    (hne : S ≠ ⊥) : e 0∈S ∧ e 1∈S := by
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h0 : e 0∈S := by
    by_cases h1 : v 1=0
    · by_cases h2 : v 2=0
      · have h : v 0 ≠ 0 := by
          intro hh
          apply hv0
          ext i
          fin_cases i <;> simp [hh,h1,h2]
        have ho : v 0=1 := by
          have hp : ∀x:F,x=0∨x=1 := by decide +kernel
          exact (hp _).resolve_left h
        have he : v=e 0 := by rw [vector_decomposition v,ho,h1,h2]; simp
        exact he ▸ hv
      · have ho : v 2=1 := ((by decide +kernel : ∀x:F,x=0∨x=1) _).resolve_left h2
        have he : shift v-v=e 0 := by ext i; fin_cases i <;> simp [shift,e,ho]
        exact he ▸ S.sub_mem (hD v hv) hv
    · have ho : v 1=1 := ((by decide +kernel : ∀x:F,x=0∨x=1) _).resolve_left h1
      have he : shear v-v=e 0 := by ext i; fin_cases i <;> simp [shear,e,ho]
      exact he ▸ S.sub_mem (hE v hv) hv
  refine ⟨h0,?_⟩
  have he : swap (e 0)=e 1 := by ext i; fin_cases i <;> simp [swap,e]
  exact he ▸ hR _ h0

/-- The actual point-parabolic quotient has just the natural plane between zero and top. -/
theorem quotient_invariant_cases (S : Submodule F Q)
    (hE : ∀v∈S,shear v∈S) (hR : ∀v∈S,swap v∈S) (hD : ∀v∈S,shift v∈S) :
    S=⊥ ∨ S=qPlane ∨ S=⊤ := by
  by_cases h : S=⊥
  · exact Or.inl h
  obtain ⟨h0,h1⟩ := one_mem_of_nonzero S hE hR hD h
  have hp : qPlane≤S := by
    intro v hv
    have hv2 : v 2=0 := hv
    rw [vector_decomposition v,hv2]
    simpa using S.add_mem (S.smul_mem (v 0) h0) (S.smul_mem (v 1) h1)
  by_cases hs : S≤qPlane
  · exact Or.inr (Or.inl (le_antisymm hs hp))
  · obtain ⟨v,hv,hn⟩ := Set.not_subset.mp hs
    have ho : v 2=1 := ((by decide +kernel : ∀x:F,x=0∨x=1) _).resolve_left hn
    have h2 : e 2∈S := by
      have he : v-(v 0•e 0+v 1•e 1)=e 2 := by
        ext i
        fin_cases i <;> simp [e,ho]
      exact he ▸ S.sub_mem hv (S.add_mem (S.smul_mem _ h0) (S.smul_mem _ h1))
    right; right
    apply top_unique
    intro v _
    rw [vector_decomposition v]
    exact S.add_mem (S.add_mem (S.smul_mem _ h0) (S.smul_mem _ h1)) (S.smul_mem _ h2)

/-- The three quotient operators are literal natural G₂ root/Weyl actions. -/
theorem tail_rootE (v : W) : tail (Restricted.NaturalCoordinates.action F (rootE 1) v)=shear (tail v) := by
  ext i
  fin_cases i <;> simp [tail,shear]

theorem tail_weylR (v : W) : tail (Restricted.NaturalCoordinates.action F weylR v)=swap (tail v) := by
  ext i
  fin_cases i <;> simp [tail,swap]

theorem tail_rootCD (v : W) : tail (Restricted.NaturalCoordinates.action F (rootC 1*rootD 1) v)=shift (tail v) := by
  rw [map_mul,Module.End.mul_apply]
  ext i
  fin_cases i <;> simp [tail,shift]

/-- Above the marked seed, invariance under three actual actors leaves precisely
V₃, V₅ and V. The actors all belong to the derived point parabolic. -/
theorem invariant_interval (S : Submodule F W) (hseed : seed≤S)
    (hE : ∀v∈S,Restricted.NaturalCoordinates.action F (rootE 1) v∈S)
    (hR : ∀v∈S,Restricted.NaturalCoordinates.action F weylR v∈S)
    (hD : ∀v∈S,Restricted.NaturalCoordinates.action F (rootC 1*rootD 1) v∈S) :
    S=seed ∨ S=hyperplane ∨ S=⊤ := by
  have heq : (S.map tail).comap tail=S := by
    rw [Submodule.comap_map_eq]
    exact sup_eq_left.mpr hseed
  have hqE : ∀v∈S.map tail,shear v∈S.map tail := by
    rintro v ⟨x,hx,rfl⟩
    exact ⟨_,hE x hx,tail_rootE x⟩
  have hqR : ∀v∈S.map tail,swap v∈S.map tail := by
    rintro v ⟨x,hx,rfl⟩
    exact ⟨_,hR x hx,tail_weylR x⟩
  have hqD : ∀v∈S.map tail,shift v∈S.map tail := by
    rintro v ⟨x,hx,rfl⟩
    exact ⟨_,hD x hx,tail_rootCD x⟩
  rcases quotient_invariant_cases (S.map tail) hqE hqR hqD with h|h|h
  · left
    rw [← heq,h]
    rfl
  · right; left
    rw [← heq,h]
    rfl
  · right; right
    rw [← heq,h,Submodule.comap_top]

/-- The quotient shears and swap occur in the same actual derived point parabolic. -/
theorem point_actor_membership :
    rootE (1:F) ∈ BinaryParabolicPair.derivedSecondAmbient ∧
      (weylR:Model F) ∈ BinaryParabolicPair.derivedSecondAmbient ∧
      rootC (1:F)*rootD 1 ∈ BinaryParabolicPair.derivedSecondAmbient := by
  refine ⟨⟨rootE_mem_parabolic _,?_⟩,⟨weylR_mem_parabolic,?_⟩,⟨?_,?_⟩⟩
  · rw [BinaryParabolicPair.commutator_eq_longRootClosure]
    exact BinaryException.rootE_in_H 1
  · rw [BinaryParabolicPair.commutator_eq_longRootClosure]
    exact BinaryException.weylR_in_H
  · apply unipotent_le_parabolic
    exact (unipotent (K:=F)).mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · rw [BinaryParabolicPair.commutator_eq_longRootClosure]
    change rootC (1:F)*rootD 1 ∈ BinaryException.H
    rw [← QuotientGroup.eq_one_iff]
    change BinaryException.projection (rootC 1*rootD 1)=1
    rw [map_mul,BinaryException.project_C_eq_D,← map_mul,rootD_add,
      show (1:F)+1=0 by decide,rootD_zero,map_one]

/-- The source first point normalizer preserves no extra subspace above V₃. -/
theorem point_invariant_interval (S : Submodule F W) (hseed : seed≤S)
    (hS : ∀a∈BinaryParabolicPair.derivedSecondAmbient,
      ∀v∈S,Restricted.NaturalCoordinates.action F a v∈S) :
    S=seed ∨ S=hyperplane ∨ S=⊤ :=
  invariant_interval S hseed (hS _ point_actor_membership.1)
    (hS _ point_actor_membership.2.1) (hS _ point_actor_membership.2.2)

private def hyperplaneEquiv : hyperplane ≃ (Fin 5→F) where
  toFun v i := v.val i.castSucc
  invFun w := ⟨![w 0,w 1,w 2,w 3,w 4,0],rfl⟩
  left_inv v := by
    apply Subtype.ext
    have hv := (mem_hyperplane v.val).mp v.prop
    ext i
    fin_cases i <;> simp [hv]
  right_inv w := by ext i; fin_cases i <;> rfl

/-- The literal invariant hyperplane has the required source order 32. -/
theorem card_hyperplane : Nat.card hyperplane=32 := by
  rw [Nat.card_congr hyperplaneEquiv]
  simp

end Atlas.G2.Natural.BinaryPointFlag

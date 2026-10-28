module
public import Theory.Representation.SU3.BinaryDegree
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.SubrepresentationLattice

/-!
# Irreducibility at the binary unitary degree minimum

Every nontrivial binary representation of SU3(2^n), n >= 2, has dimension
at least 6n. If an action of dimension at most 6n had a nonzero proper invariant
subspace, its subspace and quotient actions would both be trivial. Their
extension has abelian image, and perfectness then makes the whole action trivial.

This supplies irreducibility for the literal effective Frattini section in the
initial equal-unitary configuration of Fong--Seitz I (6D), printed p.42.
The existing minimum-degree bound and concrete perfectness are retained.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups
namespace Representation.SU3.BinaryDegree

private theorem trivial_of_trivial_subquotient
    {G W : Type*} [Group G] [Group.IsPerfect G]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (A : Subrepresentation ρ)
    (hA : A.toRepresentation=1) (hQ : A.quotientRepresentation=1) : ρ=1 := by
  have hfix (g : G) (v : W) (hv : v ∈ A) : ρ g v=v :=
    congrArg Subtype.val (DFunLike.congr_fun (DFunLike.congr_fun hA g) (⟨v,hv⟩ : A))
  have hdiff (g : G) (v : W) : ρ g v-v ∈ A := by
    apply (Submodule.Quotient.mk_eq_zero A.toSubmodule).mp
    change A.toSubmodule.mkQ (ρ g v-v)=0
    rw [map_sub,←A.quotientRepresentation_mk]
    exact sub_eq_zero.mpr (DFunLike.congr_fun (DFunLike.congr_fun hQ g) (A.toSubmodule.mkQ v))
  have hcomm (g h : G) : ρ g*ρ h=ρ h*ρ g := by
    ext v
    have hg := hfix g (ρ h v-v) (hdiff h v)
    have hh := hfix h (ρ g v-v) (hdiff g v)
    simp only [map_sub] at hg hh
    change ρ g (ρ h v)=ρ h (ρ g v)
    rw [sub_eq_iff_eq_add] at hg hh
    rw [hg,hh]
    abel
  let f:=ρ.toHomUnits
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : IsMulCommutative f.range := ⟨⟨by
    rintro ⟨_,g,rfl⟩ ⟨_,h,rfl⟩
    apply Subtype.ext
    exact Units.ext (hcomm g h)⟩⟩
  let : Subsingleton f.range := inferInstance
  ext g v
  have he : (⟨f g,⟨g,rfl⟩⟩ : f.range)=1 := Subsingleton.elim _ _
  exact LinearMap.congr_fun (congrArg (fun z : f.range => z.val.val) he) v

/-- Attaining the nontrivial unitary degree minimum forces irreducibility.
Perfectness rules out a nontrivial extension of two trivial actions. -/
theorem irreducible_of_finrank_le
    {F V : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) J.specialSubgroup V)
    (hne : ∃ g,ρ g≠1) (hd : Module.finrank (ZMod 2) V ≤ 6*n) :
    ρ.IsIrreducible := by
  let : Group.IsPerfect J.specialSubgroup := isPerfect_specialSubgroup J hn hcard hconj
  have hnt : ρ ≠ 1 := by rintro rfl; obtain ⟨g,hg⟩:=hne; exact hg rfl
  let : Nontrivial V := by
    by_contra! hh
    let : Subsingleton V := hh
    exact hnt (by ext g v; exact Subsingleton.elim _ _)
  refine ⟨?_⟩
  intro W
  by_contra! hw
  have hb : W.toSubmodule ≠ ⊥ := fun h => hw.1 (Subrepresentation.toSubmodule_injective h)
  have ht : W.toSubmodule ≠ ⊤ := fun h => hw.2 (Subrepresentation.toSubmodule_injective h)
  have hp : 0 < Module.finrank (ZMod 2) W.toSubmodule :=
    Nat.pos_of_ne_zero (fun h => hb (Submodule.finrank_eq_zero.mp h))
  have hlt := Submodule.finrank_lt ht
  have hsum := Submodule.finrank_quotient_add_finrank W.toSubmodule
  have hW : W.toRepresentation=1 := by
    apply MonoidHom.ext
    intro g
    by_contra hg
    have hl:=finrank_ge J hn hcard hconj W.toRepresentation ⟨g,hg⟩
    omega
  have hQ : W.quotientRepresentation=1 := by
    apply MonoidHom.ext
    intro g
    by_contra hg
    have hl:=finrank_ge J hn hcard hconj W.quotientRepresentation ⟨g,hg⟩
    omega
  exact hnt (trivial_of_trivial_subquotient ρ W hW hQ)
end Representation.SU3.BinaryDegree

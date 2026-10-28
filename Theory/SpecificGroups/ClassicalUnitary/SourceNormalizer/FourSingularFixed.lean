module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularity

/-!
# Singular vectors fixed by an inner unitary root actor

In the Hermitian module for SL₂(q²), a singular vector fixed by one
nonidentity element of a specified Sylow two-subgroup is fixed by that
whole Sylow. For an upper transvection, the fixed-vector equation makes
the bottom diagonal entry zero; zero determinant then makes the
off-diagonal entry zero. Sylow conjugacy transports this calculation
without changing the specified Sylow. Its common fixed line has order q.

The ambient application identifies this line with the original long-root
group, and uses ambient nonfusion to preserve its intersection with the
full outer centralizer's center–derived subgroup.
Source: Aschbacher–Smith F.4.35,37, printed pp.292–293, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Matrix Matrix.SpecialLinearGroup
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne
open Representation.OrthogonalFourMinus.CartanFixed
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularFixed
variable (m : ℕ) [NeZero m]

private theorem upper_singular_fixed (u : Field m) (hu : u ≠ 0)
    (X : Space m) (hs : form m X=0) (hx : action m (upper m u) X=X) :
    ∀ g ∈ upperUnipotent (Field m), action m g X=X := by
  have hb := ((root_fixed_iff m hu X).mp hx).1
  have hz : X.val 0 1=0 := by
    have hd := congrArg Subtype.val hs
    change X.val.det=0 at hd
    have hz' : X.val 0 1 * conjugation m (X.val 0 1)=0 := by
      rw [entry_conjugate]
      simpa only [Matrix.det_fin_two,hb,mul_zero,zero_sub,neg_eq_zero] using hd
    exact (mul_eq_zero.mp hz').elim id (fun hh => (map_eq_zero (conjugation m)).mp hh)
  intro g hg
  exact ((mem_fixedSpace_upper_iff m X).mpr ⟨hb,hz⟩) ⟨g,hg⟩

/-- Within a specified inner Sylow, one nonidentity element already detects
the common fixed line among singular Hermitian vectors. -/
theorem singular_fixed_member_iff
    (P : Sylow 2 (SpecialLinearGroup (Fin 2) (Field m)))
    (u : P) (hu : u.val ≠ 1) (X : Space m)
    (hx : action m u.val X=X) :
    form m X=0 ↔ ∀ g ∈ (P : Subgroup _), action m g X=X := by
  constructor
  · intro hs
    obtain ⟨a,ha⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) (Field m))
      (upperUnipotentSylow (Field m) 2) P
    have hP : (P : Subgroup _) =
        (upperUnipotent (Field m)).map (MulAut.conj a).toMonoidHom := by
      rw [←ha]; rfl
    have hum : u.val ∈ (P : Subgroup _) := u.property
    rw [hP] at hum
    obtain ⟨v,hv,he⟩ := hum
    obtain ⟨b,rfl⟩ := (mem_upperUnipotent _ v).mp hv
    change a*upper m b*a⁻¹=u.val at he
    have hb : b ≠ 0 := by
      rintro rfl
      apply hu
      change a*Matrix.SpecialLinearGroup.transvection _ 0*a⁻¹=u.val at he
      rw [transvection_coeff_zero,mul_one,mul_inv_cancel] at he
      exact he.symm
    have hfix : action m (upper m b) (action m a⁻¹ X)=action m a⁻¹ X := by
      have hh := congrArg (action m a⁻¹) hx
      rw [←he] at hh
      rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,
        Representation.inv_self_apply] at hh
      exact hh
    have hh := upper_singular_fixed m b hb (action m a⁻¹ X)
      (by rwa [form_preserved]) hfix
    intro g hg
    rw [hP] at hg
    obtain ⟨v,hv,rfl⟩ := hg
    change action m (a*v*a⁻¹) X=X
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,hh v hv]
    exact Representation.self_inv_apply _ _ _
  · exact FourSingularity.fixed_sylow_singular m P X

/-- The actual common fixed space of any inner Sylow has exactly q vectors. -/
theorem sylow_fixed_card
    (P : Sylow 2 (SpecialLinearGroup (Fin 2) (Field m))) :
    Nat.card {X : Space m // ∀ g ∈ (P : Subgroup _), action m g X=X}=2^m := by
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) (Field m))
    (upperUnipotentSylow (Field m) 2) P
  have hP : (P : Subgroup _) =
      (upperUnipotent (Field m)).map (MulAut.conj a).toMonoidHom := by
    rw [←ha]; rfl
  let U := Representation.invariants ((action m).comp (upperUnipotent (Field m)).subtype)
  have hf (X : Space m) : X ∈ U ↔
      ∀ g ∈ (P : Subgroup _), action m g (action m a X)=action m a X := by
    constructor
    · intro hx g hg
      rw [hP] at hg
      obtain ⟨v,hv,rfl⟩ := hg
      change action m (a*v*a⁻¹) (action m a X)=action m a X
      simp only [map_mul,Module.End.mul_apply,Representation.inv_self_apply]
      rw [show action m v X=X from hx ⟨v,hv⟩]
    · intro hx v
      change action m v.val X=X
      have hv : a*v.val*a⁻¹ ∈ (P : Subgroup _) := hP ▸ ⟨v.val,v.property,rfl⟩
      have hh := congrArg (action m a⁻¹) (hx _ hv)
      simpa only [map_mul,Module.End.mul_apply,Representation.inv_self_apply] using hh
  let e : U ≃ {X : Space m // ∀ g ∈ (P : Subgroup _), action m g X=X} :=
    { toFun X := ⟨action m a X,(hf X).mp X.property⟩
      invFun X := ⟨action m a⁻¹ X,(hf _).mpr (by
        rw [Representation.self_inv_apply]; exact X.property)⟩
      left_inv X := Subtype.ext (Representation.inv_self_apply _ _ _)
      right_inv X := Subtype.ext (Representation.self_inv_apply _ _ _) }
  rw [←Nat.card_congr e,Nat.card_congr (upperFixedEquivK m).toEquiv,card_fixedField]

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularFixed

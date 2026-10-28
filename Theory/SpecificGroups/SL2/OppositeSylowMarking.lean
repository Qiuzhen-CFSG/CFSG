module
public import Theory.SpecificGroups.SL2.FiveGeneratorRecognition

/-!
# Simultaneous coordinates for two distinct defining-characteristic Sylows

Conjugate the first Sylow to the upper unipotent group. A matrix carrying
that group to the second has a nonzero lower-left entry. Multiplying it
by an upper transvection kills its upper-left entry, so it carries the
upper root group onto all lower transvections while preserving the first
root group. This gives one marking for both full roots, over every finite
field, including the binary field.

The actual four-path radicals use these coordinates in the commuting
DGS source family, as the root-image input to (14.12)--(14.13).
Source: DGS, Groups and Graphs (1985), (14.3), p.212, and pp.217--218.
-/

public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
local notation "u" => transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one
local notation "v" => transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero

omit [Finite F] in
private theorem opposite_zero_conj_upper {g : SL(2,F)} (hg : g.val 0 0=0) (t : F) :
    g*u t*g⁻¹=v (-g.val 1 0^2*t) := by
  have hd : -(g.val 0 1*g.val 1 0)=1 := by
    simpa only [det_fin_two,hg,zero_mul,zero_sub] using g.property
  have key : g*u t=v (-g.val 1 0^2*t)*g := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply,Fin.sum_univ_two,transvection_coe,hg]
    linear_combination -g.val 1 0*t*hd
  rw [key,mul_assoc,mul_inv_cancel,mul_one]

/-- One inner marking sends the specified first Sylow to the full upper
root group and the specified second Sylow to every lower transvection. -/
theorem exists_opposite_sylow_marking (P Q : Sylow p SL(2,F)) (hne : P≠Q) :
    ∃ m : SL(2,F),
      (P : Subgroup SL(2,F)).map (MulAut.conj m).toMonoidHom=upperUnipotent F ∧
      ∀ y : SL(2,F), y∈(Q : Subgroup SL(2,F)).map (MulAut.conj m).toMonoidHom ↔
        ∃ t : F, v t=y := by
  let U := upperUnipotentSylow F p
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq SL(2,F) P U
  let Q' : Sylow p SL(2,F) := a • Q
  have hQU : Q'≠U := by
    intro he
    apply hne
    exact (MulAction.toPerm a).injective (ha.trans he.symm)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F) U Q'
  have hgc : g.val 1 0≠0 := by
    intro hz
    have hn : g∈normalizer (upperUnipotent F : Set SL(2,F)) :=
      (mem_rankOneBorel_iff g).mpr hz
    have hm := mem_normalizer_iff_map_conj_eq.mp hn
    have he : g • U=U := Sylow.ext hm
    exact hQU (hg.symm.trans he)
  let z := u (-g.val 0 0/g.val 1 0)
  let b := z*g
  have hzU : z∈upperUnipotent F := (mem_upperUnipotent F z).mpr ⟨_,rfl⟩
  have hzN := (upperUnipotent F).le_normalizer hzU
  have hb00 : b.val 0 0=0 := by
    simp [b,z,mul_apply,Fin.sum_univ_two,transvection_coe,hgc]
  have hb10 : b.val 1 0=g.val 1 0 := by
    simp [b,z,mul_apply,Fin.sum_univ_two,transvection_coe]
  have hP : (P : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom=upperUnipotent F :=
    congrArg Sylow.toSubgroup ha
  have hQ : (Q : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom=
      (upperUnipotent F).map (MulAut.conj g).toMonoidHom :=
    (congrArg Sylow.toSubgroup hg).symm
  have hcomp (x y : SL(2,F)) : (MulAut.conj (x*y)).toMonoidHom=
      (MulAut.conj x).toMonoidHom.comp (MulAut.conj y).toMonoidHom := by
    ext t
    simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,MonoidHom.comp_apply]
    group
  refine ⟨z*a,?_,?_⟩
  · rw [hcomp,←Subgroup.map_map,hP]
    exact mem_normalizer_iff_map_conj_eq.mp hzN
  · intro y
    rw [hcomp,←Subgroup.map_map,hQ,Subgroup.map_map,←hcomp]
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨t,rfl⟩ := (mem_upperUnipotent F x).mp hx
      exact ⟨_,(opposite_zero_conj_upper hb00 t).symm⟩
    · rintro ⟨t,rfl⟩
      refine ⟨u (-t/g.val 1 0^2),(mem_upperUnipotent F _).mpr ⟨_,rfl⟩,?_⟩
      change b*u (-t/g.val 1 0^2)*b⁻¹=v t
      rw [opposite_zero_conj_upper hb00,hb10]
      congr 1
      field_simp
end Matrix.SpecialLinearGroup

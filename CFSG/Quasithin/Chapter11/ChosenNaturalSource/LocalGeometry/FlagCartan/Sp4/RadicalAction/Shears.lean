module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.RadicalAction.Operators

/-!
# Two-power plane fixers in the binary symplectic normalizer

Fixing the full plane removes the field twist. The multiplier of the
remaining scalar-symplectic operator has two-power order, so characteristic
two makes it one. The resulting matrix belongs to the standard shear
radical, as detected by its upper-left and lower-left blocks.

Source: the natural-action calculation used in Aschbacher--Smith 11.2.4,
printed pp.769--770. These lemmas feed the original radical action.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open scoped MatrixGroups IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.RadicalAction.Model
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

theorem inner_of_twoPower_fixes_plane (s : naturalNormalizer (F := F))
    (hfix : ∀ v ∈ plane F, s.val v = v) (k : ℕ) (hk : s.val^(2^k)=1) :
    ∃ g : Sp F, ∀ v, s.val v = g • v := by
  have he0 : (e (F := F) 0) ≠ 0 := by
    intro he
    have hh := congrFun he (.inl 0)
    simp [Theory.SpecificGroups.SymplecticFour.e] at hh
  obtain ⟨a,g,hg⟩ := SymplecticNaturalNormalizer.scalar_symplectic_of_fixes_field_line
    s (e 0) he0 (fun c => hfix _ ((plane F).smul_mem c (e_mem_plane 0)))
  have hform (v w : Vector F) : form F (s.val v) (s.val w) =
      (a.val*a.val)*form F v w := by
    rw [hg,hg]
    change form F (a.val • (g • v)) (a.val • (g • w)) = _
    rw [LinearMap.map_smul₂,map_smul,preserves_form]
    simp only [smul_eq_mul]
    ring
  have hpow (n : ℕ) (v w : Vector F) :
      form F ((s.val^n) v) ((s.val^n) w) = (a.val*a.val)^n*form F v w := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',LinearEquiv.mul_apply,LinearEquiv.mul_apply,hform,ih,pow_succ']
      ring
  have hp : (a.val*a.val)^(2^k)=1 := by
    have h := hpow (2^k) (e 0) (Pi.single (.inr 0) 1)
    rw [hk] at h
    simpa [form_apply,Theory.SpecificGroups.SymplecticFour.e,Fin.sum_univ_two] using h.symm
  have ha2 : a.val*a.val=1 := by
    have hh : (a.val*a.val-1)^(2^k)=0 := by
      rw [sub_pow_char_pow,hp,one_pow,sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ (by decide))).mp hh)
  have ha : a.val=1 := CharTwo.sq_injective (by simpa only [pow_two,one_mul] using ha2)
  refine ⟨g,fun v => ?_⟩
  change s.val v = symplecticNatural 2 g v
  simpa [ha] using hg v

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
theorem mem_planeRadical_of_fixes (g : Sp F) (hfix : ∀ v ∈ plane F, g • v = v) :
    g ∈ Plane.radical.map planeLocal.subtype := by
  have hA : g.val.toBlocks₁₁ = 1 := by
    ext i j
    have h := congrFun (hfix (e j) (e_mem_plane j)) (.inl i)
    simpa [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Theory.SpecificGroups.SymplecticFour.e,Matrix.mulVec_single,Matrix.toBlocks₁₁,Matrix.one_apply,Pi.single_apply] using h
  have hP : g ∈ planeParabolic := by
    rw [mem_planeParabolic_iff]
    intro i j
    have h := congrFun (hfix (e j) (e_mem_plane j)) (.inr i)
    simpa [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Theory.SpecificGroups.SymplecticFour.e,Matrix.mulVec_single] using h
  have hg : g ∈ planeLocal := (Plane.mem_local_iff g).mpr ⟨hP,by rw [hA]; exact Matrix.det_one⟩
  refine ⟨⟨g,hg⟩,?_,rfl⟩
  apply Subtype.ext
  exact hA

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.RadicalAction.Model

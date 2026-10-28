module
public import Theory.Representation.Suzuki.NaturalCentralizer
public import Theory.Representation.Suzuki.SmallDegree.Models
public import Theory.Representation.Suzuki.SmallDegree.Classification.SimpleDistinct.WeightArithmetic

/-!
# Odd stabilizers of Sylow-fixed Suzuki natural vectors

The root-fixed line is the first coordinate line. Its nonzero-vector
stabilizer lies in the Borel; the faithful split-torus weight forces it
into the root two-group. Thus any odd-order stabilizer is trivial.
Sylow conjugacy transports the statement to the originally marked action.

Consumer: both original Hall projections in the centralizing-Z branch of
Aschbacher--Smith 10.2.3. Source: 10.1.2(5), printed p.742, and
Huppert--Blackburn, Finite Groups III, XI.3.1 and XI.3.3.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Representation.SuzukiNatural
open BenderSuzuki BenderSuzuki.MatrixGroups PFAppendixIII

private theorem fixes_first_mem_root (m : ℕ) (hm : 0 < m)
    (g : SuzukiMatrixGroup m)
    (hg : natural m g ![1,0,0,0] = ![1,0,0,0]) : g ∈ SuzukiRootSubgroup m := by
  classical
  let : Fintype (F m) := Fintype.ofFinite _
  have hb : g ∈ SuzukiBorelSubgroup m := by
    apply (mem_suzukiBorelSubgroup_iff_fix_infinity m hm g).mpr
    rw [Projectivization.smul_mk]
    change Projectivization.mk _ (natural m g ![1,0,0,0]) _ = _
    simp only [hg]
  have hp : (SuzukiBorelSubgroup m : Set (SuzukiMatrixGroup m)) =
      (SuzukiRootSubgroup m : Set _) * (SuzukiSplitTorus m : Set _) := by
    rw [←Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (suzukiSplitTorus_le_normalizer_root m),←suzukiBorelSubgroup_eq_sup]
  have hgb : g ∈ (SuzukiBorelSubgroup m : Set (SuzukiMatrixGroup m)) := hb
  rw [hp] at hgb
  obtain ⟨r,hr,t,ht,hrt⟩ := hgb
  obtain ⟨a,b,hab⟩ := (mem_suzukiRootSubgroup_iff m r).mp hr
  obtain ⟨u,hu⟩ := (mem_suzukiSplitTorus_iff m t).mp ht
  have hweight : (u : F m) ^ (1+2^m) = 1 := by
    have hh := congrFun hg 0
    rw [←hrt] at hh
    simpa [natural_apply,hab,hu,SuzukiRootGL,SuzukiRootMatrix,SuzukiTorusGL,
      SuzukiTorusMatrix,Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_four] using hh
  have hcard : Nat.card (F m)ˣ = 2^(2*m+1)-1 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_units]
    rw [←Nat.card_eq_fintype_card]
    exact congrArg (·-1) (GaloisField.card 2 (2*m+1) (by omega))
  have hpw : u^(1+2^m) = 1 := Units.ext (by simpa using hweight)
  have hu1 : u = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by rw [hcard]; exact SuzukiSmallDegree.highestWeight_coprime m)
      (orderOf_dvd_of_pow_eq_one hpw) (orderOf_dvd_natCard u))
  have ht1 : t = 1 := by
    apply Subtype.ext
    rw [hu,hu1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SuzukiTorusGL,SuzukiTorusMatrix]
  change r * t = g at hrt
  rw [ht1,mul_one] at hrt
  exact hrt ▸ hr

/-- An odd element fixing a nonzero root-fixed vector is the identity. -/
theorem odd_eq_one_of_fixes_root_fixed (m : ℕ) (hm : 0 < m)
    (g : SuzukiMatrixGroup m) (hodd : Odd (orderOf g))
    (v : W m) (hv : v ≠ 0)
    (hU : ∀ u ∈ SuzukiRootSubgroup m, natural m u v = v)
    (hg : natural m g v = v) : g = 1 := by
  have hc := root_fixed_coordinates m v hU
  have hv0 : v 0 ≠ 0 := by
    intro hz
    apply hv
    rw [hc,hz]
    ext i
    fin_cases i <;> rfl
  have he : v = (v 0) • (![1,0,0,0] : W m) := by
    rw [hc]
    ext i
    fin_cases i <;> simp
  have hfirst : natural m g ![1,0,0,0] = ![1,0,0,0] := by
    apply smul_right_injective (M := W m) hv0
    change (v 0) • (SuzukiSmallDegree.naturalField m g) ![1,0,0,0] = _
    rw [←(SuzukiSmallDegree.naturalField m g).map_smul,←he]
    exact hg.trans he
  have hroot := fixes_first_mem_root m hm g hfirst
  obtain ⟨k,hk⟩ := suzukiRootSubgroup_isPGroup m hm ⟨g,hroot⟩
  have hd : orderOf g ∣ 2^k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (hodd.coprime_two_right.pow_right k) dvd_rfl hd)

/-- The same statement for any actual Sylow subgroup and its fixed vectors. -/
theorem odd_eq_one_of_fixes_sylow_fixed (m : ℕ) (hm : 0 < m)
    (P : Sylow 2 (SuzukiMatrixGroup m))
    (g : SuzukiMatrixGroup m) (hodd : Odd (orderOf g))
    (v : W m) (hv : v ≠ 0)
    (hP : ∀ u ∈ P, natural m u v = v)
    (hg : natural m g v = v) : g = 1 := by
  obtain ⟨U,hU⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) P U
  have hmap : (P : Subgroup (SuzukiMatrixGroup m)).map (MulAut.conj a).toMonoidHom =
      SuzukiRootSubgroup m := (congrArg Sylow.toSubgroup ha).trans hU
  have hfix (x : SuzukiMatrixGroup m) (hx : natural m x v = v) :
      natural m (MulAut.conj a x) (natural m a v) = natural m a v := by
    change natural m (a*x*a⁻¹) (natural m a v) = _
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
    rw [map_mul,Module.End.mul_apply,hx]
  have hz : natural m a v ≠ 0 := by
    intro he
    have hh := congrArg (natural m a⁻¹) he
    simp only [map_zero,←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply] at hh
    exact hv hh
  have he := odd_eq_one_of_fixes_root_fixed m hm (MulAut.conj a g)
    ((orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective g).symm ▸ hodd)
    (natural m a v) hz (by
      intro u hu
      rw [←hmap] at hu
      obtain ⟨x,hx,rfl⟩ := hu
      exact hfix x (hP x hx)) (hfix g hg)
  exact (MulAut.conj a).map_eq_one_iff.mp he
end Representation.SuzukiNatural

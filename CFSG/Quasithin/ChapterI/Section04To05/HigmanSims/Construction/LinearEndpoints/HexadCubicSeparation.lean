module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadPairOrders
public import Theory.SpecificGroups.MathieuAmalgamCompletion.CubicVariants

/-!
# Quotient separation for the selected exterior cubic

The original non-coset cubic and the canonical endpoint torus have distinct
images in the same full A₆ quotient.  Equality of two such images would put a
kernel element in the original cubic centralizer, where the paired-radical
source makes the kernel intersection trivial.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetWordCertificate
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]
local notation "A6" => alternatingGroup (Fin 6)

private theorem eval_hom {H α : Type*} [Group H]
    (f : H→*G) (p : α→H) (w : Word α) :
    f (eval p w)=eval (fun i => f (p i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    cases a with
    | mk a b => cases b <;> simp

theorem NaturalEndpointData.hexad_cubic_quotient_separation
    (d : NaturalEndpointData A)
    (hPD : d.carrier≤d.hexad_overgroup)
    (q : d.hexad_overgroup→*A6)
    (hqker : q.ker=A.subgroupOf d.hexad_overgroup)
    (pair : Fin 2→d.carrier)
    (t : d.carrier) (ht3 : orderOf t=3)
    (hline : zpowers (eval pair
      Matrix.PSL3Four.MathieuAmalgamMarking.torusWord)=zpowers t)
    (n : G) (hnD : n∈d.hexad_overgroup)
    (_hn3 : orderOf n=3) (hnt : Commute n (t:G))
    (hnT : n∉zpowers (t:G)) :
    q ⟨n,hnD⟩≠1 ∧
      q ⟨n,hnD⟩ ≠ q (eval (fun i => inclusion hPD (pair i))
        Matrix.PSL3Four.MathieuAmalgamMarking.torusWord) ∧
      q ⟨n,hnD⟩ ≠ q ((eval (fun i => inclusion hPD (pair i))
        Matrix.PSL3Four.MathieuAmalgamMarking.torusWord)^2) ∧
      Commute ⟨n,hnD⟩ (eval (fun i => inclusion hPD (pair i))
        Matrix.PSL3Four.MathieuAmalgamMarking.torusWord) := by
  let T0 : d.carrier := eval pair Matrix.PSL3Four.MathieuAmalgamMarking.torusWord
  let TD : d.hexad_overgroup := inclusion hPD T0
  have hTD : TD = eval (fun i => inclusion hPD (pair i))
      Matrix.PSL3Four.MathieuAmalgamMarking.torusWord := by
    dsimp [TD,T0]
    exact (eval_hom (inclusion hPD) pair
      Matrix.PSL3Four.MathieuAmalgamMarking.torusWord).symm
  have hTz : (T0:G)∈zpowers (t:G) := by
    have hzD : T0∈zpowers t := by
      rw [←hline]
      exact mem_zpowers _
    rcases mem_zpowers_iff.mp hzD with ⟨z,hz⟩
    apply mem_zpowers_iff.mpr
    refine ⟨z,?_⟩
    exact congrArg Subtype.val hz
  have hTcomm : Commute (T0:G) (t:G) := by
    rcases mem_zpowers_iff.mp hTz with ⟨z,hz⟩
    rw [←hz]
    exact (Commute.refl (t:G)).zpow_left z
  have hnTcomm : Commute n (T0:G) := by
    rcases mem_zpowers_iff.mp hTz with ⟨z,hz⟩
    rw [←hz]
    exact hnt.zpow_right z
  have hkill (x : d.hexad_overgroup) (hx : x∈q.ker)
      (hxc : Commute (x:G) (t:G)) : x=1 := by
    have hxA : (x:G)∈A := by
      have hh : x∈A.subgroupOf d.hexad_overgroup := hqker ▸ hx
      exact hh
    have hz : (x:G)∈(⊥:Subgroup G) :=
      d.cubic_radical_centralizer t t.property ((orderOf_coe t).trans ht3) ▸
        (show (x:G)∈A⊓centralizer ({(t:G)}:Set G) from
          ⟨hxA,mem_centralizer_singleton_iff.mpr hxc.eq⟩)
    exact Subtype.ext (mem_bot.mp hz)
  have hqne : q ⟨n,hnD⟩≠1 := by
    intro hq
    have hx : (⟨n,hnD⟩ : d.hexad_overgroup)∈q.ker := by
      rw [MonoidHom.mem_ker]
      exact hq
    have hxn := hkill _ hx hnt
    have hnz : (n:G)∈zpowers (t:G) := by
      have hn1 : n=1 := congrArg Subtype.val hxn
      rw [hn1]
      exact (zpowers (t:G)).one_mem
    exact hnT hnz
  have hqT : q ⟨n,hnD⟩ ≠ q TD := by
    intro hq
    let x : d.hexad_overgroup := ⟨n,hnD⟩*TD⁻¹
    have hx : x∈q.ker := by
      rw [MonoidHom.mem_ker]
      dsimp [x]
      rw [map_mul,map_inv,hq]
      simp
    have hxc : (x:G) = n*(T0:G)⁻¹ := by simp [x,TD]
    have hxn := hkill x hx (hxc ▸ hnt.mul_left hTcomm.inv_left)
    have hnz : (n:G)∈zpowers (t:G) := by
      have heq : (n:G)=(T0:G) := by
        have := congrArg (fun y : d.hexad_overgroup => (y:G)) hxn
        simpa [x,TD] using (mul_inv_eq_one.mp this)
      rw [heq]
      exact hTz
    exact hnT hnz
  have hqT2 : q ⟨n,hnD⟩ ≠ q (TD^2) := by
    intro hq
    let x : d.hexad_overgroup := ⟨n,hnD⟩*(TD^2)⁻¹
    have hx : x∈q.ker := by
      rw [MonoidHom.mem_ker]
      dsimp [x]
      rw [map_mul,map_inv,hq]
      simp
    have hxc : (x:G) = n*((T0:G)^2)⁻¹ := by
      simp [x,TD]
    have hxn := hkill x hx (hxc ▸ hnt.mul_left (hTcomm.pow_left 2).inv_left)
    have hnz : (n:G)∈zpowers (t:G) := by
      have heq : (n:G)=(T0:G)^2 := by
        have := congrArg (fun y : d.hexad_overgroup => (y:G)) hxn
        have hh : n*((T0:G)^2)⁻¹=1 := by simpa [x,TD] using this
        exact mul_inv_eq_one.mp hh
      rw [heq]
      exact (zpowers (t:G)).pow_mem hTz 2
    exact hnT hnz
  refine ⟨hqne,?_,?_,?_⟩
  · simpa only [hTD] using hqT
  · simpa only [hTD] using hqT2
  · change Commute (⟨n,hnD⟩ : d.hexad_overgroup) TD
    change (⟨n,hnD⟩ : d.hexad_overgroup) * TD = TD * ⟨n,hnD⟩
    apply Subtype.ext
    simpa [TD,T0] using hnTcomm.eq

end CFSG.Quasithin.HigmanSims

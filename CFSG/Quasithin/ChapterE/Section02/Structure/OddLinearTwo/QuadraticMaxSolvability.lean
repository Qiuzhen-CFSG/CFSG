module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.PrimeAutomizer
public import Theory.GroupTheory.SingleInvolutionClassSylow
public import Theory.GroupTheory.SolvableNormalSup
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.QuadraticSource
public import Theory.SpecificGroups.PSL2.InvolutionCentralizerSolvable
/-!
# Solvability of proper odd-index subgroups in a minimal parabolic

A proper odd-index subgroup has its Sylow subgroup conjugated into the
unique maximal overgroup. Thus a solvable maximal overgroup forces the
subgroup itself solvable. The quadratic source centralizer makes that
maximal overgroup solvable, while the fixed-field subgroup is not.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Structure
/-- Proper odd-index subgroups lying under the unique maximal are solvable. -/
theorem proper_odd_index_isSolvable_of_max_isSolvable
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hM : Group.IsSolvable (ChapterB.minimalParabolicMax T hP))
    (N : Subgroup H) (hN : N ≠ ⊤) (ho : Odd N.index) : Group.IsSolvable N := by
  let Q : Sylow 2 N := Classical.choice inferInstance
  let R : Subgroup H := (Q : Subgroup N).map N.subtype
  have hR : IsPGroup 2 R := Q.isPGroup'.map N.subtype
  have hi : ¬ 2 ∣ R.index := by
    rw [show R.index = (Q : Subgroup N).index * N.index from index_map_subtype _]
    exact Nat.prime_two.not_dvd_mul Q.not_dvd_index ho.not_two_dvd_nat
  let S : Sylow 2 H := hR.toSylow hi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S T
  let e := MulAut.conj g
  let N' := N.map e.toMonoidHom
  have hTN : (T : Subgroup H) ≤ N' := by
    rw [← hg]
    change R.map e.toMonoidHom ≤ N.map e.toMonoidHom
    exact map_mono (map_subtype_le _)
  have hN' : N' ≠ ⊤ := by
    intro he
    apply hN
    exact (map_injective e.injective) (he.trans (map_top_of_surjective e.toMonoidHom e.surjective).symm)
  have hNM : N' ≤ ChapterB.minimalParabolicMax T hP := hP.1.le_maximal
    ⟨(ChapterB.minimalParabolicMax_spec T hP).2,
      (ChapterB.minimalParabolicMax_spec T hP).1.covBy_top⟩ hTN (lt_top_iff_ne_top.mpr hN')
  let := hM
  let : Group.IsSolvable N' := Group.isSolvable_of_isSolvable_injective (f := inclusion hNM) (inclusion_injective _)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (N.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
    (N.equivMapOfInjective e.toMonoidHom e.injective).injective
/-- The quadratic source maximal overgroup is solvable. -/
theorem quadratic_linear_source_max_isSolvable
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (eK : K ≃* BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) :
    Group.IsSolvable (ChapterB.minimalParabolicMax T hP) := by
  obtain ⟨t, ht, _, _, _, hMK⟩ := quadratic_linear_source_centralizer T hP K hgen ho hF hp eK
  let M := ChapterB.minimalParabolicMax T hP
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) := ⟨p, 2, Fact.out, ho, by decide, hF⟩
  have ht' : GorensteinWalter.IsInvolution (eK t) :=
    ⟨fun he => ht.1 (eK.injective (by simpa using he)), by rw [← map_pow, ht.2, map_one]⟩
  let := Theory.PSL2.involution_centralizer_isSolvable hodd (eK t) ht'
  let f : centralizer ({t} : Set K) →* centralizer ({eK t} : Set _) := {
    toFun := fun y => ⟨eK y, by
      apply mem_centralizer_singleton_iff.mpr
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp y.property]⟩
    map_one' := Subtype.ext eK.map_one
    map_mul' := fun a b => Subtype.ext (eK.map_mul a b) }
  have hf : Function.Injective f := fun a b hh =>
    Subtype.ext (eK.injective (congrArg Subtype.val hh))
  have hsolv : Group.IsSolvable (M.subgroupOf K) := by
    rw [show M.subgroupOf K = centralizer ({t} : Set K) from hMK]
    exact Group.isSolvable_of_isSolvable_injective hf
  let := hsolv
  let g : M.subgroupOf K →* M := {
    toFun := fun x => ⟨x.val.val, x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let q : M →* H ⧸ K := (QuotientGroup.mk' K).comp M.subtype
  let : Group.IsNilpotent (H ⧸ K) := (isPGroup_quotient_of_sup_eq_top K
    (T : Subgroup H) T.isPGroup' hgen).isNilpotent
  apply Group.isSolvable_of_ker_le_range g q
  intro x hx
  have hk : (x : H) ∈ K := (QuotientGroup.eq_one_iff _).mp hx
  exact ⟨⟨⟨x, hk⟩, x.property⟩, rfl⟩

end CFSG.Quasithin.ChapterE.Structure

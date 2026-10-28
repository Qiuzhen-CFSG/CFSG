module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Singer

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Sections

/-!
# Full movement of a marked doubled-dual section

A Singer element has invertible displacement on each dual three-space.
Lifting its displacement through the literal marked quotient shows that a
subgroup containing the denominator and all ambient commutators contains
the entire section. The source center application places the second hat
layer in the original commutator core joined with Z.

Source: Meierfrankenfeld--Stellmacher (1993), the collection of (4.5.4)(iii)
and (4.5), printed pp.895,899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher
open DistanceFour.Linear
variable {M : Type*} [Group M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R} {common : CommonFacts R source geometry}

private theorem singer_displacement_surjective :
    Function.Surjective (fun v : W => dual Quotients.MovingLayer.Singer.singer v - v) := by
  let d : W →ₗ[ZMod 2] W := {
    toFun := fun v => dual Quotients.MovingLayer.Singer.singer v - v
    map_add' := by intro v w; simp only [dual,Matrix.mulVec_add]; abel
    map_smul' := by intro c v; simp [dual,Matrix.mulVec_smul,smul_sub] }
  have hinv : Quotients.MovingLayer.Singer.singer⁻¹ =
      (⟨!![1,1,0; 0,0,1; 1,0,0], by decide⟩ : S) := by
    apply inv_eq_of_mul_eq_one_right
    decide +kernel
  have hz : ∀ v : W, dual Quotients.MovingLayer.Singer.singer v - v = 0 → v = 0 := by
    simp only [dual,hinv]
    decide +kernel
  have hd : Function.Injective d := LinearMap.ker_eq_bot.mp (by
    apply le_antisymm ?_ bot_le
    intro v hv
    exact hz v hv)
  exact Finite.surjective_of_injective hd

/-- A doubled-dual marked section has no trivial quotient. -/
theorem MarkedPairSection.le_of_commutator_le
    {A N D : Subgroup (FreeAmalgam R)} (s : MarkedPairSection source common A N true)
    (hN : N ≤ D) (hcomm : ⁅A,Mbar R⁆ ≤ D) : A ≤ D := by
  intro x hx
  let x' : A := ⟨x,hx⟩
  obtain ⟨v₁,hv₁⟩ := singer_displacement_surjective (s.quotient x').toAdd.1
  obtain ⟨v₂,hv₂⟩ := singer_displacement_surjective (s.quotient x').toAdd.2
  obtain ⟨a,ha⟩ := s.onto (Multiplicative.ofAdd (v₁,v₂))
  obtain ⟨m,hm⟩ := source.projection_surjective
    (common.natural.marking.symm Quotients.MovingLayer.Singer.singer)
  have hmark : common.natural.marking (source.projection m) = Quotients.MovingLayer.Singer.singer := by simp [hm]
  let b : A := ⟨embedM R m * (a : FreeAmalgam R) * (embedM R m)⁻¹,
    le_normalizer_iff.mp s.normalized _ ⟨m,rfl⟩ _ a.property⟩
  have hbx : s.quotient (b*a⁻¹) = s.quotient x' := by
    apply Multiplicative.toAdd.injective
    rw [map_mul,map_inv]
    change ((s.quotient b).toAdd.1 + -(s.quotient a).toAdd.1,
      (s.quotient b).toAdd.2 + -(s.quotient a).toAdd.2) = (s.quotient x').toAdd
    rw [s.action m a b rfl,hmark,ha]
    simp only [ite_true,toAdd_ofAdd]
    exact Prod.ext (by simpa only [sub_eq_add_neg] using hv₁)
      (by simpa only [sub_eq_add_neg] using hv₂)
  have hba : ((b*a⁻¹ : A) : FreeAmalgam R) ∈ D := by
    change ⁅embedM R m,(a : FreeAmalgam R)⁆ ∈ D
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator ⟨m,rfl⟩ a.property)
  have hker : x' * (b*a⁻¹)⁻¹ ∈ s.quotient.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,hbx,mul_inv_cancel]
  rw [s.kernel] at hker
  have hxD := D.mul_mem (hN hker) hba
  change x * ((b*a⁻¹ : A) : FreeAmalgam R)⁻¹ * ((b*a⁻¹ : A) : FreeAmalgam R) ∈ D at hxD
  simpa only [inv_mul_cancel_right] using hxD

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher

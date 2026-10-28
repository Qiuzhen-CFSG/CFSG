module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoInvertingGenerator
/-!
# The moved quaternion orbit in the reduced Hall–Janko first core

The eight explicit radical elements form a subgroup containing every
commutator with the chosen cubic. Its six elements of order four are
exactly the cubic conjugates of the endpoint frame's q and its inverse.
All multiplication, inverse and commutator witnesses are checked on the
retained ATLAS degree-100 permutations.

This lets the original outer involution be adjusted to the same q without
changing either endpoint generator frame. Source: DGS (15.3), printed
pp.229–230. No order-twelve or original parabolic recognition is asserted.
-/

open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
open Seed PairNormalizer GeneratorPair GeneratorPair.SecondOrbitCertificate FirstParabolic
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.GeneratorRelations.Orbit
private def k : Carrier := oddGenerator 1
private def q : Carrier := radicalElement 12
private def movedIndex : Fin 8 → Fin 32 := ![0,15,12,10,13,9,28,30]
private def movedMul : Fin 8 → Fin 8 → Fin 8 := ![![0,1,2,3,4,5,6,7],![1,0,5,6,7,2,3,4],![2,5,1,7,3,0,4,6],![3,6,4,1,5,7,0,2],![4,7,6,2,1,3,5,0],![5,2,0,4,6,1,7,3],![6,3,7,0,2,4,1,5],![7,4,3,5,0,6,2,1]]
private def movedInv : Fin 8 → Fin 8 := ![0,1,5,6,7,2,3,4]
private def movedComm : Fin 32 → Fin 3 → Fin 8 := ![![0,0,0],![0,0,0],![0,2,7],![0,3,5],![0,0,0],![0,2,7],![0,3,5],![0,0,0],![0,2,7],![0,4,6],![0,2,7],![0,3,5],![0,4,6],![0,3,5],![0,0,0],![0,0,0],![0,2,7],![0,4,6],![0,2,7],![0,3,5],![0,4,6],![0,3,5],![0,0,0],![0,0,0],![0,2,7],![0,4,6],![0,3,5],![0,4,6],![0,2,7],![0,4,6],![0,3,5],![0,4,6]]
private theorem moved_mul_check : ∀ i j a,
    (RadicalStructureData.tablePerm (movedIndex i)*RadicalStructureData.tablePerm (movedIndex j)) a=
      RadicalStructureData.tablePerm (movedIndex (movedMul i j)) a := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply allFin <;> decide +kernel
private theorem moved_inv_check : ∀ i a,
    ((RadicalStructureData.tablePerm (movedIndex i))⁻¹) a=
      RadicalStructureData.tablePerm (movedIndex (movedInv i)) a := by
  intro i
  fin_cases i <;> apply allFin <;> decide +kernel
private theorem moved_comm_check : ∀ i n a,
    (RadicalStructureData.tablePerm i * (QuotientData.oddTable 1)^n.val *
      (RadicalStructureData.tablePerm i)⁻¹ * ((QuotientData.oddTable 1)^n.val)⁻¹) a=
      RadicalStructureData.tablePerm (movedIndex (movedComm i n)) a := by
  intro i n
  fin_cases i <;> fin_cases n <;> apply allFin <;> decide +kernel
private theorem moved_mul (i j : Fin 8) :
    radicalElement (movedIndex i)*radicalElement (movedIndex j)=
      radicalElement (movedIndex (movedMul i j)) := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,radicalElement_inclusion,radicalElement_inclusion,radicalElement_inclusion]
  exact Equiv.ext (moved_mul_check i j)
private theorem moved_inv (i : Fin 8) :
    (radicalElement (movedIndex i))⁻¹=radicalElement (movedIndex (movedInv i)) := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_inv,radicalElement_inclusion,radicalElement_inclusion]
  exact Equiv.ext (moved_inv_check i)
private theorem moved_comm (i : Fin 32) (n : Fin 3) :
    radicalElement i*k^n.val*(radicalElement i)⁻¹*(k^n.val)⁻¹=
      radicalElement (movedIndex (movedComm i n)) := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,map_mul,map_inv,map_inv,map_pow,k,
    oddGenerator_inclusion,radicalElement_inclusion,radicalElement_inclusion]
  exact Equiv.ext (moved_comm_check i n)
private def moved : Subgroup Carrier where
  carrier := Set.range (fun i => radicalElement (movedIndex i))
  one_mem' := ⟨0,rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    exact ⟨movedMul i j,(moved_mul i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i,rfl⟩
    exact ⟨movedInv i,(moved_inv i).symm⟩
private theorem commutator_le_moved : ⁅radical,zpowers k⁆≤moved := by
  apply commutator_le.mpr
  intro a ha b hb
  obtain ⟨i,rfl⟩ := exists_radicalElement ha
  have hk : orderOf k=3 := SecondParabolic.Overlap.v_order
  have hfin : IsOfFinOrder k := orderOf_pos_iff.mp (by rw [hk]; decide)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf,hk] at hb
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hb
  refine ⟨movedComm i ⟨n,Finset.mem_range.mp hn⟩,?_⟩
  exact (moved_comm i ⟨n,Finset.mem_range.mp hn⟩).symm

private theorem moved_orbit_check : ∀ i : Fin 6, ∀ a,
    RadicalStructureData.tablePerm (movedIndex ⟨i.val+2,by omega⟩) a =
      ((QuotientData.oddTable 1)^(i.val%3) *
        (if i.val<3 then RadicalStructureData.tablePerm 12 else (RadicalStructureData.tablePerm 12)⁻¹) *
        ((QuotientData.oddTable 1)^(i.val%3))⁻¹) a := by
  intro i
  fin_cases i <;> apply allFin <;> decide +kernel
private theorem moved_orbit (i : Fin 6) :
    radicalElement (movedIndex ⟨i.val+2,by omega⟩)=
      k^(i.val%3)*(if i.val<3 then q else q⁻¹)*(k^(i.val%3))⁻¹ := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_mul,map_mul,map_inv,map_pow,radicalElement_inclusion]
  have he : inclusion (if i.val<3 then q else q⁻¹)=
      if i.val<3 then RadicalStructureData.tablePerm 12 else (RadicalStructureData.tablePerm 12)⁻¹ := by
    split <;> simp only [q,map_inv,radicalElement_inclusion]
  rw [he,k,oddGenerator_inclusion]
  exact Equiv.ext (moved_orbit_check i)
private theorem moved_center_square : (radicalElement (movedIndex 1))^2=1 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_pow,radicalElement_inclusion,map_one]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- The six order-four elements of the actual moved quaternion group form
one cubic orbit together with its inverses. -/
public theorem quaternion_orbit (y : Carrier)
    (hy : y∈⁅radical,zpowers (oddGenerator 1)⁆) (ho : orderOf y=4) :
    ∃ n : Fin 3,
      y=(oddGenerator 1)^n.val*radicalElement 12*((oddGenerator 1)^n.val)⁻¹ ∨
      y=(oddGenerator 1)^n.val*(radicalElement 12)⁻¹*((oddGenerator 1)^n.val)⁻¹ := by
  obtain ⟨i,rfl⟩ := commutator_le_moved hy
  have hi0 : i≠0 := by
    intro he
    subst i
    change orderOf (1:Carrier)=4 at ho
    simp only [orderOf_one] at ho
    contradiction
  have hi1 : i≠1 := by
    intro he
    subst i
    have hd := orderOf_dvd_of_pow_eq_one moved_center_square
    rw [ho] at hd
    norm_num at hd
  fin_cases i
  · exact (hi0 rfl).elim
  · exact (hi1 rfl).elim
  · exact ⟨0,Or.inl (moved_orbit 0)⟩
  · exact ⟨1,Or.inl (moved_orbit 1)⟩
  · exact ⟨2,Or.inl (moved_orbit 2)⟩
  · exact ⟨0,Or.inr (moved_orbit 3)⟩
  · exact ⟨1,Or.inr (moved_orbit 4)⟩
  · exact ⟨2,Or.inr (moved_orbit 5)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.GeneratorRelations.Orbit

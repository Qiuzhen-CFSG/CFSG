module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.BIntersections
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.InvolutionClasses.Reduction

/-!
# Six original local classes and their intersections with B

The native representatives are transported through the fixed marking of M.
Every involution in M belongs to exactly one of these six M-classes. Their
intersections with the original B have sizes 1, 2, 4, 4, 4, and 0; the first
is {z}, and each nonempty intersection is an orbit under the original T.
The pointwise-centralizer equalities for source classes Δ4 and Δ5 retain
the actual ambient subgroup and action used by the growth argument.

Indices 0–5 correspond respectively to z, t, a single transposition,
two transpositions, a transposition/double-transposition pair, and the swap.

Source: Aschbacher–Smith 13.9.3–5, printed p.970.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
open SymmetricFourWreath.InvolutionClasses
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

/-- The literal M-conjugacy class of the ith marked representative. -/
def localInvolutionClass (i : Fin 6) : Set G :=
  {x | ∃g∈d.M,g*m.embedding (representative i)*g⁻¹=x}

theorem embedding_mem_localInvolutionClass (i : Fin 6) (x : W) :
    m.embedding x∈m.localInvolutionClass i ↔ IsConj (representative i) x := by
  constructor
  · rintro ⟨g,hg,he⟩
    obtain ⟨w,rfl⟩ := show g∈m.embedding.range by rwa [m.range_embedding]
    refine isConj_iff.mpr ⟨w,?_⟩
    apply m.embedding_injective
    simpa only [map_mul,map_inv] using he
  · intro hc
    obtain ⟨g,hg⟩ := isConj_iff.mp hc
    exact ⟨m.embedding g,(m.equiv.symm g).property,by simpa only [map_mul,map_inv] using congrArg m.embedding hg⟩

theorem local_involution_classes (x : G) (hx : x∈d.M) (ho : orderOf x=2) :
    ∃!i:Fin 6,x∈m.localInvolutionClass i := by
  obtain ⟨w,rfl⟩ := show x∈m.embedding.range by rwa [m.range_embedding]
  have hw : orderOf w=2 := (orderOf_injective m.embedding m.embedding_injective w).symm.trans ho
  refine ⟨classIndex w,(m.embedding_mem_localInvolutionClass _ _).mpr
    ((isConj_representative_iff _ _).mpr ⟨hw,rfl⟩),?_⟩
  intro i hi
  exact ((isConj_representative_iff i w).mp
    ((m.embedding_mem_localInvolutionClass i w).mp hi)).2.symm

theorem card_B_local_class (i : Fin 6) :
    Nat.card {x:m.B // (x:G)∈m.localInvolutionClass i}=orbitSize i := by
  let e : SymmetricFourWreath.B ≃* m.B := m.imageEquiv SymmetricFourWreath.B
  let f : {x:SymmetricFourWreath.B // IsConj (representative i) (x:W)} ≃
      {x:m.B // (x:G)∈m.localInvolutionClass i} :=
    e.toEquiv.subtypeEquiv (fun x=>(m.embedding_mem_localInvolutionClass i x).symm)
  rw [←Nat.card_congr f,card_B_class]

theorem B_local_class_zero : {x:G | x∈m.B ∧ x∈m.localInvolutionClass 0}={m.z} := by
  ext x
  constructor
  · rintro ⟨⟨a,ha,rfl⟩,hc⟩
    have h : a∈{x:W | x∈SymmetricFourWreath.B ∧ IsConj (representative 0) x} :=
      ⟨ha,(m.embedding_mem_localInvolutionClass 0 a).mp hc⟩
    rw [B_class_zero] at h
    exact congrArg m.embedding h
  · rintro rfl
    exact ⟨mem_map_of_mem m.embedding (representative_mem_B 0 (by decide)),
      (m.embedding_mem_localInvolutionClass 0 SymmetricFourWreath.z).mpr (IsConj.refl SymmetricFourWreath.z)⟩

theorem B_local_class_transitive (i : Fin 6) (x y : G)
    (hx : x∈m.B) (hy : y∈m.B)
    (hxc : x∈m.localInvolutionClass i) (hyc : y∈m.localInvolutionClass i) :
    ∃g∈(d.T:Subgroup G),g*x*g⁻¹=y := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  obtain ⟨g,hg,he⟩ := B_class_sylow_transitive i (⟨a,ha⟩:SymmetricFourWreath.B)
    ⟨b,hb⟩ ((m.embedding_mem_localInvolutionClass i a).mp hxc)
    ((m.embedding_mem_localInvolutionClass i b).mp hyc)
  refine ⟨m.embedding g,?_,?_⟩
  · rw [←m.image_standardSylow]
    exact mem_map_of_mem m.embedding hg
  · simpa only [map_mul,map_inv] using congrArg m.embedding he

theorem B_local_class_pointwise_centralizer (i : Fin 6) (hi : i=3 ∨ i=4) :
    (d.T:Subgroup G) ⊓ centralizer
      {x:G | x∈m.B ∧ x∈m.localInvolutionClass i}=m.B := by
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    rw [←m.image_standardSylow] at hx
    obtain ⟨a,ha,rfl⟩ := hx
    have hmem : a∈(standardSylow:Subgroup W) ⊓ centralizer
        {x:W | x∈SymmetricFourWreath.B ∧ IsConj (representative i) x} := by
      refine ⟨ha,?_⟩
      rintro b ⟨hb,hbi⟩
      apply m.embedding_injective
      have h := hc (m.embedding b)
        ⟨mem_map_of_mem m.embedding hb,(m.embedding_mem_localInvolutionClass i b).mpr hbi⟩
      simpa only [map_mul] using h
    rw [B_class_pointwise_centralizer i hi] at hmem
    exact mem_map_of_mem m.embedding hmem
  · intro x hx
    refine ⟨m.elementaryGroup_le_sylow false false hx,?_⟩
    intro y hy
    exact congrArg Subtype.val
      ((IsElementaryAbelian.toIsMulCommutative (p:=2) (G:=m.B)).is_comm.comm
        (⟨y,hy.1⟩:m.B) ⟨x,hx⟩)

end CFSG.Quasithin.Chapter13.Section09.Marking

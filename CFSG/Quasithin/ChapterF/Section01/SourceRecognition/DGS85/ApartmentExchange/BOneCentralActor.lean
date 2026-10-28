module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCentralReflection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneNatural
public import Theory.SpecificGroups.SL2.OddBorelMarking

/-!
# Reflections from the actual neighbor center with a central actor kernel

The Chapter 10 natural-coordinate quotient has the full actor center as
kernel, and need not be injective. These coordinates give a central natural
kernel on the unchanged actor quotient. Relative normality of the neighbor
center places the edge stabilizer in its Sylow normalizer. Simultaneous odd
Borel coordinates then construct diagonal Cartan and upper-neighbor markings.

Every neighbor-center element outside the vertex core is an involution. The
central natural-kernel calculation produces a conjugate reflection fixing
the first vertex and moving the neighbor. Its Cartan normalization is inside
the actor. The larger Cartan's factors outside that actor, path-root selection,
exchange and quotient root signs remain genuine source obligations. No
trivial-center or nonbinary-field hypothesis is used here.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.155--157, and the
reflection argument (14.2), pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
open Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph
open CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace BOneActor
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F W : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {v w : Vertex (family P)} (h : LocallyRankOneTriple P B)
  (c : BOneActionData (family P) v w F W)
local instance centralAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

include h in
/-- Relative neighbor-center normality controls the actual edge image. -/
theorem neighbor_stabilizer_image (k : c.actor)
    (hk : (k:G)∈stabilizer (family P) w) :
    c.quotient k∈normalizer (c.imageSylow : Set SL(2,F)) := by
  let := finite_endpoints h
  have hZQ : Z (family P) w ≤ Q (family P) w := by
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h w).1 hz)).1
  have hn : (k:G)∈normalizer (Z (family P) w : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp (Z_normal _ _) hk
  have hn' : k∈normalizer ((Z (family P) w).subgroupOf c.actor : Set c.actor) := by
    rw [←subgroupOf_normalizer_eq (hZQ.trans c.neighbor_core_le)]
    exact hn
  change c.quotient k∈normalizer ((c.imageSylow : Subgroup SL(2,F)) : Set SL(2,F))
  rw [←c.neighbor_image]
  exact le_normalizer_map c.quotient (mem_map_of_mem c.quotient hn')

include h in
/-- Choose one inner quotient marking making the odd actor Cartan diagonal
and the neighbor Sylow upper triangular. -/
theorem exists_cartan_neighbor_marking (K : Subgroup c.actor)
    (hK : ∀ k∈K, (k:G)∈stabilizer (family P) w)
    (hodd : Nat.Coprime 2 (Nat.card K)) :
    ∃ a : SL(2,F),
      (c.imageSylow : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom =
        Matrix.SpecialLinearGroup.upperUnipotent F ∧
      (∀ k∈K, ∃ b : F, ∃ hb : b≠0,
        a*c.quotient k*a⁻¹=Matrix.SpecialLinearGroup.diag2 b hb) ∧
      (∀ k : c.actor, (k:G)∈stabilizer (family P) w →
        (a*c.quotient k*a⁻¹).val 1 0=0) := by
  have hn : K.map c.quotient≤normalizer (c.imageSylow : Set SL(2,F)) := by
    rintro y ⟨k,hk,rfl⟩
    exact neighbor_stabilizer_image h c k (hK k hk)
  have ho : Odd (Nat.card (K.map c.quotient)) :=
    Nat.coprime_two_left.mp (hodd.of_dvd_right (K.card_map_dvd c.quotient))
  obtain ⟨a,d,ha,hd⟩ := Matrix.SpecialLinearGroup.sylow_odd_subgroup_diagonal_coordinates
    c.imageSylow (K.map c.quotient) hn ho
  refine ⟨a,ha,?_,?_⟩
  · intro k hk
    let z : K.map c.quotient := ⟨c.quotient k,mem_map_of_mem c.quotient hk⟩
    exact ⟨d z,(d z).ne_zero,hd z⟩
  · intro k hk
    apply (Matrix.SpecialLinearGroup.mem_rankOneBorel_iff _).mp
    have ht := le_normalizer_map (MulAut.conj a).toMonoidHom
      (mem_map_of_mem (MulAut.conj a).toMonoidHom (neighbor_stabilizer_image h c k hk))
    rw [ha] at ht
    exact ht

/-- The source natural coordinates on the original actor kernel retain its
full central denominator. -/
def naturalCentralKernel (hcore : Q (family P) v=Z (family P) v)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F)) : NaturalCentralKernel c.quotient := Classical.choice (by
  obtain ⟨φ,honto,hker,hact⟩ := natural_core_coordinates c h hcore E
  let e : c.quotient.ker ≃* Q (family P) v :=
    (MulEquiv.subgroupCongr c.kernel).trans (subgroupOfEquivOfLe c.core_le)
  refine ⟨{ coordinates := φ.comp e.toMonoidHom
            onto := honto.comp e.surjective
            central := ?_
            isTwo := (isPGroup_pCoreIn 2 (stabilizer (family P) v)).of_equiv e.symm
            equivariant := ?_ }⟩
  · intro z hz
    have hc : (e z:G)∈centerIn c.actor := by
      have he : e z∈φ.ker := hz
      rwa [hker] at he
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact hc.2 y y.property
  · intro g z
    obtain ⟨y,hy,he⟩ := hact g (e z)
    have hconj : e ⟨g*z*g⁻¹,(inferInstance : c.quotient.ker.Normal).conj_mem z z.property g⟩=y := by
      apply Subtype.ext
      exact hy.symm
    change φ (e ⟨g*z*g⁻¹,_⟩)=Matrix.SL2.naturalAction F (c.quotient g) (φ (e z))
    rw [hconj]
    exact Multiplicative.toAdd.injective he)

include h in
/-- Construct the actor reflection from a genuine neighbor-center element
escaping the vertex core, with all matrix markings derived internally. -/
theorem exists_neighbor_center_reflection
    (hcore : Q (family P) v=Z (family P) v)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (K : Subgroup c.actor) [Group.IsSolvable K]
    (hK : ∀ k∈K, (k:G)∈stabilizer (family P) w)
    (hodd : Nat.Coprime 2 (Nat.card K))
    (x : c.actor) (hxZ : (x:G)∈Z (family P) w) (hxQ : (x:G)∉Q (family P) v) :
    ∃ t : c.actor, (t:G) • v=v ∧ (t:G) • w≠w ∧
      t∈normalizer (K : Set c.actor) ∧ t*t=1 ∧ orderOf t=2 ∧
      ∃ g : c.actor, g*x*g⁻¹=t := by
  let := finite_endpoints h
  let : Finite c.actor := Finite.of_injective (inclusion c.actor_le) (inclusion_injective _)
  obtain ⟨a,ha,hdiag,htri⟩ := exists_cartan_neighbor_marking h c K hK hodd
  let π := (MulAut.conj a).toMonoidHom.comp c.quotient
  have honto : Function.Surjective π := (MulAut.conj a).surjective.comp c.onto
  let d := (naturalCentralKernel h c hcore E).conj a
  have hxS : c.quotient x∈(c.imageSylow : Subgroup SL(2,F)) := by
    rw [←c.neighbor_image]
    exact mem_map_of_mem c.quotient hxZ
  have hxU : π x∈Matrix.SpecialLinearGroup.upperUnipotent F :=
    ha ▸ mem_map_of_mem (MulAut.conj a).toMonoidHom hxS
  obtain ⟨b,hb⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F (π x)).mp hxU
  have hxne : π x≠1 := by
    intro he
    have heq : c.quotient x=1 := (MulAut.conj a).injective (he.trans (map_one _).symm)
    have hxker : x∈c.quotient.ker := heq
    rw [c.kernel] at hxker
    exact hxQ hxker
  have hb0 : b≠0 := by
    intro he
    apply hxne
    rw [←hb,he,Matrix.SpecialLinearGroup.transvection_coeff_zero]
  have hπx : π x=upper b := hb.symm
  have hxsq : x*x=1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul,Subgroup.coe_one,pow_two] using
      ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h w).1 hxZ)).2.2
  obtain ⟨t,ht,hsq,ho,hπt,hconj⟩ := d.exists_diagonal_cartan_reflection honto K hodd
    hdiag x hxsq b hb0 hπx
  refine ⟨t,c.actor_le t.property,?_,ht,hsq,ho,hconj⟩
  intro hfix
  have he := htri t hfix
  change (π t).val 1 0=0 at he
  rw [hπt,braid_matrix b hb0] at he
  exact inv_ne_zero hb0 he

end BOneActor
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

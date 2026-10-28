module
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerModelPair
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.Pair
public import GorensteinWalter.PGL2LowTorus
public import GorensteinWalter.ReflectedCyclicIndexTwoSubgroup
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# A fixed equivalence between the two canonical J3 pair groups

The low-two-part torus in PGL₂(9) has order ten. Its torus involution is
outside the derived subgroup and centralizes an inner reflected subgroup
isomorphic to D₁₀. In the cubic normalizer model the outer involution inverts
C₃, producing an S₃ factor which commutes with that D₁₀. The resulting
order-sixty subgroup contains the cubic kernel, so the proved pair-conjugacy
theorem carries it to the canonical pair.

The only finite checks construct the six-element inversion semidirect
product and its D₃ coordinates. The final marking depends only on the two
fixed models, with no input from an arbitrary source group.
-/

noncomputable section
open Subgroup
open scoped Classical
namespace Sporadic.Janko3.SourceRecognition.CubicModelPairEquiv
open CubicNormalizerModel

private abbrev Two := Multiplicative (ZMod 2)

private def twoAction : Two →* MulAut Z where
  toFun a := if a = 1 then 1 else inversion
  map_one' := by simp
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    revert a b
    decide +kernel

private abbrev Six := Z ⋊[twoAction] Two
private instance : Fintype Six := Fintype.ofEquiv (Z × Two) SemidirectProduct.equivProd.symm

private def sixToDihedral (x : Six) : DihedralGroup 3 :=
  if x.right = 1 then DihedralGroup.r x.left.toAdd else DihedralGroup.sr (-x.left.toAdd)

private def sixHom : Six →* DihedralGroup 3 where
  toFun := sixToDihedral
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private def sixEquiv : Six ≃* DihedralGroup 3 :=
  MulEquiv.ofBijective sixHom (by decide +kernel)

private theorem two_cases (a : Two) : a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  revert a
  decide +kernel

private def twoHom (s : P) (hs : s * s = 1) : Two →* P where
  toFun a := if a = 1 then 1 else s
  map_one' := by simp
  map_mul' a b := by
    have htwo : (Multiplicative.ofAdd 1 : Two) * Multiplicative.ofAdd 1 = 1 := by decide
    rcases two_cases a with rfl | rfl <;> rcases two_cases b with rfl | rfl <;>
      simp_all

private theorem twoHom_injective (s : P) (hs : s * s = 1) (hn : s ≠ 1) :
    Function.Injective (twoHom s hs) := by
  intro a b he
  rcases two_cases a with rfl | rfl <;> rcases two_cases b with rfl | rfl <;>
    simp_all [twoHom]

private def sixLift (s : P) (hs : s * s = 1) (hout : s ∉ derived) : Six →* Model :=
  SemidirectProduct.map (MonoidHom.id Z) (twoHom s hs) (by
    intro a
    apply MonoidHom.ext
    intro z
    rcases two_cases a with rfl | rfl <;>
      simp [twoHom, twoAction, action_apply, hout])

private theorem sixLift_injective (s : P) (hs : s * s = 1) (hout : s ∉ derived) :
    Function.Injective (sixLift s hs hout) := by
  have hn : s ≠ 1 := by intro he; exact hout (he ▸ derived.one_mem)
  intro x y he
  apply SemidirectProduct.ext
  · exact congrArg (fun z : Model => z.left) he
  · exact twoHom_injective s hs hn (congrArg (fun z : Model => z.right) he)

private theorem exists_torus_data :
    ∃ (s : P) (D : Subgroup P), s * s = 1 ∧ s ∉ derived ∧ D ≤ derived ∧
      Nonempty (D ≃* DihedralGroup 5) ∧
      ∀ d : D, Commute s (d : P) := by
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card Atlas.Comparisons.Exceptional.Nine.F) := by
    rw [Atlas.Comparisons.Exceptional.Nine.card]
    exact ⟨3, 2, by decide, by decide, by decide, by decide⟩
  obtain ⟨U,s,t,w,hcyc,hhalf,hcard,hsU,hsout,_hsne,hssq,htin,htout,htsq,htinv,
    _htw,_hwout,_hwsq,_hwinv,_hcent⟩ :=
    GorensteinWalter.pgl2_low_two_part_torus_reflection_data
      Atlas.Comparisons.Exceptional.Nine.F hodd
        (by rw [Atlas.Comparisons.Exceptional.Nine.card]; decide)
  have hUc : Nat.card U = 10 := by
    rw [Atlas.Comparisons.Exceptional.Nine.card] at hcard
    rcases hcard with hcard | hcard
    · rw [hcard] at hhalf
      norm_num at hhalf
    · exact hcard
  obtain ⟨D,hD,hDJ,_hidx,_hDc,eD⟩ :=
    GorensteinWalter.exists_dihedral_subgroup_le_index_two_of_reflected_cyclic
      derived U derived_index hcyc 5 (by simpa using hUc)
        (fun h => hsout (h hsU)) t htin htout htsq htinv
  have hDU : U ≤ centralizer ({s} : Set P) := by
    let : IsCyclic U := hcyc
    let : CommGroup U := IsCyclic.commGroup
    intro u hu
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm (⟨u,hu⟩ : U) ⟨s,hsU⟩)
  have htcomm : t ∈ centralizer ({s} : Set P) := by
    rw [mem_centralizer_singleton_iff]
    have hi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hssq
    have hh := htinv s hsU
    rw [hi] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hDc : D ≤ centralizer ({s} : Set P) := by
    rw [hD]
    exact sup_le (inf_le_left.trans hDU) (zpowers_le.mpr htcomm)
  exact ⟨s,D,hssq,hsout,hDJ,eD,fun d =>
    ((mem_centralizer_singleton_iff.mp (hDc d.property)) : (d:P)*s=s*d).symm⟩

/-- The canonical cubic pair has fixed odd-dihedral product coordinates. -/
public theorem nonempty_pair_dihedral : Nonempty (pair ≃* DihedralGroup 3 × DihedralGroup 5) := by
  obtain ⟨s,D,hssq,hout,hDJ,⟨eD⟩,hcomm⟩ := exists_torus_data
  let a : Six →* Model := sixLift s hssq hout
  let b : D →* Model := (SemidirectProduct.inr : P →* Model).comp D.subtype
  have hc (x : Six) (d : D) : Commute (a x) (b d) := by
    change a x * b d = b d * a x
    apply SemidirectProduct.ext
    · change x.left * action (twoHom s hssq x.right) 1 = 1 * action (d : P) x.left
      rw [map_one, action_apply, if_pos (hDJ d.property)]
      simp
    · change twoHom s hssq x.right * (d : P) = (d : P) * twoHom s hssq x.right
      rcases two_cases x.right with hx | hx
      · rw [hx]
        simp [twoHom]
      · rw [hx]
        simpa [twoHom] using (hcomm d).eq
  have hdis : Disjoint a.range b.range := by
    apply disjoint_def.mpr
    rintro x ⟨y,rfl⟩ ⟨d,hd⟩
    have hr : (d : P) = twoHom s hssq y.right := congrArg (fun z : Model => z.right) hd
    have hy : y.right = 1 := by
      rcases two_cases y.right with hy | hy
      · exact hy
      · have hds : (d : P) = s := by simpa [twoHom,hy] using hr
        exact False.elim (hout (hds ▸ hDJ d.property))
    have hl : 1 = y.left := congrArg (fun z : Model => z.left) hd
    apply SemidirectProduct.ext
    · exact hl.symm
    · change twoHom s hssq y.right = 1
      rw [hy,map_one]
  let f : Six × D →* Model := a.noncommCoprod b hc
  have hf : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective a b hc).mpr
      ⟨sixLift_injective s hssq hout,
        SemidirectProduct.inr_injective.comp D.subtype_injective,hdis⟩
  have hcard : Nat.card f.range = 60 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,Nat.card_prod,
      Nat.card_congr sixEquiv.toEquiv,Nat.card_congr eD.toEquiv]
    rw [DihedralGroup.nat_card,DihedralGroup.nat_card]
  have hk : projection.ker ≤ f.range := by
    rw [projection_ker]
    rintro _ ⟨z,rfl⟩
    refine ⟨(SemidirectProduct.inl z,1),?_⟩
    change sixLift s hssq hout (SemidirectProduct.inl z) * b 1 = SemidirectProduct.inl z
    rw [map_one,mul_one]
    exact SemidirectProduct.map_inl _ _ _ _
  obtain ⟨g,hg⟩ := exists_conjugating_pair f.range hk hcard
  let ep : f.range ≃* pair :=
    (equivMapOfInjective f.range (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hg)
  exact ⟨((MonoidHom.ofInjective hf).trans ep).symm.trans
    (MulEquiv.prodCongr sixEquiv eD)⟩

/-- A chosen marking of the canonical cubic pair by D₃ × D₅. -/
public def dihedralEquiv : pair ≃* DihedralGroup 3 × DihedralGroup 5 := nonempty_pair_dihedral.some

/-- The pair comparison constructed from the two fixed models. -/
public def pairEquiv : Seventeen.ModelAmalgam.pair ≃* CubicNormalizerModel.pair :=
  (Seventeen.ModelAmalgam.pairEquiv.trans
    (MulEquiv.prodCongr Seventeen.ModelAmalgam.CyclicCoordinates.trianglePermEquiv.symm
      (MulEquiv.refl (DihedralGroup 5)))).trans dihedralEquiv.symm

public theorem nonempty_pairEquiv : Nonempty (Seventeen.ModelAmalgam.pair ≃* CubicNormalizerModel.pair) :=
  ⟨pairEquiv⟩

end Sporadic.Janko3.SourceRecognition.CubicModelPairEquiv

namespace Sporadic.Janko3.SourceRecognition.CubicNormalizerModel

/-- The fixed pair marking used in the simultaneous source recognition. -/
public noncomputable def modelPairEquiv : Seventeen.ModelAmalgam.pair ≃* pair :=
  CubicModelPairEquiv.pairEquiv

end Sporadic.Janko3.SourceRecognition.CubicNormalizerModel

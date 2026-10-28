module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicOverlapSource
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.TrianglePairCoreIntersection
public import Theory.GroupTheory.OddCentralInvolutionLifting
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner

/-!
# Actual returning core involutions inside the cubic normalizer

The marked cubic fixes a dihedral eight in the full involution core. A
noncentral involution in that eight is conjugate to the original field
involution inside the full cubic centralizer: its A₆ quotient has one
involution class, and the odd central kernel makes involutory lifts unique.
This supplies internal fusion for the original rank-three join.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

private theorem model_two_involutions :
    ∃ a b : MinusExtraspecial.Model, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b := by
  have h : ∃ a b : MinusExtraspecial.Model, a^2=1 ∧ a≠1 ∧ b^2=1 ∧ b≠1 ∧ a≠b := by
    decide +kernel
  obtain ⟨a,b,ha,ha1,hb,hb1,hab⟩ := h
  exact ⟨a,b,orderOf_eq_prime ha ha1,orderOf_eq_prime hb hb1,hab⟩

/-- The actual local H-type holds at every original involution. -/
theorem literal_involution_localType
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (hc : Janko23.OneInvolutionClass G) (f : G) (hf : orderOf f = 2) :
    Janko23.HTypeAt f := by
  obtain ⟨⟨eQ⟩,_,hA⟩ := literal_involution_core_and_quotient (D := D) hc f hf
  refine ⟨hf,⟨eQ⟩,hA,?_⟩
  intro hclosed
  let j : MinusExtraspecial.Model →* G := (Janko23.involutionCentralizer f).subtype.comp
    ((Janko23.localCore f).subtype.comp eQ.symm.toMonoidHom)
  have hj : Function.Injective j := Subtype.val_injective.comp
    (Subtype.val_injective.comp eQ.symm.injective)
  have he (x : MinusExtraspecial.Model) (hx : orderOf x = 2) : j x = f :=
    hclosed (j x) (mem_map_of_mem _ (eQ.symm x).property)
      (hc.isConj ((orderOf_injective j hj _).trans hx) hf)
  obtain ⟨a,b,ha,hb,hab⟩ := model_two_involutions
  exact hab (hj ((he a ha).trans (he b hb).symm))

private theorem odd_central_a6_involutions
    {H : Type*} [Group H] (q : H →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) (hodd : Odd (Nat.card q.ker))
    (hcent : q.ker ≤ center H) (x y : H) (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj x y := by
  have ho (w : H) (hw : orderOf w = 2) : orderOf (q w) = 2 := by
    apply orderOf_eq_prime
    · rw [←map_pow,show w^2=1 from hw ▸ pow_orderOf_eq_one w,map_one]
    · intro hh
      have he := OddCentralLifting.kernel_involution_eq_one q hodd hh
        (hw ▸ pow_orderOf_eq_one w)
      simp [he] at hw
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj (q x) (q y) (ho x hx) (ho y hy))
  obtain ⟨c,rfl⟩ := hq g
  refine isConj_iff.mpr ⟨c,?_⟩
  apply OddCentralLifting.involution_lift_unique q hodd hcent
  · change (MulAut.conj c x)^2=1
    rw [←map_pow,show x^2=1 from hx ▸ pow_orderOf_eq_one x,map_one]
  · exact hy ▸ pow_orderOf_eq_one y
  · simpa only [map_mul,map_inv] using hg

private theorem dihedral_two_involutions :
    ∃ a b : DihedralGroup 4, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b := by
  have h : ∃ a b : DihedralGroup 4, a^2=1 ∧ a≠1 ∧ b^2=1 ∧ b≠1 ∧ a≠b := by
    decide +kernel
  obtain ⟨a,b,ha,ha1,hb,hb1,hab⟩ := h
  exact ⟨a,b,orderOf_eq_prime ha ha1,orderOf_eq_prime hb hb1,hab⟩

/-- The actual cubic centralizer fuses the field involution to a different
involution in its full ambient two-core. -/
theorem literal_field_core_returning
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    ∃ u ∈ Janko23.ambientCore (j SingerField.fieldElement), orderOf u = 2 ∧
      u ≠ j SingerField.fieldElement ∧
      ∃ r ∈ centralizer ({j cubic} : Set G),
        r * j SingerField.fieldElement * r⁻¹ = u := by
  let f := j SingerField.fieldElement
  let s := j cubic
  have hf : orderOf f = 2 := image_involution_order j hj.1
  have hs : orderOf s = 3 := (orderOf_injective j hj.1 _).trans cubic_order
  have hsf : Commute s f :=
    (cubic_commutes_complement ⟨SingerField.fieldElement,(mem_pointComplement _).mpr rfl⟩).map j
  have hlocal := literal_involution_localType (D := D) hc f hf
  let H := Janko23.involutionCentralizer f
  let sH : H := ⟨s,mem_centralizer_singleton_iff.mpr hsf.eq⟩
  let I := Janko23.localCore f ⊓ centralizer ({sH} : Set H)
  obtain ⟨eI⟩ := cubic_core_fixed hlocal sH ((orderOf_coe _).symm.trans hs)
  let k : DihedralGroup 4 →* G := H.subtype.comp (I.subtype.comp eI.symm.toMonoidHom)
  have hk : Function.Injective k := Subtype.val_injective.comp
    (Subtype.val_injective.comp eI.symm.injective)
  have htwo : ∃ u : DihedralGroup 4, orderOf u = 2 ∧ k u ≠ f := by
    obtain ⟨b,c,hb,hc,hbc⟩ := dihedral_two_involutions
    by_cases he : k b = f
    · exact ⟨c,hc,fun hh => hbc (hk (he.trans hh.symm))⟩
    · exact ⟨b,hb,he⟩
  obtain ⟨u,hu,huf⟩ := htwo
  have huQ : k u ∈ Janko23.ambientCore f :=
    mem_map_of_mem H.subtype (eI.symm u).property.1
  have huorder : orderOf (k u) = 2 := (orderOf_injective k hk _).trans hu
  have huZ : k u ∈ centralizer ({s} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp (eI.symm u).property.2)
  let Z := centralizer ({s} : Set G)
  let x : Z := ⟨f,mem_centralizer_singleton_iff.mpr hsf.eq.symm⟩
  let y : Z := ⟨k u,huZ⟩
  obtain ⟨⟨eA⟩,_⟩ := literal_field_cubic_projective P hc A C a j hj
  let q : Z →* alternatingGroup (Fin 6) := eA.toMonoidHom.comp (QuotientGroup.mk' (cubicKernel s))
  have hker : q.ker = cubicKernel s := by
    rw [MonoidHom.ker_comp_of_injective _ _ eA.injective,QuotientGroup.ker_mk']
  have hconj := odd_central_a6_involutions q
    (eA.surjective.comp (QuotientGroup.mk'_surjective _))
    (by rw [hker,cubicKernel_card s hs]; decide) (hker ▸ cubicKernel_central s)
    x y ((orderOf_coe _).symm.trans hf) ((orderOf_coe _).symm.trans huorder)
  obtain ⟨r,hr⟩ := isConj_iff.mp hconj
  exact ⟨k u,huQ,huorder,huf,r,r.property,congrArg Subtype.val hr⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient

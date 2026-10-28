module

public import Theory.Representation.G2BinaryIsotropicThree.OffenderSpaces
public import Theory.Representation.G2BinaryIsotropicThree.PointParabolic


/-!
# The intrinsic hyperplanes in a binary unitary offender pair

An isometry fixing the marked isotropic three-space pointwise has all its
displacements in that space. It therefore centralizes C(1), and the actual
root-centralizer calculation identifies the pointwise stabilizer with ABC.
The literal ABC action induces the displayed bilinear commutator pairing on
the three quotient coordinates. Its two singular loci are hyperplanes, and
their mutual commutators span the first point. The only finite checks concern
the two eight-element binary parameter spaces.

Source: Aschbacher–Smith 13.3.12(4), printed p.890, the intrinsic descriptions
of U₅ and V₅ and the identity V₁=[U₅,V₅].
-/

@[expose] public section

open Subgroup Module Submodule Representation Representation.BinaryOffender
namespace Atlas.G2.Natural.BinaryIsotropicThree
open BinaryNondegeneratePlane Atlas.G2.Restricted.NaturalCoordinates

theorem displacement_mem_target_of_fixed_target (g : Model K)
    (hg : ∀v∈target false,rho g v=v) (v : W) : rho g v-v∈target false := by
  have hh (w : W) (hw : w∈target false) : form (rho g v-v) w=0 := by
    have hi := form_invariant g v w
    rw [hg w hw] at hi
    rw [map_sub,LinearMap.sub_apply,hi,sub_self]
  have h0 := hh ![1,0,0,0,0,0] (by simp [target,Certificate.inTarget])
  have h1 := hh ![0,1,0,0,0,0] (by simp [target,Certificate.inTarget])
  have h2 := hh ![0,0,1,0,0,0] (by simp [target,Certificate.inTarget])
  change (rho g v-v) 3=0 ∧ (rho g v-v) 4=0 ∧ (rho g v-v) 5=0
  simp [form_apply] at h0 h1 h2
  exact ⟨h2,h1,h0⟩

theorem pointwise_target_eq_elementary (g : Model K) :
    (∀v∈target false,rho g v=v) ↔ g∈EvenTwoRank.elementary K := by
  constructor
  · intro hg
    apply NaturalOffenders.mem_elementary_of_centralizes_of_fix_upper (1:K) one_ne_zero _ hg
    apply rho_injective
    apply LinearMap.ext
    intro v
    have hC (w : W) (hw : w∈target false) : rho (rootC (1:K)) w=w :=
      NaturalOffenders.rootC_fix_upper 1 hw
    have h1 := hg (rho (rootC (1:K)) v-v)
      (rootC_displacement_range ▸ (show rho (rootC (1:K)) v-v∈LinearMap.range (rho (rootC (1:K))-1) from ⟨v,rfl⟩))
    have h2 := hC (rho g v-v) (displacement_mem_target_of_fixed_target g hg v)
    simp only [map_sub,sub_eq_iff_eq_add] at h1 h2
    simp only [map_mul,Module.End.mul_apply]
    rw [h1,h2]
    abel
  · intro hg v hv
    exact NaturalOffenders.elementary_fix_upper hg hv

def pairCommutator (q v : Three) : Three :=
  ![q 0*v 1+q 1*v 0+q 2*v 2,q 0*v 2+q 2*v 0,q 1*v 2+q 2*v 1]

def tailCoordinate (v : W) : Three := ![v 3,v 4,v 5]

theorem elementary_displacement (q : Three) (v : W) :
    rho (EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd q)) v-v=
      targetEmbed false (pairCommutator q (tailCoordinate v)) := by
  have hq : q 2^2=q 2 := by exact ZMod.pow_card _
  have he : EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd q)=
      rootA (q 0)*(rootB (q 1)*rootC (q 2)) := by
    simp [EvenTwoRank.elementaryEmbedding,EvenTwoRank.elementaryParameters,unipotentProduct,mul_assoc]
  rw [he]
  simp only [map_mul,Module.End.mul_apply]
  ext i
  fin_cases i <;> simp [pairCommutator,tailCoordinate,targetEmbed,action_rootA,action_rootB,action_rootC,hq]
  all_goals ring

theorem pairCommutator_actor_kernel (q : Three) :
    (∃v : Three,v≠0 ∧ pairCommutator q v=0) ↔ q 2=0 := by
  exact (show ∀q : Three,(∃v : Three,v≠0 ∧ pairCommutator q v=0) ↔ q 2=0 by decide +kernel) q

theorem pairCommutator_vector_kernel (v : Three) :
    (∃q : Three,q≠0 ∧ pairCommutator q v=0) ↔ v 2=0 := by
  exact (show ∀v : Three,(∃q : Three,q≠0 ∧ pairCommutator q v=0) ↔ v 2=0 by decide +kernel) v

theorem pairCommutator_hyperplanes (q v : Three) (hq : q 2=0) (hv : v 2=0) :
    pairCommutator q v=![q 0*v 1+q 1*v 0,0,0] := by
  simp [pairCommutator,hq,hv]

theorem pairCommutator_point : pairCommutator ![1,0,0] ![0,1,0]=![1,0,0] := by
  decide +kernel
theorem elementary_fixed_outside_target (q : Three) :
    (∃v : W,v∉target false ∧
      rho (EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd q)) v=v) ↔ q 2=0 := by
  rw [←pairCommutator_actor_kernel]
  have htail (v : W) : tailCoordinate v=0 ↔ v∈target false := by
    change ![v 3,v 4,v 5]=0 ↔ v 3=0 ∧ v 4=0 ∧ v 5=0
    simp
  have hfix (v : W) :
      rho (EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd q)) v=v ↔
        pairCommutator q (tailCoordinate v)=0 := by
    rw [←sub_eq_zero,elementary_displacement]
    rw [←map_zero (targetEmbed false)]
    constructor
    · intro hh
      exact (targetEquiv false).injective (Subtype.ext hh)
    · exact congrArg (targetEmbed false)
  constructor
  · rintro ⟨v,hv,hg⟩
    exact ⟨tailCoordinate v,fun hh=>hv ((htail v).mp hh),(hfix v).mp hg⟩
  · rintro ⟨v,hv,hg⟩
    have ht : tailCoordinate ![0,0,0,v 0,v 1,v 2]=v := by
      ext i
      fin_cases i <;> rfl
    refine ⟨![0,0,0,v 0,v 1,v 2],?_,?_⟩
    · intro hh
      apply hv
      exact ht ▸ (htail _).mpr hh
    · apply (hfix _).mpr
      rwa [ht]
end Atlas.G2.Natural.BinaryIsotropicThree

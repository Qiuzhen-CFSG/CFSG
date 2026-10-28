module

public import Glauberman.SylowAutomorphisms.Abelian
public import Glauberman.SylowAutomorphisms.NormalComplement
public import Theory.GroupTheory.SylowCentralFusion

/-!
# Glauberman's theorem on Sylow pointwise automorphisms

For a finite group with trivial odd core, the pointwise automorphism fixer
of a Sylow two-subgroup has abelian Sylow two-subgroups and a normal odd
complement. The elementary central-involution fusion theorem discharges
the fusion premise in both parts of the proof. Part (a) then supplies the
abelian-Sylow premise of part (b), whose normalizer argument uses Z-star
and Burnside transfer.

Source: G. Glauberman, “On the automorphism group of a finite group having
no non-identity normal subgroups of odd order”, Math. Z. 93 (1966),
Theorem 1(a–b), pp.154,157–158, DOI 10.1007/BF01111033.
The normal-complement conclusion supplies the noncyclic simple branch
of the two-Schreier input in `ChapterI.Section03.SylowAutomorphisms`.
-/

public section
namespace Glauberman.SylowAutomorphisms
open Subgroup

/-- Theorem 1(a), with the elementary fusion premise discharged. -/
theorem fixingSubgroup_sylow_isMulCommutative_of_oddCore_eq_bot
    {G : Type*} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (P : Sylow 2 (fixingSubgroup (MulAut G) (S : Set G))) :
    IsMulCommutative P :=
  fixingSubgroup_sylow_isMulCommutative
    SylowCentralFusion.centralInvolutionFusion hcore S P

/-- Theorem 1(b): the actual pointwise fixer has a normal two-complement.
Neither fusion nor abelian Sylow subgroups remain as additional premises. -/
theorem fixingSubgroup_hasNormalTwoComplement
    {G : Type*} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥) (S : Sylow 2 G) :
    HasNormalPComplement 2 (fixingSubgroup (MulAut G) (S : Set G)) :=
  NormalComplement.fixingSubgroup_normalComplement_of_abelian_sylows
    SylowCentralFusion.centralInvolutionFusion hcore S
    (fixingSubgroup_sylow_isMulCommutative_of_oddCore_eq_bot hcore S)

end Glauberman.SylowAutomorphisms

module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.SolvableLift
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.G2Recognition.Source
public import Theory.AtlasPort.LinearGroups.G2.ParabolicPrimeToResidual
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport

/-!
# The two G₂ entries in the marked Lie sieve

The source S₃ shadow makes Y₊ solvable. The residual identity
O^{3′}((M ∩ L)*) = Y₊* therefore makes the actual intersection's residual
solvable. Recognition identifies that intersection with a full root
parabolic in a Sylow-compatible marking. For every field larger than two,
the intrinsic parabolic residual is nonsolvable, giving a contradiction.
For the binary field the full G₂ group has derived subgroup of index two,
contradicting the actual component's perfectness.

For the proper derived group G₂(2)′, the recognition theorem instead
constructs the required marking. Its proof uses the source residual,
S₃ shadow and three-subgroup order bound to obtain the nontrivial two-core,
then the normalizer cover, Sylow alignment and invariant maximality to
identify the literal intersection. Both root parabolics are fixed by S*,
so in particular both labeled conjugacy classes are preserved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.5–6,
printed pp.104–105 (PDF pp.115–116), and 15.3.26–28, printed pp.1130–1131
(PDF pp.1147–1148). Neither branch uses the later 15.3.30–31 elimination.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

private theorem yplus_solvable (a : Input d I c) : Group.IsSolvable d.Yplus := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  obtain ⟨e⟩ := a.facts.shadow
  let : Group.IsSolvable ((d.Yplus ⊔ d.S : Subgroup G) ⧸
      pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let := (pCore_isPGroup (p := 2) (G := (d.Yplus ⊔ d.S : Subgroup G))).isNilpotent
  let : Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 (d.Yplus ⊔ d.S : Subgroup G))).mpr
      ⟨inferInstance, inferInstance⟩
  exact Group.isSolvable_of_isSolvable_injective (f := inclusion (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left))
    (inclusion_injective le_sup_left)

private theorem intersection_residual_solvable (a : Input d I c) :
    Group.IsSolvable (primeToResidual 3 (d.starImage I (d.M ⊓ c.L))) := by
  let := yplus_solvable a
  let j := subgroupOfEquivOfLe (a.yplus_le_intersection.trans inf_le_right)
  let : Group.IsSolvable (d.Yplus.subgroupOf I) :=
    Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective
  let : Group.IsSolvable (d.starImage I d.Yplus) :=
    Group.isSolvable_of_surjective ((d.starMap I).subgroupMap_surjective
      (d.Yplus.subgroupOf I))
  let f := (d.starImage I (d.M ⊓ c.L)).subtype
  have hs : Group.IsSolvable ((primeToResidual 3 (d.starImage I (d.M ⊓ c.L))).map f) :=
    a.componentIntersectionStar_residual ▸ inferInstance
  let := hs
  exact Group.isSolvable_of_isSolvable_injective
    (f := f.subgroupMap (primeToResidual 3 (d.starImage I (d.M ⊓ c.L))))
    (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun x => x.val) h)))

/-- No full G₂ model satisfies the source Lie-sieve input, including the full
binary group, which is distinguished from its proper commutator subgroup. -/
theorem g2_excluded (a : Input d I c) (F : ClassificationField)
    (e : d.starImage I c.L ≃* Atlas.G2.Model F.Carrier) : False := by
  by_cases hq : Nat.card F.Carrier = 2
  · let := c.star_quasisimple
    let := Fintype.ofFinite F.Carrier
    let k : F.Carrier ≃+* ZMod 2 := (ZMod.ringEquiv F.Carrier
      (by simpa only [← Nat.card_eq_fintype_card] using hq)).symm
    let f := e.trans (Atlas.G2.fieldEquiv k)
    let : Group.IsPerfect (Atlas.G2.Model (ZMod 2)) :=
      Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
    have ht : Atlas.G2.BinaryException.H = ⊤ :=
      Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure.symm.trans
        Group.IsPerfect.commutator_eq_top
    have hi := Atlas.G2.BinaryException.index_H
    rw [ht, index_top] at hi
    omega
  · have hgt : 2 < Nat.card F.Carrier := by
      have := Finite.one_lt_card (α := F.Carrier)
      omega
    obtain ⟨f, i, hi⟩ := G2Recognition.full_recognition a F e
    let L := d.starImage I c.L
    let P := d.starImage I (d.M ⊓ c.L)
    let J := P.subgroupOf L
    let t : P ≃* (if i = 0 then Atlas.G2.LieParabolicSetup.parabolic₁ (F := F.Carrier)
        else Atlas.G2.LieParabolicSetup.parabolic₂ : Subgroup (Atlas.G2.Model F.Carrier)) :=
      (subgroupOfEquivOfLe a.componentIntersectionStar_lt.le).symm.trans
        ((f.subgroupMap J).trans (MulEquiv.subgroupCongr hi))
    let r := primeToResidualEquiv 3 t
    let := intersection_residual_solvable a
    exact Atlas.G2.LieParabolicSetup.parabolic_primeToResidual_not_solvable hgt i
      (Group.isSolvable_of_surjective (f := r.toMonoidHom) r.surjective)

/-- The binary derived G₂ alternative, with the literal component intersection
and preservation of both labeled parabolic classes by every element of S*. -/
theorem g2DerivedTwo_marking (a : Input d I c)
    (e : d.starImage I c.L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Nonempty (RankTwoParabolicMarking d I c.L (commutator (Atlas.G2.Model (ZMod 2)))
      g2DerivedParabolic) :=
  G2Recognition.binary_marking a e

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve

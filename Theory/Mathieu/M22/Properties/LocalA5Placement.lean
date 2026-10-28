module

public import Theory.Mathieu.M22.Properties.LocalA5Placement.Core
public import Theory.Mathieu.M22.Properties.LocalA5Placement.Quintet
public import Theory.Mathieu.M22.Properties.LocalA5Placement.Hexad

/-!
# Marked placement of the local E16:A5 subgroup in M22

Conjugate the given full Sylow to the simultaneous source Sylow and retain
the same conjugation on the original subgroup. Local subnormality places its
intrinsic elementary core in that Sylow. The two-core catalogue gives hexad
or quintet type. The hexad quotient would contain a locally subnormal A5 at
a full Sylow of A6, which is impossible. The quintet core fixes precisely a
tetrad, and perfectness forces the original subgroup to be its pointwise
stabilizer. The resulting marking is an actual automorphism of native M22.

Source: Aschbacher--Smith A.3.12(12), A.3.14(6), pp.47--49, used in 10.2.9,
pp.750--751. All model identifications and both branches are discharged here.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped Pointwise
namespace Sporadic.Mathieu.M22LocalA5Placement
open M22ChapterH

private theorem local_subnormal_map {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (B S : Subgroup X)
    (hB : (B.subgroupOf (B ⊔ S)).IsSubnormal) :
    ((B.map e.toMonoidHom).subgroupOf
      (B.map e.toMonoidHom ⊔ S.map e.toMonoidHom)).IsSubnormal := by
  let H := B ⊔ S
  let J := B.map e.toMonoidHom ⊔ S.map e.toMonoidHom
  let eH : H ≃* J := (e.subgroupMap H).trans
    (MulEquiv.subgroupCongr (by
      change (B ⊔ S).map e.toMonoidHom = B.map e.toMonoidHom ⊔ S.map e.toMonoidHom
      rw [Subgroup.map_sup]))
  have hh := hB.map (f := eH.toMonoidHom) eH.surjective
  have hm : (B.subgroupOf H).map eH.toMonoidHom =
      (B.map e.toMonoidHom).subgroupOf J := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨b.val,hb,rfl⟩
    · rintro ⟨b,hb,hbx⟩
      exact ⟨⟨b,(show B ≤ H from le_sup_left) hb⟩,hb,Subtype.ext hbx⟩
  rw [hm] at hh
  exact hh

/-- The full local Sylow and actual E16 core determine a marking of the native
A5 block. The hexad alternative is excluded before using quintet geometry. -/
theorem exists_marking
    (S : Sylow 2 M22) (B : Subgroup M22)
    (hsub : (B.subgroupOf (B ⊔ (S : Subgroup M22))).IsSubnormal)
    [Group.IsPerfect B]
    (hE : IsElementaryAbelian 2 (pCore 2 B))
    (h16 : Nat.card (pCore 2 B) = 16)
    (eB : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5)) :
    ∃ a : MulAut M22,
      Quintet.naturalActor.map M22Quintet.Q.subtype ≤
        (B.map a.toMonoidHom).map m22ToPairStabilizer := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M22 S CompatibleSylow.inner
  let a := MulAut.conj g
  have hS : (S : Subgroup M22).map a.toMonoidHom = CompatibleSylow.inner.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  let C := B.map a.toMonoidHom
  have hC : (C.subgroupOf (C ⊔ CompatibleSylow.inner.toSubgroup)).IsSubnormal := by
    have hh := local_subnormal_map a B (S : Subgroup M22) hsub
    rw [hS] at hh
    exact hh
  let e := a.subgroupMap B
  let ec : pCore 2 B ≃* pCore 2 C :=
    (e.subgroupMap (pCore 2 B)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  let : IsElementaryAbelian 2 (pCore 2 B) := hE
  let : IsElementaryAbelian 2 (pCore 2 C) :=
    IsElementaryAbelian.of_surjective ec.toMonoidHom ec.surjective
  have he : IsElementaryAbelian 2 (C.pCoreIn 2) := IsElementaryAbelian.map C.subtype
  have hc : Nat.card (pCore 2 C) = 16 := (Nat.card_congr ec.toEquiv).symm.trans h16
  have hac : Nat.card (C.pCoreIn 2) = 16 := by
    rw [pCoreIn, card_map_of_injective C.subtype_injective, hc]
  let eq : (B ⧸ pCore 2 B) ≃* (C ⧸ pCore 2 C) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let eqC := eq.symm.trans eB
  have hcore : C.pCoreIn 2 = m22InnerQuintetKernel m22SourceSextet :=
    (marked_core_cases C hC he hac).resolve_left (core_ne_hexad_kernel C hC eqC)
  have hq : (pCore 2 C).index = 60 := by
    change Nat.card (C ⧸ pCore 2 C) = 60
    rw [Nat.card_congr eqC.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hcard : Nat.card C = 960 := by
    rw [← (pCore 2 C).card_mul_index, hc, hq]
  let : Group.IsPerfect C := Group.IsPerfect.map _
  exact ⟨a, (quintet_core_placement C hcore hcard).symm.le⟩

end Sporadic.Mathieu.M22LocalA5Placement

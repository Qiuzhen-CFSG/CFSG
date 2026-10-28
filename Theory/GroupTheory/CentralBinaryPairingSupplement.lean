module
public import Theory.ElementaryAbelian.BinaryPairingDuality
public import Theory.GroupAction.QuotientCommutatorPairing
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A central binary pairing gives a centralizer supplement

Let Z≤V≤U≤Q be actual finite subgroups, with V elementary abelian,
Z of order two, and the literal quotients V/Z and U/V elementary abelian
of equal order. Suppose Q fixes Z, [V,Q]≤Z, and C_V(U)=Z. Then
Q=C_Q(V)U and C_Q(V)∩U=V. No order bound on Q/U or ambient normality
of U is assumed; the supplied quotient normality instances are retained.

The existing central commutator homomorphism, evaluated in Z modulo the
trivial subgroup, factors through both literal quotients. Its left kernel
is C_V(U)/Z. Finite binary duality therefore makes the right map bijective.
Injectivity identifies C_U(V)=V. Surjectivity matches the functional of
each q∈Q by an element u∈U, so q/u centralizes V and yields the product.

This source-neutral algebra supplies the terminal core supplement in
Stellmacher (10.1), Journal of Algebra 190 (1997), printed p.65 immediately
after (20). The native application proves every hypothesis from the
actual Section Ten geometry and sources (14)/(18).
-/

namespace Subgroup
open scoped IsMulCommutative commutatorElement

public theorem eq_centralizer_sup_of_binary_pairing
    {G : Type*} [Group G] [Finite G]
    (Q U V Z : Subgroup G) [IsElementaryAbelian 2 V]
    [hNZ : (Z.subgroupOf V).Normal] [hNV : (V.subgroupOf U).Normal]
    [IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V)]
    [IsElementaryAbelian 2 (U ⧸ V.subgroupOf U)]
    (hUQ : U≤Q) (hVU : V≤U) (hZV : Z≤V) (hZcard : Nat.card Z=2)
    (hcard : Nat.card (V ⧸ Z.subgroupOf V)=Nat.card (U ⧸ V.subgroupOf U))
    (hcentral : Q≤centralizer (Z:Set G)) (hcomm : ⁅V,Q⁆≤Z)
    (hfixed : V⊓centralizer (U:Set G)=Z) :
    Q=(Q⊓centralizer (V:Set G))⊔U ∧
      (Q⊓centralizer (V:Set G))⊓U=V := by
  classical
  let C := Q⊓centralizer (V:Set G)
  let A := V ⧸ Z.subgroupOf V
  let B := U ⧸ V.subgroupOf U
  let πV : V→*A := QuotientGroup.mk' (Z.subgroupOf V)
  let πU : U→*B := QuotientGroup.mk' (V.subgroupOf U)
  let ι := Subgroup.inclusion hUQ
  have hVQ : V≤Q := hVU.trans hUQ
  let _ : IsMulCommutative Z := ⟨⟨fun x y => Subtype.ext
    (setLike_mul_comm (s:=V) (hZV x.property) (hZV y.property))⟩⟩
  have hbot : (⊥:Subgroup G).subgroupOf Z=(⊥:Subgroup Z) := by ext z; simp
  let _ : ((⊥:Subgroup G).subgroupOf Z).Normal := hbot.symm ▸ inferInstance
  let e0 : (Z ⧸ (⊥:Subgroup G).subgroupOf Z)≃*Z :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let eZ : Z≃*Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hZcard (by simp)
  have hZQ : ⁅Z,Q⁆≤⊥ := by
    rw [le_bot_iff,commutator_comm,commutator_eq_bot_iff_le_centralizer]
    exact hcentral
  let raw := (quotientCommutatorPairing V Q Z ⊥ hZV hcomm hZQ).compr₂
    (e0.trans eZ).toMonoidHom
  have hraw (v:V) (q:Q) :
      raw v q=eZ ⟨⁅(v:G),(q:G)⁆,hcomm (commutator_mem_commutator v.property q.property)⟩ := by
    dsimp only [raw]
    rw [MonoidHom.compr₂_apply,quotientCommutatorPairing_apply]
    change eZ (e0 (QuotientGroup.mk' ((⊥:Subgroup G).subgroupOf Z) _))=_
    simp only [e0,MulEquiv.trans_apply]
    rfl
  have hraw_one (v:V) (q:Q) : raw v q=1 ↔ Commute (v:G) (q:G) := by
    rw [hraw,←eZ.map_one,eZ.injective.eq_iff,Subtype.ext_iff]
    change ⁅(v:G),(q:G)⁆=1 ↔ _
    exact commutatorElement_eq_one_iff_mul_comm
  have hkillZ : Z.subgroupOf V≤raw.ker := by
    intro z hz
    apply MonoidHom.ext
    intro q
    apply (hraw_one z q).mpr
    exact mem_centralizer_iff.mp (hcentral q.property) z hz
  let first : A→*(Q→*Multiplicative (ZMod 2)) :=
    QuotientGroup.lift (Z.subgroupOf V) raw hkillZ
  have hkillV (a:A) : V.subgroupOf U≤((first a).comp ι).ker := by
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf V) a
    intro u hu
    change raw v (ι u)=1
    apply (hraw_one v (ι u)).mpr
    exact setLike_mul_comm (s:=V) v.property hu
  let pairing : A→*(B→*Multiplicative (ZMod 2)) := {
    toFun a := QuotientGroup.lift (V.subgroupOf U) ((first a).comp ι) (hkillV a)
    map_one' := by
      apply MonoidHom.ext
      intro b
      obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf U) b
      change first 1 (ι u)=1
      simp
    map_mul' a b := by
      apply MonoidHom.ext
      intro c
      obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf U) c
      change first (a*b) (ι u)=first a (ι u)*first b (ι u)
      rw [map_mul]
      rfl }
  have happly (v:V) (u:U) : pairing (πV v) (πU u)=raw v (ι u) := rfl
  have hinj : Function.Injective pairing := by
    apply (MonoidHom.ker_eq_bot_iff pairing).mp
    apply bot_unique
    intro a ha
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf V) a
    have hvZ : (v:G)∈Z := by
      apply hfixed.le
      refine ⟨v.property,mem_centralizer_iff.mpr ?_⟩
      intro u hu
      have hh := congrArg (fun f:B→*Multiplicative (ZMod 2) => f (πU ⟨u,hu⟩)) ha
      have hrawzero : raw v (ι ⟨u,hu⟩)=1 := hh
      exact ((hraw_one v (ι ⟨u,hu⟩)).mp hrawzero).symm.eq
    exact (QuotientGroup.eq_one_iff (N:=Z.subgroupOf V) v).mpr hvZ
  have hperfect := MonoidHom.binary_pairing_flip_bijective pairing hcard hinj
  have hVC : V≤C := le_inf hVQ (le_centralizer V)
  have hCU : C⊓U=V := by
    apply le_antisymm ?_ (le_inf hVC hVU)
    intro c hc
    let u : U := ⟨c,hc.2⟩
    have hzero : pairing.flip (πU u)=1 := by
      apply MonoidHom.ext
      intro a
      obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf V) a
      change raw v (ι u)=1
      apply (hraw_one v (ι u)).mpr
      exact mem_centralizer_iff.mp hc.1.2 v v.property
    have hu : πU u=1 := hperfect.1 (hzero.trans pairing.flip.map_one.symm)
    exact (QuotientGroup.eq_one_iff (N:=V.subgroupOf U) u).mp hu
  refine ⟨le_antisymm ?_ (sup_le inf_le_left hUQ),hCU⟩
  intro q hq
  obtain ⟨b,hb⟩ := hperfect.2 (first.flip ⟨q,hq⟩)
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf U) b
  have hmatch (v:V) : raw v (ι u)=raw v ⟨q,hq⟩ :=
    congrArg (fun f:A→*Multiplicative (ZMod 2) => f (πV v)) hb
  let c : Q := ⟨q,hq⟩/(ι u)
  have hc : (c:G)∈C := by
    refine ⟨c.property,mem_centralizer_iff.mpr ?_⟩
    intro v hv
    have hzero : raw ⟨v,hv⟩ c=1 := by
      change raw ⟨v,hv⟩ (⟨q,hq⟩/(ι u))=1
      rw [map_div,hmatch]
      simp
    exact ((hraw_one ⟨v,hv⟩ c).mp hzero).eq
  have hm := (C⊔U).mul_mem ((le_sup_left:C≤C⊔U) hc) ((le_sup_right:U≤C⊔U) u.property)
  change (q/(u:G))*(u:G)∈C⊔U at hm
  simpa only [div_mul_cancel] using hm

end Subgroup

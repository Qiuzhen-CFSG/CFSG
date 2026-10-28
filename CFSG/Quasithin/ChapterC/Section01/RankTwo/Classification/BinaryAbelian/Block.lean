module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.Intrinsic
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility

/-!
# The actual block in the abelian one-copy MS branch

The natural quotient acts irreducibly on the intrinsic block module. Subnormal
Fitting monotonicity, perfectness and the proved elementary-core and centrality
facts establish every short-group clause. The quotient isomorphism intertwines
literal conjugation, including when the core has a nontrivial fixed line.

The final original-input alternative is an SL₃(2)-block or an equivariant
isomorphism of the whole core with two natural copies. It does not yet assert
the radical inequalities or the index-seven clause of full C.1.34.

Source: Aschbacher–Smith C.1.7, C.1.34(1),(2),(5), printed pp.123,136–137.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
abbrev AbelianNaturalVector := Fin 3 → ZMod 2
abbrev AbelianNaturalActor := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

private theorem natural_subgroup_cases (A : Subgroup (Multiplicative AbelianNaturalVector))
    (hA : ∀ g v, v ∈ A → Multiplicative.ofAdd (specialLinearNatural 3 g v.toAdd) ∈ A) :
    A = ⊥ ∨ A = ⊤ := by
  let W : Subrepresentation (specialLinearNatural (k := ZMod 2) 3) := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 A.toAddSubgroup
    apply_mem_toSubmodule := hA }
  let : IsIrreducible (specialLinearNatural (k := ZMod 2) 3) :=
    BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  rcases eq_bot_or_eq_top W with hb | ht
  · left
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro x hx
    have hxW : x.toAdd ∈ W := hx
    rw [hb] at hxW
    exact hxW
  · right
    apply top_unique
    intro x _
    have hxW : x.toAdd ∈ W := by rw [ht]; trivial
    exact hxW

variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)

include h in
private theorem component_fitting : generalizedFitting L = pCore 2 L := by
  apply le_antisymm _ ((pCore_le_fitting L 2).trans (fitting_le_generalizedFitting L))
  rw [pCore_subnormal_eq_comap 2 h.component.subnormal]
  apply map_le_iff_le_comap.mp
  rw [← h.fitting]
  exact generalizedFitting_map_subtype_le_of_isSubnormal L h.component.subnormal

namespace AbelianCore.NaturalQuotient
variable {h} (q : AbelianCore.NaturalQuotient h 1)
noncomputable def singleProjection : blockU L →* Multiplicative AbelianNaturalVector where
  toFun x := Multiplicative.ofAdd ((q.intrinsicProjection x).toAdd 0)
  map_one' := by rw [map_one]; rfl
  map_mul' x y := by rw [map_mul]; rfl

theorem singleProjection_surjective : Function.Surjective q.singleProjection := by
  intro v
  obtain ⟨x,hx⟩ := q.intrinsicProjection_surjective (Multiplicative.ofAdd (fun _ => v.toAdd))
  exact ⟨x, congrArg (fun y => Multiplicative.ofAdd (y.toAdd 0)) hx⟩

theorem singleProjection_kernel : q.singleProjection.ker = blockFixed L := by
  rw [← q.intrinsicProjection_kernel]
  ext x
  change Multiplicative.ofAdd ((q.intrinsicProjection x).toAdd 0) = 1 ↔
    q.intrinsicProjection x = 1
  constructor
  · intro hx
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    change (q.intrinsicProjection x).toAdd i = 0
    rw [hi]
    exact congrArg Multiplicative.toAdd hx
  · intro hx
    rw [hx]
    rfl

theorem singleProjection_conjugate (l : L) (x : blockU L) :
    (q.singleProjection (blockConjugate L l x)).toAdd =
      specialLinearNatural 3 (q.quotientEquiv (QuotientGroup.mk' _ l))
        (q.singleProjection x).toAdd := q.intrinsicProjection_conjugate l x 0

include q in
theorem block_irreducible : BlockModuleIrreducible L := by
  have hneq : blockU L ⊓ center L ≠ blockU L := by
    intro he
    have hz : ∀ x, q.singleProjection x = 1 := by
      intro x
      have hx : x ∈ q.singleProjection.ker := by
        rw [q.singleProjection_kernel]
        have hx' : (x : L) ∈ blockU L ⊓ center L := by rw [he]; exact x.property
        exact hx'.2
      exact hx
    obtain ⟨x,hx⟩ := q.singleProjection_surjective (Multiplicative.ofAdd (fun _ => 1))
    have hh := (hz x).symm.trans hx
    have hh' := congrArg (fun y : Multiplicative AbelianNaturalVector => y.toAdd 0) hh
    exact zero_ne_one hh'
  refine ⟨lt_of_le_of_ne inf_le_left hneq, ?_⟩
  intro N hN hlow hhigh
  let := hN
  let A := (N.subgroupOf (blockU L)).map q.singleProjection
  have hA : ∀ g v, v ∈ A → Multiplicative.ofAdd (specialLinearNatural 3 g v.toAdd) ∈ A := by
    intro g v hv
    obtain ⟨l,rfl⟩ := q.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _) g
    obtain ⟨x,hx,rfl⟩ := hv
    refine ⟨blockConjugate L l x, hN.conj_mem x hx l, ?_⟩
    exact congrArg Multiplicative.ofAdd (q.singleProjection_conjugate l x)
  rcases natural_subgroup_cases A hA with hb | ht
  · left
    apply le_antisymm _ hlow
    intro x hx
    refine ⟨hhigh hx, ?_⟩
    have hxA : q.singleProjection ⟨x,hhigh hx⟩ ∈ A := mem_map_of_mem _ hx
    have hxker : (⟨x,hhigh hx⟩ : blockU L) ∈ q.singleProjection.ker := by
      change q.singleProjection ⟨x,hhigh hx⟩ = 1
      simpa only [hb, mem_bot] using hxA
    rwa [q.singleProjection_kernel] at hxker
  · right
    apply le_antisymm hhigh
    intro x hx
    have hxA : q.singleProjection ⟨x,hx⟩ ∈ A := ht ▸ mem_top _
    obtain ⟨y,hy,he⟩ := hxA
    have hd : (⟨x,hx⟩ : blockU L) * y⁻¹ ∈ q.singleProjection.ker := by
      change q.singleProjection (_ * _) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    rw [q.singleProjection_kernel] at hd
    have hn : x * (y : L)⁻¹ ∈ N := hlow ⟨(blockU L).mul_mem hx ((blockU L).inv_mem y.property),hd⟩
    have hh : x * (y : L)⁻¹ * (y : L) ∈ N := N.mul_mem hn hy
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

include q in
theorem block_short (hc : IsMulCommutative (commutatorCore L)) : IsShort L := by
  let := h.component.perfect
  have hp : IsPPerfect 2 L := by
    intro N hn hq
    let := hn
    have hs : Subsingleton (L ⧸ N) := by
      by_contra! hnt
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hq.isNilpotent
    apply eq_top_iff.mpr
    intro l _
    exact (QuotientGroup.eq_one_iff l).mp (Subsingleton.elim _ _)
  have he : IsElementaryAbelian 2 (blockU L) := by
    let := h.abelianCore_elementary_of_naturalQuotient hc q
    exact IsElementaryAbelian.of_surjective h.intrinsicCoreEquiv.symm.toMonoidHom
      h.intrinsicCoreEquiv.symm.surjective
  have hc' : blockU L ≤ centralizer (pCore 2 L : Set L) := by
    intro x hx y hy
    apply Subtype.ext
    have hx' := (h.abelianCore_componentCore_centralizes_of_naturalQuotient hc q)
      (h.intrinsicCoreEquiv ⟨x,hx⟩).property
    exact hx' y (mem_map_of_mem L.subtype hy)
  have hq : IsQuasisimple (L ⧸ pCore 2 L) := by
    let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup (L ⧸ pCore 2 L) :=
      (h.quotientEquiv.trans Matrix.PSL3Two.equiv).isSimpleGroup
    exact { toIsPerfect := inferInstance
            simple := ((QuotientGroup.quotientMulEquivOfEq h.quotient_center).trans
              QuotientGroup.quotientBot).isSimpleGroup }
  exact ⟨inferInstance, hp, component_fitting h, he, hc', Or.inl hq, q.block_irreducible⟩

noncomputable def singleModuleEquiv : BlockModule L ≃* Multiplicative AbelianNaturalVector :=
  (QuotientGroup.quotientMulEquivOfEq q.singleProjection_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q.singleProjection q.singleProjection_surjective)

@[simp] theorem singleModuleEquiv_mk (x : blockU L) :
    q.singleModuleEquiv (QuotientGroup.mk' (blockFixed L) x) = q.singleProjection x := rfl

private def naturalAction : AbelianNaturalActor →* MulAut (Multiplicative AbelianNaturalVector) where
  toFun g := (Matrix.SpecialLinearGroup.toLin' g).toAddEquiv.toMultiplicative
  map_one' := by ext v : 1; change Matrix.SpecialLinearGroup.toLin' 1 v.toAdd = v.toAdd; rw [map_one]; rfl
  map_mul' g h := by
    ext v : 1
    change Matrix.SpecialLinearGroup.toLin' (g*h) v.toAdd =
      Matrix.SpecialLinearGroup.toLin' g (Matrix.SpecialLinearGroup.toLin' h v.toAdd)
    rw [map_mul]
    rfl

include q in
theorem block_model : IsLinearBlockModel L (specialLinearNatural (k := ZMod 2) 3) := by
  refine ⟨naturalAction,⟨{
    quotientIso := q.quotientEquiv
    moduleIso := q.singleModuleEquiv
    intertwining := ?_ }⟩,fun _ _ => rfl⟩
  intro l x
  rw [q.singleModuleEquiv_mk,q.singleModuleEquiv_mk]
  exact congrArg Multiplicative.ofAdd (q.singleProjection_conjugate l x)

include q in
theorem block_type (hc : IsMulCommutative (commutatorCore L)) : IsSL3EvenBlock L 1 :=
  ⟨by decide,q.block_short hc,ZMod 2,inferInstance,inferInstance,by norm_num,q.block_model⟩

end AbelianCore.NaturalQuotient

include h in
/-- The genuine abelian source gives either an SL₃(2)-block or the literal doubled natural core. -/
theorem Input.abelian_block_or_double
    (hc : IsMulCommutative (commutatorCore L)) :
    IsSL3EvenBlock L 1 ∨
      ∃ (e : (L ⧸ pCore 2 L) ≃* AbelianNaturalActor)
        (f : commutatorCore L ≃* Multiplicative (Fin 2 → AbelianNaturalVector)),
        ∀ l x i, (f (h.coreConjugate l x)).toAdd i =
          specialLinearNatural 3 (e (QuotientGroup.mk' (pCore 2 L) l)) ((f x).toAdd i) := by
  obtain ⟨m,hm,⟨q⟩⟩ := AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient
    (h := h) hc
  rcases hm with rfl | rfl
  · exact Or.inl (q.block_type hc)
  · right
    have hk := h.abelianCore_fixedKernel_eq_one_of_twoCopies hc q
    have hbot : coreFixed L = ⊥ := Subgroup.card_eq_one.mp hk
    have hi : Function.Injective q.projection := by
      rw [← MonoidHom.ker_eq_bot_iff,q.kernel,hbot]
    refine ⟨q.quotientEquiv,MulEquiv.ofBijective q.projection ⟨hi,q.surjective⟩,?_⟩
    exact q.equivariant

include h in
/-- The one-copy block is forced whenever the original core does not have order 64. -/
theorem Input.abelian_block_of_card_ne_sixtyFour
    (hc : IsMulCommutative (commutatorCore L))
    (hcard : Nat.card (commutatorCore L) ≠ 64) : IsSL3EvenBlock L 1 := by
  rcases h.abelian_block_or_double hc with hb | ⟨e,f,_⟩
  · exact hb
  · apply (hcard _).elim
    rw [Nat.card_congr f.toEquiv]
    change Nat.card (Fin 2 → Fin 3 → ZMod 2) = 64
    simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
    norm_num

end CFSG.Quasithin.ChapterC.BinaryMS

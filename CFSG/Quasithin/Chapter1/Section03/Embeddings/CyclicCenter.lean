module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Extension
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
/-!
# A Xi complement cannot be normal inside a cyclic-center component

Two-perfectness places the actual residual in the conjugate orbit. If it
were normal in an overgroup containing a quasisimple component quotient
with cyclic center, its solvable quotient image would be central. The odd
Sylow complement injects through the two-core quotient, contradicting its
noncyclicity. All subgroup inclusions and quotient maps are retained.

Source: the normal alternative in Aschbacher--Smith 1.3.4 as used in
13.3.14(d), printed pp.509--511,892.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem le_componentOrbit_of_twoPerfect {T X B : Subgroup G}
    (hp : IsPPerfect 2 X) (hT : IsPGroup 2 T) (hXB : X ≤ B ⊔ T) :
    X ≤ componentOrbit B T := by
  let H := B ⊔ T
  let N := (componentOrbit B T).subgroupOf H
  let : N.Normal := componentOrbit_normal_subgroupOf_sup B T
  let q := QuotientGroup.mk' N
  let f : X →* H ⧸ N := q.comp (inclusion hXB)
  have hf : f = 1 := hp.hom_eq_one_of_isPGroup
    (componentOrbit_quotient_isPGroup B T hT) f
  intro x hx
  have he : q ⟨x,hXB hx⟩ = 1 := congrArg (fun a : X →* H ⧸ N => a ⟨x,hx⟩) hf
  have hh : (⟨x,hXB hx⟩ : H) ∈ N := (QuotientGroup.eq_one_iff _).mp he
  exact hh

theorem LocalInput.not_normal_in_cyclic_center_component
    {p : ℕ} {T X P H K : Subgroup G} (h : LocalInput p T X P H)
    (hX : X ∈ Xi G T) (hXK : X ≤ K) (hKH : K ≤ H)
    [IsQuasisimple (XiQuotient K)] [IsCyclic (center (XiQuotient K))] :
    ¬ (X.subgroupOf H).Normal := by
  intro hn
  let : Fact p.Prime := ⟨h.prime⟩
  have hXH : X ≤ H := le_sup_left.trans h.overgroup
  have hKX : K ≤ normalizer X := hKH.trans
    ((normal_subgroupOf_iff_le_normalizer hXH).mp hn)
  let R := X.subgroupOf K
  let : R.Normal := normal_subgroupOf_of_le_normalizer hKX
  let : Group.IsSolvable X := hX.isSolvable
  let : Group.IsSolvable R := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hXK).toMonoidHom) (subgroupOfEquivOfLe hXK).injective
  let q := QuotientGroup.mk' (pCore 2 K)
  let A := R.map q
  let : A.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable A := Group.isSolvable_of_surjective (q.subgroupMap_surjective R)
  have hAZ : A ≤ center (XiQuotient K) :=
    (le_solvableRadical A inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center
  have hPX : P ≤ X := h.complement ▸ le_sup_right
  have hPK : P ≤ K := hPX.trans hXK
  let f : P →* XiQuotient K := q.comp (inclusion hPK)
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    have hcore : (⟨a,hPK a.property⟩ : K) ∈ pCore 2 K :=
      (QuotientGroup.eq_one_iff _).mp ha
    have hd : Disjoint (pCore 2 K) (P.subgroupOf K) :=
      pCore_isPGroup.disjoint_of_coprime h.odd_complement.isPGroup.comap_subtype
        (Nat.coprime_two_left.mpr h.odd)
    have he : (⟨a,hPK a.property⟩ : K) = 1 := hd.le_bot ⟨hcore,a.property⟩
    exact Subtype.ext (congrArg (fun b : K => (b : G)) he)
  let z : P →* center (XiQuotient K) := f.codRestrict _ (fun a =>
    hAZ (mem_map.mpr ⟨⟨a,hPK a.property⟩,hPX a.property,rfl⟩))
  exact h.complement_not_cyclic (isCyclic_of_injective z (by
    intro a b he
    exact hi (congrArg Subtype.val he)))
end CFSG.Quasithin.Chapter1.XiEmbedding

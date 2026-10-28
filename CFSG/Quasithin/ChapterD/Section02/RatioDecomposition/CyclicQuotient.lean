module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.ClassifiedFactors
public import Theory.GroupTheory.Fitting.Subgroup
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The Fitting quotient of the classified cyclic factors

The source classification supplies a normal odd prime-power kernel and an
involution supplement in each literal indecomposable factor. The kernel maps
into the Fitting subgroup of its actor, and characteristicity transfers that
Fitting subgroup into the decomposed group. Each factor therefore has a
two-group image modulo the intrinsic Fitting subgroup. The factors are normal
and generate the decomposed group, so the whole quotient is a two-group.
Normality then sends its intrinsic Fitting subgroup into the ambient Fitting
subgroup and puts the original subgroup in the preimage of the quotient two-core.

The actors are only assumed normal in the decomposed subgroup. Full Fitting
movement remains on every classified factor and is supplied by the earlier
seed reduction. Source: Aschbacher--Smith D.2.16--17, printed pp.187--189,
and the original starred-actor join in 15.1.2, printed pp.1084--1085.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
universe u

private theorem fitting_normal_le {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] : (fittingSubgroup K).map K.subtype ≤ fittingSubgroup G :=
  le_sSup ⟨fittingSubgroupOf_normal K inferInstance,fittingSubgroupOf_isNilpotent K⟩

private theorem local_kernel_le_fitting {D K Y : Type*} [Group D] [Finite D]
    [Group K] [Finite K] [AddCommGroup Y] [Module (ZMod 2) Y]
    {σ : Representation (ZMod 2) D Y} (l : CyclicSource.LocalGeneration σ)
    (f : D →* K) (hf : Function.Injective f) [f.range.Normal] :
    l.kernel.map f ≤ fittingSubgroup K := by
  let e := MonoidHom.ofInjective hf
  let : l.kernel.Normal := l.normal
  let : Fact l.prime.Prime := ⟨l.prime_prime⟩
  let : Group.IsNilpotent l.kernel := l.pgroup.isNilpotent
  have hn : (l.kernel.map e.toMonoidHom).Normal := Normal.map l.normal _ e.surjective
  have hnil : Group.IsNilpotent (l.kernel.map e.toMonoidHom) :=
    Group.nilpotent_of_surjective (e.toMonoidHom.subgroupMap l.kernel)
      (e.toMonoidHom.subgroupMap_surjective l.kernel)
  have hle : l.kernel.map e.toMonoidHom ≤ fittingSubgroup f.range := le_sSup ⟨hn,hnil⟩
  have hm := (map_mono hle (f := f.range.subtype)).trans (fitting_normal_le f.range)
  rw [map_map] at hm
  have he : f.range.subtype.comp e.toMonoidHom = f := by ext x; rfl
  rwa [he] at hm

private theorem local_image_two {D K Y : Type*} [Group D] [Finite D]
    [Group K] [Finite K] [AddCommGroup Y] [Module (ZMod 2) Y]
    {σ : Representation (ZMod 2) D Y} (l : CyclicSource.LocalGeneration σ)
    (f : D →* K) (hf : Function.Injective f) [f.range.Normal] :
    IsPGroup 2 (f.range.map (QuotientGroup.mk' (fittingSubgroup K))) := by
  let q := QuotientGroup.mk' (fittingSubgroup K)
  let φ := q.comp f
  have hk : l.kernel.map φ = ⊥ := by
    apply bot_unique
    rintro y ⟨x,hx,rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr
      (local_kernel_le_fitting l f hf (mem_map.mpr ⟨x,hx,rfl⟩))
  have ht : IsPGroup 2 (zpowers l.involution) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,l.order_two]; norm_num)
  have hg := congrArg (Subgroup.map φ) l.generated
  rw [Subgroup.map_sup,hk,bot_sup_eq,←MonoidHom.range_eq_map] at hg
  have hh := ht.map φ
  rw [hg] at hh
  rw [show f.range.map (QuotientGroup.mk' (fittingSubgroup K)) = φ.range from
    (MonoidHom.range_comp q f).symm]
  exact hh

namespace FactorData
variable {G V : Type u} [Group G] [Finite G] [Group.IsSolvable G]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {K : Subgroup G} [K.Normal]
    {U : Submodule (ZMod 2) V} (c : FactorData ρ K U)
    (d : Decomposition c.representation)

/-- The classified cyclic factor action makes the intrinsic Fitting quotient a two-group. -/
theorem cyclic_quotient_fitting_two
    (hcore : pCore 2 G = ⊥) (hq : cubicRatio ρ ≤ 2) (hd : d.FittingFull)
    {H : Type*} [Group H] [Finite H] {C : GroupClass}
    (hH : IsSQTK C H) (f : H →* G) (honto : Function.Surjective f)
    (hc : ∀ A ∈ QhatStar ρ, IsCyclic A) : IsPGroup 2 (K ⧸ fittingSubgroup K) := by
  classical
  let q := QuotientGroup.mk' (fittingSubgroup K)
  have hfactor (i : d.Index) : IsPGroup 2 ((d.factor i).actor.map q) := by
    let F := d.factor i
    have hcF : ∀ A ∈ QhatStar F.action, IsCyclic A := by
      intro A hA
      let j := K.subtype.comp F.embedding.groupMap
      have hj : Function.Injective j := K.subtype_injective.comp F.embedding.group_injective
      have hstar : A.map j ∈ QhatStar ρ := by
        rw [←map_map]
        exact (c.stars _).mp ((F.embedding.stars A).mp hA)
      let : IsCyclic (A.map j) := hc _ hstar
      exact isCyclic_of_injective (j.subgroupMap A)
        (by
          intro x y he
          apply Subtype.ext
          apply hj
          exact congrArg (fun z : A.map j => (z : G)) he)
    obtain ⟨l⟩ := c.factor_cyclic_localGeneration d hcore hq hd hH f honto i hcF
    let : F.actor.Normal := d.actor_normal c.representation c.faithful i
    let : F.embedding.groupMap.range.Normal := inferInstanceAs F.actor.Normal
    exact local_image_two l F.embedding.groupMap F.embedding.group_injective
  have hle (i : d.Index) : (d.factor i).actor.map q ≤ pCore 2 (K ⧸ fittingSubgroup K) := by
    let : (d.factor i).actor.Normal := d.actor_normal c.representation c.faithful i
    exact le_sSup ⟨Normal.map inferInstance q (QuotientGroup.mk'_surjective _),hfactor i⟩
  have htop : pCore 2 (K ⧸ fittingSubgroup K) = ⊤ := by
    apply top_unique
    rw [←map_top_of_surjective q (QuotientGroup.mk'_surjective _),←d.group_generation,Subgroup.map_iSup]
    exact iSup_le hle
  exact (htop ▸ pCore_isPGroup).of_equiv Subgroup.topEquiv

/-- Normality transfers the intrinsic result to the literal ambient Fitting quotient. -/
theorem cyclic_image_fitting_two
    (hcore : pCore 2 G = ⊥) (hq : cubicRatio ρ ≤ 2) (hd : d.FittingFull)
    {H : Type*} [Group H] [Finite H] {C : GroupClass}
    (hH : IsSQTK C H) (f : H →* G) (honto : Function.Surjective f)
    (hc : ∀ A ∈ QhatStar ρ, IsCyclic A) :
    IsPGroup 2 (K.map (QuotientGroup.mk' (fittingSubgroup G))) := by
  have hp := c.cyclic_quotient_fitting_two d hcore hq hd hH f honto hc
  intro x
  obtain ⟨k,hk,he⟩ := x.property
  obtain ⟨n,hn⟩ := hp (QuotientGroup.mk' (fittingSubgroup K) ⟨k,hk⟩)
  have hh : (⟨k,hk⟩ : K) ^ 2 ^ n ∈ fittingSubgroup K :=
    (QuotientGroup.eq_one_iff _).mp hn
  refine ⟨n,Subtype.ext ?_⟩
  change (x : G ⧸ fittingSubgroup G) ^ 2 ^ n = 1
  rw [←he,←map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr
    (fitting_normal_le K (mem_map_of_mem K.subtype hh))

/-- The original normal actor lies over the two-core of the ambient Fitting quotient. -/
theorem cyclic_le_twoCore_preimage
    (hcore : pCore 2 G = ⊥) (hq : cubicRatio ρ ≤ 2) (hd : d.FittingFull)
    {H : Type*} [Group H] [Finite H] {C : GroupClass}
    (hH : IsSQTK C H) (f : H →* G) (honto : Function.Surjective f)
    (hc : ∀ A ∈ QhatStar ρ, IsCyclic A) :
    K ≤ (pCore 2 (G ⧸ fittingSubgroup G)).comap (QuotientGroup.mk' (fittingSubgroup G)) := by
  apply map_le_iff_le_comap.mp
  exact le_sSup ⟨Normal.map inferInstance _ (QuotientGroup.mk'_surjective _),
    c.cyclic_image_fitting_two d hcore hq hd hH f honto hc⟩

end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition

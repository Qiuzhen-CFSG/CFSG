module

public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.IsPerfect

/-!
# A perfect normal factor in the two-residual

A centerless perfect normal subgroup with two-group outer automorphism
quotient splits off from O²(G). The other factor is the literal centralizer
intersection. If a local subgroup supplements the perfect factor, has cubic
quotient by its two-core, and escapes that factor, the centralizer intersection
has order three when O₂(G) is trivial. The multiplication isomorphism retains
both actual embeddings.

This is the structural product argument in Aschbacher--Smith F.6.17,
printed p.309; no local or global classification conclusion is assumed.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_le_twoResidual (K : Subgroup G) [Group.IsPerfect K] :
    K ≤ pResidual 2 G := by
  apply le_pResidual_of_isPPerfect
  intro N hN hq
  let : N.Normal := hN
  by_contra hn
  let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
  let : Group.IsPerfect (K ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance

theorem exists_twoResidual_product (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hz : center K = ⊥) (ho : IsPGroup 2 (MulAut.Outer K)) :
    let D := pResidual 2 G ⊓ centralizer (K : Set G)
    K ⊔ D = pResidual 2 G ∧ Disjoint K D ∧
      ∃ e : K × D ≃* pResidual 2 G,
        ∀ k d, (e (k,d) : G) = (k : G) * (d : G) := by
  dsimp only
  let L := pResidual 2 G
  let C := centralizer (K : Set G)
  let D := L ⊓ C
  have hKL : K ≤ L := perfect_le_twoResidual K
  let a : G →* MulAut.Outer K :=
    (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp MulAut.conjNormal
  have hLC : L ≤ K ⊔ C := by
    have hh := pResidual_le_ker_of_isPGroup 2 a ho
    have hk : a.ker = K ⊔ C := by
      change ((QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
        (MulAut.conjNormal : G →* MulAut K)).ker = _
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', MulAut.conjNormal_comap_innerSubgroup]
    exact hk ▸ hh
  have hsup : K ⊔ D = L := by
    apply le_antisymm (sup_le hKL inf_le_left)
    intro x hx
    obtain ⟨k,hk,c,hc,rfl⟩ := mem_sup_of_normal_left.mp (hLC hx)
    have hcL : c ∈ L := (L.mul_mem_cancel_left (hKL hk)).mp hx
    exact (K ⊔ D).mul_mem (mem_sup_left hk) (mem_sup_right ⟨hcL,hc⟩)
  have hd : Disjoint K D := by
    apply disjoint_def.mpr
    intro x hx hd
    have hzmem : (⟨x,hx⟩ : K) ∈ center K :=
      mem_center_iff.mpr (fun k => Subtype.ext (hd.2 k k.property))
    have hx1 : (⟨x,hx⟩ : K) = 1 := by simpa only [hz, mem_bot] using hzmem
    exact congrArg (fun z : K => (z : G)) hx1
  have hc : K ≤ centralizer (D : Set G) := by
    intro k hk d hd
    exact (hd.2 k hk).symm
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting K D hd hc
  exact ⟨hsup,hd,e.trans (MulEquiv.subgroupCongr hsup),he⟩


theorem twoResidual_centralizer_card_three (K A : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hz : center K = ⊥) (ho : IsPGroup 2 (MulAut.Outer K))
    (hcore : pCore 2 G = ⊥) (hgen : K ⊔ A = pResidual 2 G)
    (hne : ¬ A ≤ K) (hthree : Nat.card (A ⧸ pCore 2 A) = 3) :
    Nat.card (pResidual 2 G ⊓ centralizer (K : Set G) : Subgroup G) = 3 := by
  let L := pResidual 2 G
  let D := L ⊓ centralizer (K : Set G)
  obtain ⟨hsup, hd, e, he⟩ := exists_twoResidual_product K hz ho
  change K ⊔ D = L at hsup
  change K × D ≃* L at e
  have hKL : K ≤ L := perfect_le_twoResidual K
  have hAL : A ≤ L := (le_sup_right : A ≤ K ⊔ A).trans hgen.le
  let f : L →* D := (MonoidHom.snd K D).comp e.symm.toMonoidHom
  have hfK (k : K) : f (inclusion hKL k) = 1 := by
    have hk : inclusion hKL k = e (k,1) := Subtype.ext (by simpa using (he k 1).symm)
    rw [hk]
    exact congrArg Prod.snd (e.symm_apply_apply (k,1))
  have hfD (d : D) : f (inclusion inf_le_left d) = d := by
    have hh : inclusion inf_le_left d = e (1,d) := Subtype.ext (by simpa using (he 1 d).symm)
    rw [hh]
    exact congrArg Prod.snd (e.symm_apply_apply (1,d))
  let g : A →* D := f.comp (inclusion hAL)
  have hgs : Function.Surjective g := by
    intro d
    have hdL : (d : G) ∈ K ⊔ A := hgen.symm ▸ d.property.1
    obtain ⟨k,hk,a,ha,hka⟩ := mem_sup_of_normal_left.mp hdL
    refine ⟨⟨a,ha⟩, ?_⟩
    have hdeq : inclusion inf_le_left d = inclusion hKL ⟨k,hk⟩ * inclusion hAL ⟨a,ha⟩ :=
      Subtype.ext hka.symm
    have hh := congrArg f hdeq
    rw [hfD, map_mul, hfK, one_mul] at hh
    exact hh.symm
  have hDcore : pCore 2 D = ⊥ := by
    have hle : (pCore 2 D).map D.subtype ≤ pCore 2 G :=
      le_sSup ⟨inferInstance, pCore_isPGroup.map D.subtype⟩
    apply (map_eq_bot_iff_of_injective _ D.subtype_injective).mp
    exact le_bot_iff.mp (hle.trans hcore.le)
  have hker : pCore 2 A ≤ g.ker := by
    have hmap : (pCore 2 A).map g ≤ pCore 2 D :=
      le_sSup ⟨Normal.map inferInstance g hgs, pCore_isPGroup.map g⟩
    exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp (hmap.trans hDcore.le))
  let q := QuotientGroup.lift (pCore 2 A) g hker
  have hqs : Function.Surjective q := by
    intro d
    obtain ⟨a, ha⟩ := hgs d
    exact ⟨QuotientGroup.mk' _ a, ha⟩
  have hdiv : Nat.card D ∣ 3 := hthree ▸ card_dvd_of_surjective q hqs
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hone | hthree
  · have hb : D = ⊥ := card_eq_one.mp hone
    have hLK : L = K := by simpa [hb] using hsup.symm
    exact (hne (hAL.trans hLK.le)).elim
  · exact hthree

end Theory.GroupTheory

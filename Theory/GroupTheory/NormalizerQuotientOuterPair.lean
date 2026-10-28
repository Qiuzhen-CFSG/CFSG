module
public import Theory.GroupTheory.PairedOuterActionKernel
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Separating two outer coordinates of a normalizer

The normalizer acts on a subgroup modulo its two-core. For two commuting
conjugates generating a normal subgroup N, an actor inducing inner actions
on both quotients lies in N, provided the ambient quotient is a two-group
and its two-core lies in N. The second coordinate is the first action
conjugated by an element exchanging the factors, so the proof retains the
literal action and needs no independently chosen quotient isomorphism.

Source application: Aschbacher--Smith, 2.4.7, printed p.540, where the two
coordinates are the outer actions on the original linear blocks.
-/

@[expose] public section
namespace Subgroup
variable {H : Type*} [Group H]

def normalizerPCoreQuotientAction (L : Subgroup H) : normalizer (L : Set H) →* MulAut (L ⧸ pCore 2 L) :=
  (quotientAut (pCore 2 L)).comp L.normalizerMonoidHom

theorem normalizerPCoreQuotientAction_inner (L : Subgroup H) (l : L) :
    normalizerPCoreQuotientAction L (inclusion L.le_normalizer l) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 L) l) := by
  ext z
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
  change quotientAut (pCore 2 L) _ _ = _
  rw [quotientAut_apply_mk]
  simp only [MulAut.conj_apply, ←map_mul, ←map_inv]
  rfl

theorem normalizerPCoreQuotientAction_centralizer (L : Subgroup H) (b : normalizer (L : Set H))
    (hb : (b:H) ∈ centralizer (L : Set H)) : normalizerPCoreQuotientAction L b = 1 := by
  ext z
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
  change quotientAut (pCore 2 L) _ _ = _
  rw [quotientAut_apply_mk]
  change QuotientGroup.mk' (pCore 2 L) _ = QuotientGroup.mk' (pCore 2 L) u
  apply congrArg (QuotientGroup.mk' (pCore 2 L))
  apply Subtype.ext
  change (b:H)*(u:H)*(b:H)⁻¹=(u:H)
  rw [←hb u u.property, mul_assoc, mul_inv_cancel, mul_one]

private theorem quotient_pGroup_restrict (N B : Subgroup H) [N.Normal]
    (hq : IsPGroup 2 (H ⧸ N)) : IsPGroup 2 (B ⧸ N.subgroupOf B) := by
  intro y
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf B) y
  obtain ⟨m,hm⟩ := hq (QuotientGroup.mk' N (b:H))
  refine ⟨m,?_⟩
  rw [←map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  change (b:H)^(2^m) ∈ N
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' N ((b:H)^(2^m)) = 1
  simpa only [map_pow] using hm

theorem normalizerPCoreQuotient_inner_pair
    (L J N : Subgroup H) [N.Normal] [(normalizer (L : Set H)).Normal]
    (hLN : L ≤ N) (hjoin : L ⊔ J = N)
    (hcomm : J ≤ centralizer (L : Set H))
    (hq : IsPGroup 2 (H ⧸ N)) (hcore : pCore 2 H ≤ N)
    (hc : center (L ⧸ pCore 2 L) = ⊥)
    (x : H) (hx : L.conjBy x = J) (hxi : L.conjBy x⁻¹ = J)
    (b : normalizer (L : Set H))
    (hb₁ : normalizerPCoreQuotientAction L b ∈ MulAut.innerSubgroup (L ⧸ pCore 2 L))
    (hb₂ : normalizerPCoreQuotientAction L (MulAut.conjNormal x b) ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L)) : (b:H) ∈ N := by
  let B := normalizer (L : Set H)
  let a₁ : L →* B := inclusion L.le_normalizer
  let a₂ : L →* B := (MulAut.conjNormal x⁻¹).toMonoidHom.comp a₁
  let q := QuotientGroup.mk' (pCore 2 L)
  let ρ₁ := normalizerPCoreQuotientAction L
  let ρ₂ := ρ₁.comp (MulAut.conjNormal x).toMonoidHom
  have ha₁ : ∀ l, a₁ l ∈ N.subgroupOf B := fun l => hLN l.property
  have ha₂ : ∀ l, a₂ l ∈ N.subgroupOf B := by
    intro l
    exact (inferInstance : N.Normal).conj_mem (l:H) (hLN l.property) x⁻¹
  have hdecomp : ∀ z : N.subgroupOf B, ∃ l₁ l₂, (z:B) = a₁ l₁ * a₂ l₂ := by
    intro z
    have hz : ((z:B):H) ∈ L ⊔ J := hjoin.symm ▸ z.property
    rw [←SetLike.mem_coe, coe_mul_of_right_le_normalizer_left L J
      (hcomm.trans (Subgroup.centralizer_le_normalizer _))] at hz
    obtain ⟨l,hl,j,hj,he⟩ := hz
    have hj' : j ∈ L.conjBy x⁻¹ := hxi.symm ▸ hj
    obtain ⟨v,hv,hv'⟩ := hj'
    refine ⟨⟨l,hl⟩,⟨v,hv⟩,?_⟩
    apply Subtype.ext
    change ((z:B):H) = l * ((MulAut.conjNormal x⁻¹ (a₁ ⟨v,hv⟩)):H)
    rw [MulAut.conjNormal_apply,inv_inv]
    rw [←he,←hv']
    change l*(x⁻¹*v*(x⁻¹)⁻¹) = l*(x⁻¹*v*x)
    rw [inv_inv]
  have hcross₁ (l : L) : (a₂ l:H) ∈ centralizer (L : Set H) := by
    apply hcomm
    rw [←hxi]
    exact mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom l.property
  have hcross₂ (l : L) : ((MulAut.conjNormal x (a₁ l)):H) ∈
      centralizer (L : Set H) := by
    apply hcomm
    rw [←hx]
    exact mem_map_of_mem (MulAut.conj x).toMonoidHom l.property
  have hcm : ∀ l₁ l₂, Commute (a₁ l₁) (a₂ l₂) := by
    intro l₁ l₂
    apply Subtype.ext
    exact hcross₁ l₂ (l₁:H) l₁.property
  have hi₁ : ∀ l, ρ₁ (a₁ l) = MulAut.conj (q l) := normalizerPCoreQuotientAction_inner L
  have hi₂ : ∀ l, ρ₂ (a₂ l) = MulAut.conj (q l) := by
    intro l
    change ρ₁ (MulAut.conjNormal x (MulAut.conjNormal x⁻¹ (a₁ l))) = _
    have he : MulAut.conjNormal x (MulAut.conjNormal x⁻¹ (a₁ l)) = a₁ l := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply,inv_inv,mul_assoc,mul_inv_cancel_left,
        mul_inv_cancel,mul_one]
    rw [he]
    exact hi₁ l
  have hz₁ : ∀ l, ρ₁ (a₂ l) = 1 := fun l => normalizerPCoreQuotientAction_centralizer L _ (hcross₁ l)
  have hz₂ : ∀ l, ρ₂ (a₁ l) = 1 := fun l => normalizerPCoreQuotientAction_centralizer L _ (hcross₂ l)
  have hp : IsPGroup 2 q.ker := by
    dsimp only [q]
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hcoreB : pCore 2 B ≤ N.subgroupOf B := by
    rw [pCore_eq_comap_of_normal]
    exact comap_mono hcore
  exact Theory.GroupTheory.mem_of_paired_inner_actions (N.subgroupOf B)
    (quotient_pGroup_restrict N B hq) a₁ a₂ hdecomp hcm q q hp hp hc hc
    ρ₁ ρ₂ hi₁ hi₂ hz₁ hz₂ ha₁ ha₂ (QuotientGroup.mk'_surjective _)
    (QuotientGroup.mk'_surjective _) hcoreB b hb₁ hb₂

theorem normalizerPCoreQuotient_outer_kernel
    (L J N : Subgroup H) (hjoin : L ⊔ J = N)
    (hcomm : J ≤ centralizer (L : Set H))
    (hNB : N ≤ normalizer (L : Set H)) :
    N.subgroupOf (normalizer (L : Set H)) ≤
      ((QuotientGroup.mk' (MulAut.innerSubgroup (L ⧸ pCore 2 L))).comp
        (normalizerPCoreQuotientAction L)).ker := by
  let B := normalizer (L : Set H)
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup (L ⧸ pCore 2 L))).comp
    (normalizerPCoreQuotientAction L)
  have hL : L ≤ f.ker.map B.subtype := by
    intro l hl
    refine ⟨inclusion L.le_normalizer ⟨l,hl⟩,?_,rfl⟩
    change QuotientGroup.mk' _ (normalizerPCoreQuotientAction L _) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [normalizerPCoreQuotientAction_inner]
    exact ⟨QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩,rfl⟩
  have hJ : J ≤ f.ker.map B.subtype := by
    intro j hj
    have hjB : j ∈ B := hNB ((le_sup_right.trans_eq hjoin) hj)
    refine ⟨⟨j,hjB⟩,?_,rfl⟩
    change QuotientGroup.mk' _ (normalizerPCoreQuotientAction L _) = 1
    rw [normalizerPCoreQuotientAction_centralizer L _ (hcomm hj),map_one]
  intro z hz
  have hz' : (z:H) ∈ f.ker.map B.subtype := (hjoin ▸ sup_le hL hJ) hz
  obtain ⟨y,hy,he⟩ := hz'
  exact (Subtype.ext he : y=z) ▸ hy



end Subgroup

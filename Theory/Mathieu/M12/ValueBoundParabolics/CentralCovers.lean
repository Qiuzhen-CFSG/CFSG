module

public import Theory.Mathieu.M12.ValueBoundParabolics.CentralCovers.PrimeReduction
public import Theory.Mathieu.M12.ValueBoundParabolics.CentralCovers.Rigidity

/-!
# Centerless M₁₂ covers with trivial two-core

For a finite perfect group Q with Q/Z(Q) isomorphic to the concrete M₁₂, cyclic
Sylow transfer and the triviality of O₂(Q) first make Z(Q) a three-group.
Pull back the marked Sylow three-subgroup and lift its inverting normalizer
element. The local central-extension calculation shows that its derived
subgroup misses Z(Q). Transfer from Q to this local group's abelianization
then kills Z(Q), since the index is prime to three.

This proves the central-cover input needed for Aschbacher–Smith E.4.3(1),
printed pp.241–242 (PDF pp.252–253). It establishes the needed consequence of
the M₁₂ multiplier datum in GLS3 §6.1 directly, without assuming the table or
constructing the double cover. The local model is the actual subgroup from
`M12.Properties.Sylow3`, with the normalizer action of GLS3 Table 5.3b.
-/

public section

open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.CentralCovers
universe u

/-- A finite perfect central cover of M₁₂ with trivial two-core is centerless. -/
theorem center_eq_bot_of_twoCore_eq_bot
    {Q : Type u} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (hcore : pCore 2 Q = ⊥) (e : (Q ⧸ center Q) ≃* M12) :
    center Q = ⊥ := by
  let f : Q →* M12 := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center Q := by
    ext x
    change e (QuotientGroup.mk' (center Q) x) = 1 ↔ x ∈ center Q
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hk3 : IsPGroup 3 f.ker := by
    rw [hk]
    exact center_isThreeGroup hcore e
  let S := m12Sylow3Subgroup
  let H := S.comap f
  let g0 : H →* S :=
    { toFun := fun x => ⟨f x, x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f (x : Q) (y : Q)) }
  have hg0 : Function.Surjective g0 := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨⟨x, by change f x ∈ S; rw [hx]; exact y.property⟩, Subtype.ext hx⟩
  let eS := m12Sylow3Subgroup_mulEquiv_heisenberg
  let g := eS.toMonoidHom.comp g0
  have hgker : g.ker = f.ker.comap H.subtype := by
    ext x
    change eS (g0 x) = 1 ↔ f x = 1
    rw [← eS.map_one, eS.injective.eq_iff]
    exact Subtype.ext_iff
  have hgcenter : g.ker ≤ center H := by
    intro x hx
    have hxc : (x : Q) ∈ center Q := hk ▸ (show (x : Q) ∈ f.ker from by
      simpa only [hgker, mem_comap, Subgroup.subtype_apply] using hx)
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hxc y))
  have hg3 : IsPGroup 3 g.ker := by
    rw [hgker]
    exact hk3.comap_of_injective H.subtype H.subtype_injective
  obtain ⟨t, ht⟩ := hf sylowThreeInverter
  have htn : t ∈ normalizer (H : Set Q) := by
    apply mem_normalizer_iff.mpr
    intro x
    change f x ∈ S ↔ f (t * x * t⁻¹) ∈ S
    simpa only [map_mul, map_inv, ht] using
      (mem_normalizer_iff.mp sylowThreeInverter_mem_normalizer (f x))
  let α : MulAut H := H.normalizerMonoidHom ⟨t, htn⟩
  have hα (x : H) : (α x : Q) = t * x * t⁻¹ := rfl
  have hfix : ∀ z ∈ g.ker, α z = z := by
    intro z hz
    apply Subtype.ext
    rw [hα]
    have hzc : (z : Q) ∈ center Q := hk ▸ (show (z : Q) ∈ f.ker from by
      simpa only [hgker, mem_comap, Subgroup.subtype_apply] using hz)
    rw [mem_center_iff.mp hzc t, mul_inv_cancel_right]
  have hcompat : ∀ x, g (α x) = heisenbergInversion (g x) := by
    intro x
    apply eS.symm.injective
    change eS.symm (eS (g0 (α x))) = _
    rw [eS.symm_apply_apply]
    apply Subtype.ext
    change f (α x) = (eS.symm (heisenbergInversion (g x)) : M12)
    rw [hα, map_mul, map_mul, map_inv, ht]
    have hid (a : M12Heisenberg) : (eS.symm a : M12) = m12HeisenbergHom a :=
      heisenbergEquiv_symm_apply a
    rw [hid]
    have hx : m12HeisenbergHom (g x) = f x := by
      rw [← hid]
      exact congrArg Subtype.val (eS.symm_apply_apply (g0 x))
    rw [← hx, sylowThreeInverter_conj]
  have hrigid := kernel_inf_commutator_eq_bot g (eS.surjective.comp hg0) hgcenter hg3 α hfix hcompat
  have hindex : ¬ 3 ∣ H.index := by
    rw [show H.index = S.index from S.index_comap_of_surjective hf]
    exact m12Sylow3.not_dvd_index
  apply le_bot_iff.mp
  intro z hz
  have hzf : f z = 1 := by
    have hzk : z ∈ f.ker := by simpa only [hk] using hz
    exact hzk
  let zH : H := ⟨z, by change f z ∈ S; rw [hzf]; exact S.one_mem⟩
  let ab : H →* Abelianization H := Abelianization.of
  let tau : Q →* Abelianization H := MonoidHom.transfer ab
  have htau : tau z = 1 := Abelianization.commutator_subset_ker tau
    (Group.IsPerfect.mem_commutator (g := z))
  have hkey : ∀ (k : ℕ) (q : Q), q⁻¹ * z ^ k * q ∈ H → q⁻¹ * z ^ k * q = z ^ k := by
    intro k q _
    rw [mul_assoc, (mem_center_iff.mp ((center Q).pow_mem hz k) q).symm,
      inv_mul_cancel_left]
  have hp : ab (zH ^ H.index) = 1 := by
    have hformula := MonoidHom.transfer_eq_pow ab z hkey
    exact hformula.symm.trans htau
  have hpowD : zH ^ H.index ∈ commutator H := by
    change zH ^ H.index ∈ Abelianization.of.ker at hp
    rwa [Abelianization.ker_of] at hp
  have hpowK : zH ^ H.index ∈ g.ker := by
    rw [hgker]
    change f (z ^ H.index) = 1
    rw [map_pow, hzf, one_pow]
  have hone : z ^ H.index = 1 := by
    have hh : zH ^ H.index ∈ g.ker ⊓ commutator H := ⟨hpowK, hpowD⟩
    rw [hrigid, mem_bot] at hh
    exact congrArg Subtype.val hh
  have hz3 := center_isThreeGroup hcore e
  apply mem_bot.mpr
  have hzC : (⟨z,hz⟩ : center Q) ^ H.index = 1 := Subtype.ext hone
  have hz1 : (⟨z,hz⟩ : center Q) = 1 := by
    apply (hz3.powEquiv' hindex).injective
    simpa only [IsPGroup.powEquiv_apply, one_pow] using hzC
  exact congrArg Subtype.val hz1

/-- A quasisimple group with M₁₂ central quotient and trivial two-core has
trivial center. No multiplier bound is assumed. -/
theorem center_eq_bot {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hcore : pCore 2 Q = ⊥) (e : (Q ⧸ center Q) ≃* M12) : center Q = ⊥ :=
  center_eq_bot_of_twoCore_eq_bot hcore e

end Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.CentralCovers

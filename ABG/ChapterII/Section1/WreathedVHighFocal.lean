module
public import ABG.ChapterII.Section1.WreathedVNormalizerRestriction
public import ABG.ChapterII.Section1.FocalGenerators
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut

/-!
# The high central-product normalizer focal contribution

For a chosen wreathed presentation of a Sylow two-subgroup, if the canonical
central product has outer automizer index six, its local normalizer fusion
subgroup is exactly the quaternion core inside the Sylow subgroup. This is
the local focal calculation in ABG Chapter II Section 1 Proposition 2,
article p.13, `refs/latex/alperin-brauer-gorenstein-pages/page-014.tex`.
The outer denominator remains the product with the ambient centralizer.

The proved restriction theorem says that the normalizer preserves the core
and fixes the Sylow center pointwise. Write a local fusion element as `q*c`,
where `q` belongs to the core and `c` is central. Its conjugate is `q'*c`,
so cancellation puts the fusion difference in the core. Conversely the
normalizer realizes all automorphisms of the core. The two explicit
quaternion automorphism differences give its standard generators; quaternion
normal forms then place every core element in the local fusion subgroup.
All maps use the actual Sylow inclusion and quaternion-factor equivalence.
-/

namespace ABG.Wreathed
variable {G : Type*} [Group G] (S : Sylow 2 G) {n : ℕ}
    (P : Presentation S n)

/-- Outer index six makes the local central-product fusion differences generate precisely its core. -/
public theorem v_normalizerFusionSubgroup_eq [Finite G]
    (hindex : outerAutomizerIndex (P.V.map (S : Subgroup G).subtype) = 6) :
    normalizerFusionSubgroup (S : Subgroup G) (P.V.map (S : Subgroup G).subtype) =
      P.quaternionCore := by
  obtain ⟨hNQ,hNC,_⟩ := canonical_v_normalizer_structure S P
  have hsurj := canonical_v_restriction_surjective S P hindex
  let V := P.V.map (S : Subgroup G).subtype
  let Q := P.quaternionCore.map (S : Subgroup G).subtype
  let F := normalizerFusionSubgroup (S : Subgroup G) V
  have hQS : Q ≤ S := Subgroup.map_subtype_le _
  have hQV : Q ≤ V := Subgroup.map_mono (show P.quaternionCore ≤ P.V from le_sup_left)
  let j := Subgroup.inclusion hQS
  apply le_antisymm
  · rw [normalizerFusionSubgroup, Subgroup.closure_le]
    rintro z ⟨x,y,g,hg,hx,hxy,rfl⟩
    have hxV : x ∈ P.V := by
      obtain ⟨v,hv,he⟩ := hx
      exact (show v = x from Subtype.ext he) ▸ hv
    obtain ⟨q,hq,c,hc,hqc⟩ := Subgroup.mem_sup_of_normal_right.mp hxV
    have hqmap : (q : G) ∈ Q := ⟨q,hq,rfl⟩
    have hconjq : g⁻¹ * (q : G) * g ∈ Q :=
      (Subgroup.mem_normalizer_iff''.mp (hNQ hg) (q : G)).mp hqmap
    obtain ⟨q', hq', heq⟩ := hconjq
    change (q' : G) = g⁻¹ * (q : G) * g at heq
    have hgc : (c : G) * g = g * (c : G) := hNC hg c ⟨c,hc,rfl⟩
    have hy : y = q' * c := by
      apply Subtype.ext
      rw [← hxy, ← hqc]
      change g⁻¹ * ((q : G) * (c : G)) * g = (q' : G) * (c : G)
      rw [heq]
      calc
        _ = g⁻¹ * (q : G) * ((c : G) * g) := by group
        _ = _ := by rw [hgc]; group
    rw [← hqc, hy]
    have hcc : (q⁻¹ * q') * c = c * (q⁻¹ * q') :=
      Subgroup.mem_center_iff.mp hc (q⁻¹ * q')
    have he : (q * c)⁻¹ * (q' * c) = q⁻¹ * q' := by
      calc
        _ = c⁻¹ * ((q⁻¹ * q') * c) := by group
        _ = _ := by rw [hcc]; simp
    rw [he]
    exact P.quaternionCore.mul_mem (P.quaternionCore.inv_mem hq) hq'
  · obtain ⟨e₀⟩ := P.quaternion_core_model.1
    let eQ : Q ≃* QuaternionGroup 2 :=
      (P.quaternionCore.equivMapOfInjective (S : Subgroup G).subtype
        (S : Subgroup G).subtype_injective).symm.trans e₀
    have hd (a : MulAut (QuaternionGroup 2)) (z : QuaternionGroup 2) :
        j (eQ.symm (z⁻¹ * a z)) ∈ F := by
      let b := MulAut.congr eQ.symm a
      obtain ⟨g,hg,hgact⟩ := hsurj b
      have hmem : j ((eQ.symm z)⁻¹ * b (eQ.symm z)) ∈ F := by
        apply Subgroup.subset_closure
        refine ⟨j (eQ.symm z), j (b (eQ.symm z)), g⁻¹,
          (Subgroup.normalizer (V : Set G)).inv_mem hg,
          hQV (eQ.symm z).property, ?_, ?_⟩
        · simpa only [j, inv_inv, Subgroup.coe_inclusion] using hgact (eQ.symm z)
        · simp only [map_mul, map_inv]
      simpa only [b, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
        MulEquiv.apply_symm_apply, map_mul, map_inv] using hmem
    obtain ⟨a,b,x,y,hx,hy⟩ := QuaternionGroup.aut_difference_generators_two
    have ha : j (eQ.symm (QuaternionGroup.a 1)) ∈ F := by rw [← hx]; exact hd a x
    have hb : j (eQ.symm (QuaternionGroup.xa 0)) ∈ F := by rw [← hy]; exact hd b y
    have hgen : ∀ q : QuaternionGroup 2, j (eQ.symm q) ∈ F := by
      intro q
      cases q with
      | a i =>
        have ht := F.pow_mem ha i.val
        rw [← map_pow, ← map_pow, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val] at ht
        exact ht
      | xa i =>
        have ht := F.mul_mem hb (F.pow_mem ha i.val)
        rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, QuaternionGroup.a_one_pow,
          ZMod.natCast_zmod_val, QuaternionGroup.xa_mul_a, zero_add] at ht
        exact ht
    intro z hz
    let q : Q := ⟨z, ⟨z,hz,rfl⟩⟩
    have hq : j q ∈ F := by simpa only [MulEquiv.symm_apply_apply] using hgen (eQ q)
    exact hq

end ABG.Wreathed

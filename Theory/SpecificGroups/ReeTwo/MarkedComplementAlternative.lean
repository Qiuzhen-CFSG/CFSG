module

public import Theory.SpecificGroups.ReeTwo.CyclicExtensionStandardAlternative
public import Theory.SpecificGroups.ReeTwo.NativeComplementRecognition
public import Theory.SpecificGroups.ReeTwo.CoreFiveActionNormalization

/-!
# Marked endpoint recognition or the intrinsic first-core obstruction

The cyclic-extension alternative either supplies the standard split action,
which can be corrected inside the actual endpoint and recognized, or fixes
the actual last-root mark in the intrinsic first core of the specified
subgroup. Normalizing the five-action preserves the middle and last roots,
so the same alternative applies without a prescribed five-action coordinate.
-/

public noncomputable section
namespace ReeTwo.Centralizer
open Subgroup

/-- The native five-action yields recognition of the whole endpoint or the
fixed marked first-core obstruction in the actual specified subgroup. -/
theorem equiv_or_firstCore_obstruction_of_native_five
    {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 20480) (S : Subgroup H) (hS : Nat.card S = 4096)
    (j : Core →* H) (hj : Function.Injective j) (hjS : j.range ≤ S)
    (c s : H) (hc5 : c ^ 5 = 1) (hs : s ∈ S)
    (hsc : s * c * s⁻¹ = c ^ 2)
    (hfour : s ^ 4 = 1 ∨ s ^ 4 = j (Core.root 9))
    (hgen : j.range ⊔ zpowers s = S)
    (f : H →* MulAut Core)
    (hact : ∀ h q, j (f h q) = h * j q * h⁻¹)
    (hfc : f c = Core.c) :
    Nonempty (Centralizer ≃* H) ∨
      (Nat.card (InvertingExtension.firstCore S) = 2048 ∧
        ∃ hz : (⟨j (Core.root 9),hjS ⟨Core.root 9,rfl⟩⟩ : S) ∈
          InvertingExtension.firstCore S,
          ∀ a : MulAut (InvertingExtension.firstCore S),
            a ⟨⟨j (Core.root 9),hjS ⟨Core.root 9,rfl⟩⟩,hz⟩ =
              ⟨⟨j (Core.root 9),hjS ⟨Core.root 9,rfl⟩⟩,hz⟩) := by
  let jS : Core →* S := j.codRestrict S (fun q => hjS ⟨q,rfl⟩)
  let sS : S := ⟨s,hs⟩
  have hgenS : jS.range ⊔ zpowers sS = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup,MonoidHom.map_range,MonoidHom.map_zpowers,
      ←MonoidHom.range_eq_map,range_subtype]
    change j.range ⊔ zpowers s = S
    exact hgen
  have hbeta : f s * Core.c * (f s)⁻¹ = Core.c ^ 2 := by
    rw [←hfc,←map_inv,←map_mul,←map_mul,←map_pow,hsc]
  have hconj (q : Core) : sS * jS q * sS⁻¹ = jS (f s q) :=
    Subtype.ext (hact s q).symm
  have hfourS : sS ^ 4 = 1 ∨ sS ^ 4 = jS (Core.root 9) := by
    rcases hfour with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  rcases CyclicExtension.standard_or_firstCore_obstruction hS jS sS (f s)
      hgenS hbeta hconj hfourS with ⟨hs4, i, hi, hfi⟩ | hbad
  · left
    have hs4H : s ^ 4 = 1 := congrArg Subtype.val hs4
    let t := j (Core.root 2)
    have ht4 : t ^ 4 = 1 := by
      dsimp [t]
      rw [←map_pow]
      exact (congrArg j (show Core.root 2 ^ 4 = 1 from by decide +kernel)).trans j.map_one
    have ht : f t = MulAut.conj (Core.root 2) := by
      apply MulEquiv.ext
      intro q
      apply hj
      rw [hact]
      change j (Core.root 2) * j q * (j (Core.root 2))⁻¹ =
        j (Core.root 2 * q * (Core.root 2)⁻¹)
      simp only [map_mul,map_inv]
    have hct : Commute c t := by
      apply mul_inv_eq_iff_eq_mul.mp
      have hh := (hact c (Core.root 2)).symm
      rw [hfc,show Core.c (Core.root 2) = Core.root 2 from by decide +kernel] at hh
      exact hh
    have hst : Commute s t := by
      apply mul_inv_eq_iff_eq_mul.mp
      have hh := (hact s (Core.root 2)).symm
      rw [hfi,Core.FixingActionCensus.representative_root_two] at hh
      exact hh
    obtain ⟨b,hb4,hbc,hfb⟩ := Core.FixingActionCensus.exists_standard_actor
      f c s t hs4H ht4 hsc hct hst hfc ht i hi hfi
    obtain ⟨e,_⟩ := exists_equiv_of_native_actions hH j c b hc5 hb4 hbc
      (fun q => by rw [←hfc]; exact hact c q)
      (fun q => by rw [←hfb]; exact hact b q)
      (fun hz => (by decide +kernel : Core.root 9 ≠ 1) (hj (hz.trans j.map_one.symm)))
    exact ⟨e⟩
  · exact Or.inr hbad

/-- An order-five action fixing the middle root can be normalized without
changing the actual last-root mark. The resulting complete endpoint is native,
or the specified subgroup has a first core of order 2048 fixing that mark. -/
theorem equiv_or_firstCore_obstruction
    {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 20480) (S : Subgroup H) (hS : Nat.card S = 4096)
    (j : Core →* H) (hj : Function.Injective j) (hjS : j.range ≤ S)
    (c s : H) (hc5 : c ^ 5 = 1) (hs : s ∈ S)
    (hsc : s * c * s⁻¹ = c ^ 2)
    (hfour : s ^ 4 = 1 ∨ s ^ 4 = j (Core.root 9))
    (hgen : j.range ⊔ zpowers s = S)
    (f : H →* MulAut Core)
    (hact : ∀ h q, j (f h q) = h * j q * h⁻¹)
    (hfc : orderOf (f c) = 5) (hroot : f c (Core.root 2) = Core.root 2) :
    Nonempty (Centralizer ≃* H) ∨
      (Nat.card (InvertingExtension.firstCore S) = 2048 ∧
        ∃ hz : (⟨j (Core.root 9),hjS ⟨Core.root 9,rfl⟩⟩ : S) ∈
          InvertingExtension.firstCore S,
          ∀ a : MulAut (InvertingExtension.firstCore S),
            a ⟨⟨j (Core.root 9),hjS ⟨Core.root 9,rfl⟩⟩,hz⟩ =
              ⟨⟨j (Core.root 9),hjS ⟨Core.root 9,rfl⟩⟩,hz⟩) := by
  obtain ⟨d,_,hd9,hd⟩ := Core.exists_marked_conjugator_of_orderOf_eq_five (f c) hfc hroot
  let j' : Core →* H := j.comp d.symm.toMonoidHom
  let f' : H →* MulAut Core := (MulAut.conj d).toMonoidHom.comp f
  have hj' : Function.Injective j' := hj.comp d.symm.injective
  have hsame : j'.range = j.range := by
    apply le_antisymm
    · rintro _ ⟨q,rfl⟩
      exact ⟨d.symm q,rfl⟩
    · rintro _ ⟨q,rfl⟩
      exact ⟨d q,by change j (d.symm (d q)) = j q; rw [d.symm_apply_apply]⟩
  have hj'S : j'.range ≤ S := hsame ▸ hjS
  have hmark : j' (Core.root 9) = j (Core.root 9) := by
    change j (d.symm (Core.root 9)) = j (Core.root 9)
    rw [←hd9,d.symm_apply_apply,hd9]
  have hact' (h : H) (q : Core) : j' (f' h q) = h * j' q * h⁻¹ := by
    change j (d.symm (d (f h (d.symm q)))) = h * j (d.symm q) * h⁻¹
    rw [d.symm_apply_apply]
    exact hact h (d.symm q)
  have hfc' : f' c = Core.c := hd
  have hfour' : s ^ 4 = 1 ∨ s ^ 4 = j' (Core.root 9) := by rwa [hmark]
  have hgen' : j'.range ⊔ zpowers s = S := by rwa [hsame]
  rcases equiv_or_firstCore_obstruction_of_native_five hH S hS j' hj' hj'S
      c s hc5 hs hsc hfour' hgen' f' hact' hfc' with hmodel | ⟨hsize,hfix⟩
  · exact Or.inl hmodel
  · right
    refine ⟨hsize,?_⟩
    have he : (⟨j' (Core.root 9),hj'S ⟨Core.root 9,rfl⟩⟩ : S) =
        ⟨j (Core.root 9),hjS ⟨Core.root 9,rfl⟩⟩ := Subtype.ext hmark
    simpa only [he] using hfix

end ReeTwo.Centralizer

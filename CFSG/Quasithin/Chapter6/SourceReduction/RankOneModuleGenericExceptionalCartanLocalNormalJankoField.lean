module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNormalJanko
public import Theory.SpecificGroups.SL2.SylowNormalizerTorusAction
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.GroupTheory.NormalizerQuotientInner

/-!
# The original right cubic in the normal J₁ row acts on the left field

The original normal-container calculation supplies an order-seven subgroup
of the left Cartan moved by the original right cubic. An inner automorphism
preserving a Sylow and its odd complement fixes the complement: the literal
Sylow-normalizer quotient is abelian, and its two-kernel misses the complement.
Thus the right cubic has a nontrivial field image. Its prime order makes the
actual quotient-conjugation field homomorphism faithful, with image order three.
Both quotient maps, the full original Sylow, and both Hall conditions are retained.

This supplies the field-action step of the normal J₁ row. Omega movement and
its faithful-module exclusion are separate obligations of the original sieve.
Source: Aschbacher--Smith 5.1.13, printed p.637, refs/quasithin.pdf.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

private theorem inner_sylow_actor_fixes_odd
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (P : Sylow 2 G)
    (hk : q.ker ≤ (P : Subgroup G)) (A : Subgroup G)
    (hAP : A ≤ normalizer (P : Set G)) (ho : Odd (Nat.card A))
    (α : MulAut G) (g : SL(2,F))
    (he : ∀ x, q (α x) = g*q x*g⁻¹)
    (hP : (P : Subgroup G).map α.toMonoidHom = P)
    (hA : ∀ x ∈ A, α x ∈ A) : ∀ x ∈ A, α x = x := by
  obtain ⟨f,_,_,hfk,_⟩ := Matrix.SpecialLinearGroup.exists_sylowNormalizer_torus_action
    q hq P hk (MulEquiv.refl G) (MulEquiv.refl SL(2,F)) (fun _ => rfl) (by simp)
  obtain ⟨l,hl⟩ := hq g
  have hroot : ((P : Subgroup G).map q).comap q = P := comap_map_eq_self hk
  have hg : g ∈ normalizer (((P : Subgroup G).map q) : Set SL(2,F)) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh : (MulAut.conj g).toMonoidHom.comp q = q.comp α.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact (he x).symm
    change ((P : Subgroup G).map q).map (MulAut.conj g).toMonoidHom = _
    rw [Subgroup.map_map,hh,←Subgroup.map_map,hP]
  have hlN : l ∈ normalizer (P : Set G) := by
    have hh : l ∈ (normalizer (((P : Subgroup G).map q) : Set SL(2,F))).comap q := by
      change q l ∈ normalizer (((P : Subgroup G).map q) : Set SL(2,F))
      rwa [hl]
    rw [comap_normalizer_eq_of_surjective _ hq,hroot] at hh
    exact hh
  have hker : f.ker = (P : Subgroup G).subgroupOf (normalizer (P : Set G)) := by
    ext x
    exact hfk x
  have hd : Disjoint A (P : Subgroup G) := by
    obtain ⟨k,hk⟩ := P.isPGroup'.exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hk]; exact ho.coprime_two_right.pow_right k)
  intro x hx
  let xN : normalizer (P : Set G) := ⟨x,hAP hx⟩
  let yN : normalizer (P : Set G) := ⟨α x,hAP (hA x hx)⟩
  let lN : normalizer (P : Set G) := ⟨l,hlN⟩
  have hdiff : yN * (lN*xN*lN⁻¹)⁻¹ ∈ f.ker := by
    rw [hker]
    apply hk
    change q (α x * (l*x*l⁻¹)⁻¹) = 1
    rw [map_mul,map_inv,map_mul,map_mul,map_inv,he,hl,mul_inv_cancel]
  have hfe : f yN = f xN := by
    have hh : f (yN * (lN*xN*lN⁻¹)⁻¹) = 1 := hdiff
    rw [map_mul,map_inv,mul_inv_eq_one] at hh
    rw [hh,map_mul,map_mul,map_inv]
    simp only [mul_comm (f lN),mul_inv_cancel_right]
  have hxyP : α x*x⁻¹ ∈ P := by
    apply (hfk (yN*xN⁻¹)).mp
    rw [map_mul,map_inv,hfe,mul_inv_cancel]
  have hxy : α x*x⁻¹ = 1 := hd.le_bot ⟨A.mul_mem (hA x hx) (A.inv_mem hx),hxyP⟩
  exact mul_inv_eq_one.mp hxy


/-- The source right cubic acts faithfully on the field of the original
left quotient. The homomorphism is literal quotient conjugation followed
by the standard PSL₂ field projection. -/
theorem normal_janko_cubic_field_action
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) [C.Normal] (hRC : (residual H).subgroupOf Y ≤ C)
    (eC : (C ⧸ pCore 2 C) ≃* Janko1.Model)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* PSL(2,F)) :
    let a := (MulAut.congr e).toMonoidHom.comp
      ((normalizerQuotientAction L (pCore 2 L)).comp
        (inclusion (c.right_le.trans inf_le_left)))
    let f := (Theory.PSL2.fieldProjection F).comp a
    Function.Injective f ∧ Nat.card f.range = 3 := by
  let a := (MulAut.congr e).toMonoidHom.comp
    ((normalizerQuotientAction L (pCore 2 L)).comp
      (inclusion (c.right_le.trans inf_le_left)))
  let f := (Theory.PSL2.fieldProjection F).comp a
  obtain ⟨hB,_,hseven,_,_,hmove⟩ := normal_janko_original_seven h hH hgen c hY hescape C hRC eC
  have hLH : ¬ L ≤ H := by
    intro hh
    exact hescape (inf_le_left.trans ((c.left_le.trans (inf_le_left.trans hh)).trans
      (le_normalizer_residual H)))
  have hBP := c.right_le.trans
    (intersection_normalizes_localSylow h.linear h.sylow_normalizes hH.1.1.2 hLH)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L h.sylow_normalizes
  let eSL := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let q := eSL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := eSL.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker ≤ (P : Subgroup L) := by
    rw [MonoidHom.ker_comp_of_injective _ _ eSL.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have hA : A.subgroupOf L ≤ normalizer (P : Set L) := by
    intro x hx
    change x ∈ normalizer ((P : Subgroup L) : Set L)
    rw [hP]
    have hh : (x : G) ∈ (normalizer ((T : Subgroup G).subgroupOf L : Set L)).map L.subtype := by
      rw [←localBorel_eq_map]
      exact c.left_le hx
    exact (mem_map_iff_mem L.subtype_injective).mp hh
  have ho : Odd (Nat.card (A.subgroupOf L)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (c.left_le.trans inf_le_left)).toEquiv,
      ←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have hnot : f.range ≠ ⊥ := by
    intro hz
    apply hmove
    intro b hb x hx
    have hb0 : f ⟨b,hb⟩ = 1 := by
      have hh : f ⟨b,hb⟩ ∈ f.range := ⟨⟨b,hb⟩,rfl⟩
      rwa [hz,mem_bot] at hh
    have hbinner : a ⟨b,hb⟩ ∈ MulAut.innerSubgroup PSL(2,F) := by
      change a ⟨b,hb⟩ ∈ Theory.PSL2.inner F
      rw [←Theory.PSL2.fieldProjection_ker]
      exact hb0
    obtain ⟨g,hg⟩ := hbinner
    let bN : normalizer (L : Set G) := ⟨b,(c.right_le.trans inf_le_left) hb⟩
    let α := L.normalizerMonoidHom bN
    let β := MulAut.congr eSL (normalizerQuotientAction L (pCore 2 L) bN)
    have he (l : L) : q (α l) = β (q l) := by
      change eSL (QuotientGroup.mk' _ (α l)) =
        eSL (normalizerQuotientAction L (pCore 2 L) bN
          (eSL.symm (eSL (QuotientGroup.mk' _ l))))
      rw [eSL.symm_apply_apply]
      simp only [normalizerQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk]
      rfl
    have hβ : β = MulAut.conj ((Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm g) := by
      have hh := congrArg (MulAut.congr (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm) hg
      rw [MulAut.congr_conj] at hh
      exact hh.symm
    have hPa : (P : Subgroup L).map α.toMonoidHom = P := by
      apply eq_of_le_of_card_ge
      · rw [hP]
        rintro _ ⟨x,hx,rfl⟩
        exact ((mem_normalizer_iff.mp (hBP hb)) (x : G)).mp ⟨hx,x.property⟩ |>.1
      · exact (Nat.card_congr ((P : Subgroup L).equivMapOfInjective
          α.toMonoidHom α.injective).toEquiv).le
    have hAa : ∀ x ∈ A.subgroupOf L, α x ∈ A.subgroupOf L := by
      intro x hx
      exact (mem_normalizer_iff.mp (c.right_normalizes_left hb) (x : G)).mp hx
    have hfix := inner_sylow_actor_fixes_odd q hq P hk (A.subgroupOf L) hA ho α
      ((Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm g)
      (fun x => by rw [he,hβ]; rfl) hPa hAa
    have hxA : x ∈ A := by rw [hseven] at hx; exact hx.1
    have hh := congrArg (fun l : L => (l : G))
      (hfix ⟨x,(c.left_le.trans inf_le_left) hxA⟩ hxA)
    change b*x*b⁻¹=x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hd := card_range_dvd f
  rw [hB] at hd
  have hc : Nat.card f.range = 3 := ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left
    (fun hh => hnot (card_eq_one.mp hh))
  have hi : Function.Injective f := by
    have hi := f.rangeRestrict_surjective.bijective_of_nat_card_le (by rw [hc,hB]) |>.1
    intro x y he
    exact hi (Subtype.ext he)
  exact ⟨hi,hc⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

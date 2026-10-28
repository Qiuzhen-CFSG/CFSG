module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.CommutatorValue
/-!
# The action on Campbell's second replacement

Theorem 6 makes the elementary conjugate span of the inverse actor
commute with the normalized centralizer factor. Maximum order then
forces A to normalize the second replacement. Mixed-word commutation
puts its A-commutator in the mixed actor centralizer.
Source: Campbell II.7.2(ii), printed pp.33–34.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open CampbellTheoremA
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

omit [Finite H] in
private theorem conj_map_mul (X : Subgroup H) (x g : H) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      X.map (MulAut.conj (x*g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply,mul_assoc]

theorem InLocalClass.replacement_normalized
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (g : H) (hgK : g ∈ Campbell.J (⊤ : Subgroup H)) :
    A ≤ normalizer (replacement S a A g : Set H) := by
  let C := inverseConjugate S a g
  let D := firstReplacement S a A ⊓ centralizer (C : Set H)
  let E := conjugateSpanBy C A
  have hb := h.replacement_geometry S hB a hAll A hA g
  have hAD : A ≤ normalizer (D : Set H) := hb.2.2
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  have hAK : A ≤ Campbell.J (⊤ : Subgroup H) :=
    (show A ≤ Campbell.J S from le_sSup hA).trans (hST ▸ elementaryAbelianMaxJ_sylow_le_top T)
  let : IsElementaryAbelian 2 A := hA.2.1
  have hEA := h.two_subgroup_conjugate_span_elementary S hB a.symm (hAll a.symm) A
    (IsElementaryAbelian.isPGroup (p:=2) (G:=A)) hAK g hgK
  let : IsElementaryAbelian 2 E := hEA
  let : IsElementaryAbelian 2 (replacement S a A g) := hb.1.2.1
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (show D ≤ replacement S a A g from le_sup_right)
  have hEC : E ≤ centralizer (D : Set H) := conjugateSpanBy_le
    (le_centralizer_iff.mp (show D ≤ centralizer (C : Set H) from inf_le_right))
    (hAD.trans (normalizer_le_normalizer_centralizer _))
  let : IsElementaryAbelian 2 (E ⊔ D : Subgroup H) := IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hEC)
  have hEQ : E ≤ pCore 2 H := conjugateSpanBy_le (le_sup_left.trans hb.2.1) le_normalizer_of_normal
  have hES : E ⊔ D ≤ S := sup_le (hEQ.trans hQS) (le_sup_right.trans hb.1.1)
  have hBE : replacement S a A g ≤ E ⊔ D := sup_le_sup (le_conjugateSpanBy C A) le_rfl
  have he : replacement S a A g = E ⊔ D := Subgroup.eq_of_le_of_card_ge hBE (hb.1.2.2 _ hES inferInstance)
  rw [he]
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy C A hx),
    mem_normalizer_iff_map_conj_eq.mp (hAD hx)]

theorem InLocalClass.replacement_commutator_centralizes_mixed
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hF : ¬ imageF S a ≤ Campbell.F H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (g : H) (hgK : g ∈ Campbell.J (⊤ : Subgroup H)) (hg2 : g^2=1) :
    ⁅A,replacement S a A g⁆ ≤ replacement S a A g ⊓ centralizer (mixedActor S a g : Set H) := by
  let C := inverseConjugate S a g
  let D := firstReplacement S a A ⊓ centralizer (C : Set H)
  let Y := mixedActor S a g
  have hb := h.replacement_geometry S hB a hAll A hA g
  have hp := h.firstReplacement_geometry S hB a (hAll a) A hA
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  have hAK : A ≤ Campbell.J (⊤ : Subgroup H) :=
    (show A ≤ Campbell.J S from le_sSup hA).trans (hST ▸ elementaryAbelianMaxJ_sylow_le_top T)
  have hgpow : ∃ n, orderOf g=2^n := by
    have ho := orderOf_dvd_of_pow_eq_one hg2
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp ho with ho | ho
    · exact ⟨0,by simpa using ho⟩
    · exact ⟨1,by simpa using ho⟩
  have hYQ : Y ≤ pCore 2 H := by
    rintro x ⟨y,hy,rfl⟩
    exact (inferInstance : (pCore 2 H).Normal).conj_mem y
      (h.inverse_conjugate_core S hB a (hAll a) g hgK hgpow hy) g
  have hYS := hYQ.trans hQS
  have hZZ : fixed S ⊔ automorphismImage S a (fixed S) ≤ centralizer (Y : Set H) :=
    sup_le (inf_le_right.trans (centralizer_le hYS))
      ((h.automorphism_fixed_le_center S hB a (hAll a) hF).trans (center_le_centralizer _))
  have hCY : C ≤ centralizer (Y : Set H) := by
    have hc := h.mixed_inverse_actor_commutes S hB a hAll hF g 1 hgK (one_mem _) hg2 (by simp)
    dsimp only at hc
    change (imageF S a.symm).map (MulAut.conj g).toMonoidHom ≤ centralizer
      ((automorphismImage S a.symm ((imageF S a).map (MulAut.conj g).toMonoidHom)).map (MulAut.conj g).toMonoidHom : Set H)
    simpa only [one_mul,imageF] using le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
  refine le_inf (le_normalizer_iff_commutator_le_right.mp (h.replacement_normalized S hB a hAll A hA g hgK)) ?_
  apply commutator_le.mpr
  intro x hx b hb'
  let : IsElementaryAbelian 2 A := hA.2.1
  have hx2 : x^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx
  have hCxY : C.map (MulAut.conj x).toMonoidHom ≤ centralizer (Y : Set H) := by
    have hc := h.mixed_inverse_actor_commutes S hB a hAll hF g x hgK (hAK hx) hg2 hx2
    dsimp only at hc
    rw [←conj_map_mul] at hc
    change ((imageF S a.symm).map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom ≤ centralizer
      ((automorphismImage S a.symm ((imageF S a).map (MulAut.conj g).toMonoidHom)).map (MulAut.conj g).toMonoidHom : Set H)
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hprod : (replacement S a A g : Set H) = (C : Set H) * (D : Set H) :=
    coe_mul_of_left_le_normalizer_right C D
      ((le_centralizer_iff.mp (show D ≤ centralizer (C : Set H) from inf_le_right)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hmem : b ∈ (C : Set H) * (D : Set H) := by rw [←hprod]; exact hb'
  obtain ⟨c,hc,d,hd,rfl⟩ := hmem
  have hxc : ⁅x,c⁆ ∈ centralizer (Y : Set H) := by
    change x*c*x⁻¹*c⁻¹ ∈ _
    exact (centralizer (Y : Set H)).mul_mem (hCxY (mem_map_of_mem (MulAut.conj x).toMonoidHom hc))
      ((centralizer (Y : Set H)).inv_mem (hCY hc))
  have hxd : ⁅x,d⁆ ∈ centralizer (Y : Set H) := hZZ (hp.2.2.2
    (commutator_mem_commutator hx hd.1))
  have he : ⁅x,c*d⁆ = ⁅x,c⁆*(c*⁅x,d⁆*c⁻¹) := by simp only [commutatorElement_def]; group
  rw [he]
  exact (centralizer (Y : Set H)).mul_mem hxc
    ((centralizer (Y : Set H)).mul_mem ((centralizer (Y : Set H)).mul_mem (hCY hc) hxd)
      ((centralizer (Y : Set H)).inv_mem (hCY hc)))
end CFSG.Quasithin.ChapterC.GlaubermanNiles

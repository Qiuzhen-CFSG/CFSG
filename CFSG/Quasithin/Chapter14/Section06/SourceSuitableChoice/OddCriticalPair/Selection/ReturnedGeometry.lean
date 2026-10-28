module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Transvections
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Selection
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.OriginalF916

/-!
# The returned-line endpoint geometry

The full-denominator endpoint returns a conjugate of the original elementary
module whose commutator is the transported central line. Its nontrivial
quotient action consists of transvections, so the exchanged dihedral factors
force dimension four and p = 3. These transvections preserve both moved
planes. Faithfulness on the moved section makes one plane noncentral; the
original factor exchanger marks the first plane when necessary.

All conjugations are left conjugations. The conjugator, reverse containment
and exclusion from Mc are retained together through this change of marking.
The full source-prefix application is in Selection.FullOrthogonalSource.

Source: Aschbacher--Smith, original 14.6.13, printed p.1031.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open OddNormalizer Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Chapter13.Section08.SourceCompletion Chapter13.Section08.CriticalGeometry
variable {G : Type*} [Group G] [Finite G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

theorem ReturnedLineAction.displacement_rank
    (a : LocalQuotientAction H U Z) (hz : H ≤ centralizer (Z : Set G))
    (hZ : Nat.card Z = 2) (l : ReturnedLineAction H U Z)
    {t : H ⧸ pCore 2 H} (ht : t ∈ actorImage H (U.map (MulAut.conj l.g).toMonoidHom)) :
    Module.finrank (ZMod 2) (LinearMap.range (a.representation t - LinearMap.id)) ≤ 1 := by
  let s := ModuleBound.OriginalF916.conjugationSection a hz
  let A := U.map (MulAut.conj l.g).toMonoidHom
  let C := Z.map (MulAut.conj l.g).toMonoidHom
  have hC : Nat.card C = 2 := by
    rw [show C = Z.map (MulAut.conj l.g).toMonoidHom from rfl,
      card_map_of_injective (MulAut.conj l.g).injective,hZ]
  have hr : LinearMap.range (a.representation t - LinearMap.id) ≤ s.image C := by
    rintro _ ⟨v,rfl⟩
    obtain ⟨u,hu⟩ := s.surjective (Multiplicative.ofAdd v)
    have hv : v ∈ s.image U := ⟨u,u.property,congrArg Multiplicative.toAdd hu⟩
    exact s.displacement_mem U A C (by rw [commutator_comm]; exact l.commutator.le) t ht v hv
  exact (Submodule.finrank_mono hr).trans (by
    simpa only [hC,show Nat.log 2 2 = 1 from by decide] using s.image_finrank_le C)

omit [Finite G] in
theorem support_fixed_of_commutator_le
    (a : LocalQuotientAction H U Z) (hz : H ≤ centralizer (Z : Set G))
    (V : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)))
    (B : Subgroup G) (_hBH : B ≤ H) (hc : ⁅supportPreimage a V,B⁆ ≤ Z) :
    ∀ b ∈ actorImage H B, ∀ v ∈ V, a.representation b v = v := by
  let s := ModuleBound.OriginalF916.conjugationSection a hz
  rintro b ⟨x,hx,rfl⟩ v hv
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) v.toMul
  have he : (s.quotient u).toAdd = v := congrArg Additive.ofMul hu
  have hpre : (u:G) ∈ supportPreimage a V := (mem_supportPreimage a V u).mpr (he ▸ hv)
  rw [← he]
  apply sub_eq_zero.mp
  rw [s.displacement]
  apply (s.quotient_eq_zero_iff _).mpr
  exact commutator_le.mp (by rwa [commutator_comm] : ⁅B,supportPreimage a V⁆ ≤ Z)
    x hx u hpre

theorem ReturnedLineAction.transvection
    (a : LocalQuotientAction H U Z) (hz : H ≤ centralizer (Z : Set G))
    (hZ : Nat.card Z = 2) (l : ReturnedLineAction H U Z) :
    ∃ t ∈ actorImage H (U.map (MulAut.conj l.g).toMonoidHom),
      t ≠ 1 ∧ t ^ 2 = 1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (a.representation t - LinearMap.id)) ≤ 1 := by
  let s := ModuleBound.OriginalF916.conjugationSection a hz
  let A := U.map (MulAut.conj l.g).toMonoidHom
  let C := Z.map (MulAut.conj l.g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hC : Nat.card C = 2 := by
    rw [show C = Z.map (MulAut.conj l.g).toMonoidHom from rfl,
      card_map_of_injective (MulAut.conj l.g).injective,hZ]
  have hne : ¬ ⁅U,A⁆ ≤ Z := by
    rw [l.commutator]
    intro hle
    have hbot : C = ⊥ := le_bot_iff.mp ((le_inf hle le_rfl).trans l.disjoint.le)
    have hc1 : Nat.card C = 1 := hbot ▸ Subgroup.card_bot
    omega
  have hfix : A ≤ centralizer (C : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mul_comm (⟨y,map_mono a.kernel_le hy⟩ : A) ⟨x,hx⟩)
  have hq := ModuleBound.OriginalF916.quadratic_member_of_common_line s l.in_H hC
    l.commutator.le hfix hne
  have hB : actorImage H A ≠ ⊥ := hq.1.1
  obtain ⟨t,ht,htne⟩ : ∃ t ∈ actorImage H A, t ≠ 1 := by
    by_contra hh
    push Not at hh
    exact hB (eq_bot_iff.mpr (fun x hx => Subgroup.mem_bot.mpr (hh x hx)))
  let : IsElementaryAbelian 2 (actorImage H A) := starImage_isElementaryAbelian H A l.in_H
  refine ⟨t,ht,htne,elemPow_eq_one_of_isElementaryAbelian t ht,?_⟩
  exact l.displacement_rank a hz hZ ht

theorem returned_line_four
    (a : LocalQuotientAction H U Z) (hz : H ≤ centralizer (Z : Set G))
    (hZ : Nat.card Z = 2) (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    (l : ReturnedLineAction H U Z) :
    p = 3 ∧ Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 4 := by
  obtain ⟨t,_,hne,h2,hr⟩ := l.transvection a hz hZ
  exact exchanged_moved_four_of_transvection a T hTH p H0 H1 H2 d hne h2 hr

theorem ReturnedLineAction.supports
    (a : LocalQuotientAction H U Z) (hz : H ≤ centralizer (Z : Set G))
    (hZ : Nat.card Z = 2) (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    (l : ReturnedLineAction H U Z)
    (hf : ∀ g : H ⧸ pCore 2 H,
      (∀ v ∈ subspaceCommutator a.representation ⊤ ⊤, a.representation g v = v) → g = 1) :
    (U.map (MulAut.conj l.g).toMonoidHom ≤ normalizer (firstSupport a H1 : Set G)) ∧
    (U.map (MulAut.conj l.g).toMonoidHom ≤ normalizer (firstSupport a H2 : Set G)) ∧
    (¬ ⁅firstSupport a H1,U.map (MulAut.conj l.g).toMonoidHom⁆ ≤ Z ∨
     ¬ ⁅firstSupport a H2,U.map (MulAut.conj l.g).toMonoidHom⁆ ≤ Z) := by
  classical
  let B := U.map (MulAut.conj l.g).toMonoidHom
  have hnorm : ∀ i ∈ ({H1,H2} : Set (Subgroup G)), B ≤ normalizer (firstSupport a i : Set G) := by
    intro i hi
    apply supportPreimage_normalized a _ B l.in_H
    intro t ht
    have hs := exchanged_transvection_preserves_planes a T hTH p H0 H1 H2 d
      (l.displacement_rank a hz hZ ht)
    rcases hi with rfl | rfl
    · exact (subspace_map_eq_iff _ _ _).mp hs.1
    · exact (subspace_map_eq_iff _ _ _).mp hs.2
  refine ⟨hnorm H1 (by simp),hnorm H2 (by simp),?_⟩
  by_cases h1 : ⁅firstSupport a H1,B⁆ ≤ Z
  · right
    intro h2
    obtain ⟨t,ht,hne,_,_⟩ := l.transvection a hz hZ
    apply hne
    apply hf t
    intro v hv
    have hv' : v ∈ subspaceCommutator a.representation ⊤ (actorImage H H1) ⊔
        subspaceCommutator a.representation ⊤ (actorImage H H2) := d.split.symm ▸ hv
    obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv'
    rw [map_add, support_fixed_of_commutator_le a hz _ B l.in_H h1 t ht x hx,
      support_fixed_of_commutator_le a hz _ B l.in_H h2 t ht y hy]
  · exact Or.inl h1

omit [Finite G] in
noncomputable def ReturnedLineAction.conjugate
    (a : LocalQuotientAction H U Z) (hz : H ≤ centralizer (Z : Set G))
    (l : ReturnedLineAction H U Z) (x : H) : ReturnedLineAction H U Z := by
  have hU : U.map (MulAut.conj (x:G)).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (a.normalizes x.property)
  have hH : H.map (MulAut.conj (x:G)).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer x.property)
  have hZ : Z.map (MulAut.conj (x:G)).toMonoidHom = Z :=
    mem_normalizer_iff_map_conj_eq.mp ((hz.trans (Subgroup.centralizer_le_normalizer _)) x.property)
  have hc (K : Subgroup G) : (K.map (MulAut.conj l.g).toMonoidHom).map
      (MulAut.conj (x:G)).toMonoidHom = K.map (MulAut.conj ((x:G)*l.g)).toMonoidHom :=
    (conjBy_mul K (x:G) l.g).symm
  refine ⟨(x:G)*l.g,?_,?_,?_,?_⟩
  · have h := map_mono (f := (MulAut.conj (x:G)).toMonoidHom) l.in_H
    rwa [hc U,hH] at h
  · have h := map_mono (f := (MulAut.conj (x:G)).toMonoidHom) l.reverse
    rwa [hU,hc H] at h
  · have h := congrArg (fun K : Subgroup G => K.map (MulAut.conj (x:G)).toMonoidHom) l.commutator
    rwa [map_commutator,hU,hc U,hc Z] at h
  · have h := congrArg (fun K : Subgroup G => K.map (MulAut.conj (x:G)).toMonoidHom) l.disjoint
    rwa [map_inf _ _ _ (MulAut.conj (x:G)).injective,hZ,hc Z,Subgroup.map_bot] at h

theorem returned_line_four_geometry
    (a : LocalQuotientAction H U Z) (hz : H ≤ centralizer (Z : Set G))
    (hZ : Nat.card Z = 2) (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    (Mc : Subgroup G) (hHMc : H ≤ Mc)
    (l : ReturnedLineAction H U Z) (hout : l.g ∉ Mc)
    (hf : ∀ g : H ⧸ pCore 2 H,
      (∀ v ∈ subspaceCommutator a.representation ⊤ ⊤, a.representation g v = v) → g = 1) :
    p = 3 ∧ Nonempty (FourCriticalGeometry a Mc H1) := by
  obtain ⟨hp,hdim⟩ := returned_line_four a hz hZ T hTH p H0 H1 H2 d l
  obtain ⟨hN1,hN2,hc | hc⟩ := l.supports a hz hZ T hTH p H0 H1 H2 d hf
  · exact ⟨hp,⟨⟨hdim,l.g,hout,le_inf l.in_H hN1,l.reverse,hc⟩⟩⟩
  · obtain ⟨x,hx,hxN,hex⟩ := d.exchanged
    let xH : H := ⟨x,hTH hx⟩
    let l' := l.conjugate a hz xH
    have hout' : l'.g ∉ Mc := by
      intro hh
      change x*l.g ∈ Mc at hh
      have h := Mc.mul_mem (Mc.inv_mem (hHMc xH.property)) hh
      exact hout (by simpa only [show (xH:G) = x from rfl,inv_mul_cancel_left] using h)
    have hnorm := (l'.supports a hz hZ T hTH p H0 H1 H2 d hf).1
    have heS : (firstSupport a H2).map (MulAut.conj x).toMonoidHom = firstSupport a H1 := by
      unfold firstSupport
      rw [supportPreimage_conjugate a _ xH,moved_map_conjugate,
        ← actorImage_conjugate H2 (d.second_le.trans d.zero_le) xH,
        exchange_factor_inverse x hex]
    have heB : (U.map (MulAut.conj l.g).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        U.map (MulAut.conj l'.g).toMonoidHom := (conjBy_mul U x l.g).symm
    have heZ : Z.map (MulAut.conj x).toMonoidHom = Z :=
      mem_normalizer_iff_map_conj_eq.mp ((hz.trans (Subgroup.centralizer_le_normalizer _)) xH.property)
    have hc' : ¬ ⁅firstSupport a H1,U.map (MulAut.conj l'.g).toMonoidHom⁆ ≤ Z := by
      intro hh
      apply hc
      apply (map_le_map_iff_of_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective).mp
      rw [map_commutator,heS,heB,heZ]
      exact hh
    exact ⟨hp,⟨⟨hdim,l'.g,hout',le_inf l'.in_H hnorm,l'.reverse,hc'⟩⟩⟩

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection

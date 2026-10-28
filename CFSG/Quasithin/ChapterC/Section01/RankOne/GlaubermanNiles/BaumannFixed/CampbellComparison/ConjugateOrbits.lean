module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellComparison.ReplacementGeometry
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.ConjugateSpanCentralizer


/-!
# Campbell II.5.3: elementary spans of paired conjugates

The maximum elementary replacement and its commutator alternative remain
valid after any ambient conjugation inside the first two-core. For a
maximum elementary A, the relative centralizer in the paired replacement
is A-invariant. If F′ᵍ and F′ˣᵍ failed to commute, their two maximum
replacements would identify Z′ᵍ with Z′ˣᵍ. The literal maximal/Borel
separation then excludes x outside the core; elements inside the core
already normalize F′ᵍ. Thus all A-conjugates commute and their span is
elementary abelian.

The final theorem constructs the actual maximal subgroup from the original
local hypotheses and the noncentral branch, rather than requiring a new
normalizer or model premise. Source: Campbell, *Pushing up in Finite Groups*
(1979), II.5.3, printed p.28; Aschbacher–Smith C.1.17–18, printed p.126.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {J H H' : Type*} [Group J] [Group H] [Finite H] [Group H'] [Finite H']
  {B' : Type*} [Group B'] [Finite B'] {e' : B' →* H'}
  {F' : Type} [Field F'] [Finite F'] [CharP F' 2]

omit [Finite H] in
private theorem equiv_roundtrip (c : H ≃* H) (A : Subgroup H) :
    (A.map c.symm.toMonoidHom).map c.toMonoidHom = A := by
  rw [Subgroup.map_map]
  have hc : c.toMonoidHom.comp c.symm.toMonoidHom = MonoidHom.id H := by
    ext x
    exact c.apply_symm_apply x
  rw [hc,Subgroup.map_id]

omit [Finite H] in
private theorem equiv_inf_centralizer (c : H ≃* H) (A X : Subgroup H) :
    (A ⊓ centralizer (X : Set H)).map c.toMonoidHom =
      A.map c.toMonoidHom ⊓ centralizer (X.map c.toMonoidHom : Set H) := by
  apply le_antisymm
  · exact le_inf (map_mono inf_le_left)
      ((map_mono inf_le_right).trans (map_centralizer_le_centralizer_image _ _))
  · rintro y ⟨⟨a,ha,rfl⟩,hc⟩
    refine ⟨a,⟨ha,?_⟩,rfl⟩
    intro x hx
    apply c.injective
    have hh := hc (c x) (mem_map_of_mem c.toMonoidHom hx)
    change c x * c a = c a * c x at hh
    simpa only [map_mul] using hh

private theorem max_core_equiv (S : Sylow 2 H) (c : H ≃* H)
    (hc : (pCore 2 H).map c.toMonoidHom = pCore 2 H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (S : Subgroup H))
    (hAQ : A ≤ pCore 2 H) :
    A.map c.toMonoidHom ∈ elementaryAbelianMaxSubgroups (S : Subgroup H) := by
  apply (maxFamily_sylow_iff S _).mpr
  refine ⟨(map_mono hAQ).trans (hc.le.trans (pCore_isPGroup.le_sylow_of_normal S)),?_⟩
  have hh := (maxFamily_map_injective_iff c.toMonoidHom c.injective ⊤ A).mpr
    ((maxFamily_sylow_iff S A).mp hA).2
  rwa [map_top_of_surjective _ c.surjective] at hh

theorem InLocalClass.paired_conjugate_replacement (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hYQ : d.transfer d' (Campbell.F H') ≤ pCore 2 H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H))
    (hAQ : A ≤ pCore 2 H) (g : H) :
    (d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom ⊔
      (A ⊓ centralizer ((d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom : Set H)) ∈
      elementaryAbelianMaxSubgroups (d.sylow : Subgroup H) := by
  let c : H ≃* H := MulAut.conj g
  have hc : (pCore 2 H).map c.toMonoidHom = pCore 2 H :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  have hci : (pCore 2 H).map c.symm.toMonoidHom = pCore 2 H :=
    calc
      _ = ((pCore 2 H).map c.toMonoidHom).map c.symm.toMonoidHom := congrArg (Subgroup.map c.symm.toMonoidHom) hc.symm
      _ = _ := equiv_roundtrip c.symm _
  have hAi := max_core_equiv d.sylow c.symm hci A hA hAQ
  have hh := h'.paired_campbellF_replacement hB' m' d d' _ hAi
  have hhQ : d.transfer d' (Campbell.F H') ⊔
      (A.map c.symm.toMonoidHom ⊓ centralizer (d.transfer d' (Campbell.F H') : Set H)) ≤ pCore 2 H :=
    sup_le hYQ (inf_le_left.trans ((map_mono hAQ).trans hci.le))
  have hout := max_core_equiv d.sylow c hc _ hh hhQ
  rw [Subgroup.map_sup,equiv_inf_centralizer,equiv_roundtrip] at hout
  exact hout

theorem InLocalClass.paired_conjugate_commutator_dichotomy (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS' : (d'.sylow : Subgroup H') = e'.range)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H))
    (hAQ : A ≤ pCore 2 H) (g : H) :
    ⁅A,(d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∨
      ⁅A,(d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom⁆ =
        (d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H'))).map (MulAut.conj g).toMonoidHom := by
  let c : H ≃* H := MulAut.conj g
  have hc : (pCore 2 H).map c.toMonoidHom = pCore 2 H :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  have hci : (pCore 2 H).map c.symm.toMonoidHom = pCore 2 H :=
    calc
      _ = ((pCore 2 H).map c.toMonoidHom).map c.symm.toMonoidHom := congrArg (Subgroup.map c.symm.toMonoidHom) hc.symm
      _ = _ := equiv_roundtrip c.symm _
  have hAi := max_core_equiv d.sylow c.symm hci A hA hAQ
  rcases h'.paired_campbellF_commutator_dichotomy hB' m' d d' hS' _ hAi with hb | hz
  · have hh := congrArg (Subgroup.map c.toMonoidHom) hb
    rw [map_commutator,equiv_roundtrip,Subgroup.map_bot] at hh
    exact Or.inl hh
  · have hh := congrArg (Subgroup.map c.toMonoidHom) hz
    rw [map_commutator,equiv_roundtrip] at hh
    exact Or.inr hh


omit [Finite H] in
private theorem conj_map_mul (Y : Subgroup H) (x g : H) :
    (Y.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      Y.map (MulAut.conj (x*g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply,mul_assoc]

variable {B : Type*} [Group B] [Finite B] {e : B →* H}
  {F : Type} [Field F] [Finite F] [CharP F 2]

theorem InLocalClass.paired_conjugates_commute (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS : (d.sylow : Subgroup H) = e.range) (hS' : (d'.sylow : Subgroup H') = e'.range)
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H))
    (M : Subgroup H) (hM : (d.sylow : Subgroup H) ≤ M ∧ M ⋖ ⊤)
    (hNZ : normalizer (d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) : Set H) ≤ M)
    (g : H) (hg : g ∉ M) (x : H) (hx : x ∈ A) :
    ⁅(d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom,
      (d.transfer d' (Campbell.F H')).map (MulAut.conj (x*g)).toMonoidHom⁆ = ⊥ := by
  let Y := d.transfer d' (Campbell.F H')
  let Z := d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H'))
  let Yg := Y.map (MulAut.conj g).toMonoidHom
  let Yx := Y.map (MulAut.conj (x*g)).toMonoidHom
  have hYg := h.paired_conjugates_in_core_thompson hB m h' hB' m' d d' hV g
  have hYx := h.paired_conjugates_in_core_thompson hB m h' hB' m' d d' hV (x*g)
  have hYQ := h.transferred_campbellF_le_core hB m h' hB' m' d d' hV
  have hRQ : Campbell.J (pCore 2 H) ≤ pCore 2 H := sSup_le fun _ hA => hA.1
  by_cases hxQ : x ∈ pCore 2 H
  · have hxR : x ∈ Campbell.J (pCore 2 H) :=
      h.submaximal_core_le_thompson hB d (A ⊓ pCore 2 H) A hA inf_le_left inf_le_right ⟨hx,hxQ⟩
    have he : Yx = Yg := (conj_map_mul Y x g).symm.trans
      (mem_normalizer_iff_map_conj_eq.mp (hYg.2 hxR))
    change ⁅Yg,Yx⁆ = ⊥
    rw [he]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    obtain ⟨A',hA',hFA'⟩ := h'.campbellF_le_some_maxElementary hB' d'
    let : IsElementaryAbelian 2 (d.transfer d' A') := (d.transfer_maxElementary d' A' hA').2.1
    have hYA' : Y ≤ d.transfer d' A' := map_mono (comap_mono hFA')
    let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le hYA'
    let : IsElementaryAbelian 2 Yg := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  · by_contra hnon
    let A₀ := (A ⊓ pCore 2 H) ⊔ Campbell.F H
    let A₁ := Y ⊔ (A₀ ⊓ centralizer (Y : Set H))
    let C := A₁ ⊓ centralizer (Yg : Set H)
    let W := Yg ⊔ C
    let Wx := Yx ⊔ C
    have hd := h.paired_replacement_geometry hB m h' hB' m' d d' hS' hV A hA
    have hCN : A ≤ normalizer (C : Set H) := hd.2.2.2.2.2 g
    have hW := InLocalClass.paired_conjugate_replacement h' hB' m' d d' hYQ A₁ hd.2.1 hd.2.2.1 g
    have hWQ : W ≤ pCore 2 H := sup_le (hYg.1.trans hRQ) (inf_le_left.trans hd.2.2.1)
    have hCeq : C.map (MulAut.conj x).toMonoidHom = C := mem_normalizer_iff_map_conj_eq.mp (hCN hx)
    have hWxmap : W.map (MulAut.conj x).toMonoidHom = Wx := by
      change (Yg ⊔ C).map _ = Yx ⊔ C
      rw [Subgroup.map_sup,hCeq]
      exact congrArg (fun U => U ⊔ C) (conj_map_mul Y x g)
    have hQx : (pCore 2 H).map (MulAut.conj x).toMonoidHom = pCore 2 H :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top x))
    have hWx : Wx ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H) :=
      hWxmap ▸ max_core_equiv d.sylow (MulAut.conj x) hQx W hW hWQ
    have hWxQ : Wx ≤ pCore 2 H := sup_le (hYx.1.trans hRQ) (inf_le_left.trans hd.2.2.1)
    have hCYx : C ≤ centralizer (Yx : Set H) := by
      let : IsElementaryAbelian 2 Wx := hWx.2.1
      exact (le_sup_right : C ≤ Wx).trans
        ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le (show Yx ≤ Wx from le_sup_left)))
    have hcomm1 : ⁅Yg,Yx⁆ = ⁅Wx,Yg⁆ := by
      rw [commutator_comm Wx]
      exact commutator_eq_of_centralizing_sup (sup_comm C Yx) inf_le_right (hYx.1.trans hYg.2)
    have hcomm2 : ⁅Yg,Yx⁆ = ⁅W,Yx⁆ := by
      rw [commutator_comm Yg Yx,commutator_comm W]
      exact commutator_eq_of_centralizing_sup (sup_comm C Yg) hCYx (hYg.1.trans hYx.2)
    have he1 : ⁅Wx,Yg⁆ = Z.map (MulAut.conj g).toMonoidHom := by
      rcases InLocalClass.paired_conjugate_commutator_dichotomy h' hB' m' d d' hS' Wx hWx hWxQ g with hb | hz
      · exact False.elim (hnon (hcomm1.trans hb))
      · exact hz
    have he2 : ⁅W,Yx⁆ = Z.map (MulAut.conj (x*g)).toMonoidHom := by
      rcases InLocalClass.paired_conjugate_commutator_dichotomy h' hB' m' d d' hS' W hW hWQ (x*g) with hb | hz
      · exact False.elim (hnon (hcomm2.trans hb))
      · exact hz
    have hZZ : Z.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj (x*g)).toMonoidHom :=
      he1.symm.trans (hcomm1.symm.trans (hcomm2.trans he2))
    have hxNZ : x ∈ normalizer (Z.map (MulAut.conj g).toMonoidHom : Set H) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      exact (conj_map_mul Z x g).trans hZZ.symm
    have hxmap : x ∈ (normalizer (Z : Set H)).map (MulAut.conj g).toMonoidHom := by
      rw [map_equiv_normalizer_eq]
      exact hxNZ
    obtain ⟨y,hy,hey⟩ := hxmap
    have hconj : g⁻¹*x*g ∈ M := by
      have he : g⁻¹*x*g=y := by rw [←hey]; simp [MulAut.conj_apply,mul_assoc]
      rw [he]
      exact hNZ hy
    have hginv : g⁻¹ ∉ M := by intro hh; exact hg (by simpa using M.inv_mem hh)
    exact h.campbell_maximal_separation hB m d hS M hM g⁻¹ x hginv (hA.1 hx) hxQ
      (by simpa using hconj)


omit [Finite H] [Finite H'] in
theorem Campbell.Embedding.transferred_fixed_centralizes_thompson (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H') :
    d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) ≤
      centralizer (Campbell.J (d.sylow : Subgroup H) : Set H) := by
  rintro z ⟨a,ha,rfl⟩ t ht
  obtain ⟨b,rfl⟩ := (d.range_eq.symm ▸ ht : t ∈ d.marking.range)
  have hbs : d'.marking b ∈ d'.sylow := by
    have hj : d'.marking b ∈ Campbell.J (d'.sylow : Subgroup H') :=
      d'.range_eq ▸ (show d'.marking b ∈ d'.marking.range from ⟨b,rfl⟩)
    exact (show Campbell.J (d'.sylow : Subgroup H') ≤ (d'.sylow : Subgroup H') from
      sSup_le fun _ hA => hA.1) hj
  have hh := ha.2 _ hbs
  have hba : b*a=a*b := d'.injective (by simpa only [map_mul] using hh)
  rw [←map_mul,hba,map_mul]

theorem InLocalClass.paired_conjugate_span_elementary (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS : (d.sylow : Subgroup H) = e.range) (hS' : (d'.sylow : Subgroup H') = e'.range)
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H))
    (M : Subgroup H) (hM : (d.sylow : Subgroup H) ≤ M ∧ M ⋖ ⊤)
    (hNZ : normalizer (d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) : Set H) ≤ M)
    (g : H) (hg : g ∉ M) :
    IsElementaryAbelian 2 (conjugateSpanBy
      ((d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom) A) := by
  let Y := d.transfer d' (Campbell.F H')
  let Yg := Y.map (MulAut.conj g).toMonoidHom
  obtain ⟨A',hA',hFA'⟩ := h'.campbellF_le_some_maxElementary hB' d'
  let : IsElementaryAbelian 2 (d.transfer d' A') := (d.transfer_maxElementary d' A' hA').2.1
  have hYA' : Y ≤ d.transfer d' A' := map_mono (comap_mono hFA')
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le hYA'
  let : IsElementaryAbelian 2 Yg := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hcomm : IsMulCommutative (conjugateSpanBy Yg A) := by
    apply (conjugateSpanBy_commutative_iff Yg A).mpr
    apply le_centralizer_iff.mpr
    apply (closure_le _).mpr
    rintro y ⟨x,hx,z,hz,rfl⟩
    have hh := InLocalClass.paired_conjugates_commute h hB m h' hB' m' d d' hS hS' hV A hA M hM hNZ g hg x hx
    have hc : Y.map (MulAut.conj (x*g)).toMonoidHom ≤ centralizer (Yg : Set H) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
    apply hc
    rw [←conj_map_mul Y x g]
    exact mem_map_of_mem (MulAut.conj x).toMonoidHom hz
  exact conjugateSpanBy_elementary_of_commutative Yg A

theorem InLocalClass.exists_paired_elementary_geometry (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS : (d.sylow : Subgroup H) = e.range) (hS' : (d'.sylow : Subgroup H') = e'.range)
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H)
    (hn : ¬ d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) ≤
      centralizer (Campbell.J (⊤ : Subgroup H) : Set H)) :
    ∃ M : Subgroup H, (d.sylow : Subgroup H) ≤ M ∧ M ⋖ ⊤ ∧
      normalizer (d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) : Set H) ≤ M ∧
      ∀ A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H), ∀ g ∉ M,
        IsElementaryAbelian 2 (conjugateSpanBy
          ((d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom) A) := by
  obtain ⟨M,hSM,hMt,hbound⟩ := h.exists_campbell_maximal_normalizer_bound hB m d hS
  have hNZ := hbound _ (Campbell.Embedding.transferred_fixed_centralizes_thompson d d') hn
  exact ⟨M,hSM,hMt,hNZ,fun A hA g hg => InLocalClass.paired_conjugate_span_elementary
    h hB m h' hB' m' d d' hS hS' hV A hA M ⟨hSM,hMt⟩ hNZ g hg⟩

end CFSG.Quasithin.ChapterC.GlaubermanNiles

module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.ActorConjugates
/-!
# Natural centralization controls Campbell's full elementary layer

For any subgroup Y of a maximum elementary subgroup, the actual source
F decomposes as V·C_F(Y). Transfer through the common Thompson marking
preserves this equality. Conjugation preserves maximum elementary rank
inside the two-core, so the identity remains valid for every conjugated
paired F and every submaximal Y in that core.

Consequently, centralizing the corresponding V-conjugate forces Y to
centralize the F-conjugate. Two conjugate paired V layers which commute
therefore have commuting F layers: construct actual maximum elementary
replacements in the core and apply the control identity twice.
Source: Campbell II.4.4–4.5 and the final step of II.6.3, printed pp.25–26,31.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {J H H' : Type*} [Group J] [Group H] [Finite H] [Group H'] [Finite H']
  {B B' : Type*} [Group B] [Finite B] [Group B'] [Finite B']
  {e : B →* H} {e' : B' →* H'}
  {F F' : Type} [Field F] [Finite F] [CharP F 2] [Field F'] [Finite F'] [CharP F' 2]

theorem InLocalClass.paired_campbellF_submaximal_split (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (Y A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) (hYA : Y ≤ A) :
    d.transfer d' (Campbell.F H') = d.transfer d' (Campbell.V H') ⊔
      (d.transfer d' (Campbell.F H') ⊓ centralizer (Y : Set H)) := by
  have hAr : A ≤ d.marking.range := by rw [d.range_eq]; exact le_sSup hA
  have hYr : Y ≤ d.marking.range := hYA.trans hAr
  have hFr := (h'.campbell_marked_containments hB' d').1
  have hVr := (h'.campbell_marked_containments hB' d').2.1
  have hYt : d'.transfer d Y ≤ d'.transfer d A := map_mono (comap_mono hYA)
  have hc := (h'.campbellF_submaximal_control hB' m' d' (d'.transfer d Y) (d'.transfer d A)
    (d'.transfer_maxElementary d A hA) hYt).2
  have hh := congrArg (d.transfer d') hc
  rw [Campbell.Embedding.transfer_sup d d' _ _ hVr (inf_le_left.trans hFr),
    Campbell.Embedding.transfer_inf_centralizer d d' _ (d'.transfer d Y) (hYt.trans (map_le_range _ _)),
    Campbell.Embedding.transfer_roundtrip d d' Y hYr] at hh
  exact hh

omit [Finite H] in
private theorem map_roundtrip (c : H ≃* H) (A : Subgroup H) :
    (A.map c.symm.toMonoidHom).map c.toMonoidHom=A := by
  rw [Subgroup.map_map]
  have hc : c.toMonoidHom.comp c.symm.toMonoidHom = MonoidHom.id H := by
    ext x
    exact c.apply_symm_apply x
  rw [hc,Subgroup.map_id]

omit [Finite H] in
private theorem map_inf_centralizer (c : H ≃* H) (A X : Subgroup H) :
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

private theorem max_core_conjugate (S : Sylow 2 H) (g : H) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (S : Subgroup H)) (hAQ : A ≤ pCore 2 H) :
    A.map (MulAut.conj g).toMonoidHom ∈ elementaryAbelianMaxSubgroups (S : Subgroup H) := by
  apply (maxFamily_sylow_iff S _).mpr
  have hQ : (pCore 2 H).map (MulAut.conj g).toMonoidHom = pCore 2 H :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  refine ⟨(map_mono hAQ).trans (hQ.le.trans (pCore_isPGroup.le_sylow_of_normal S)),?_⟩
  have hh := (maxFamily_map_injective_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective ⊤ A).mpr
    ((maxFamily_sylow_iff S A).mp hA).2
  rwa [map_top_of_surjective _ (MulAut.conj g).surjective] at hh

theorem InLocalClass.paired_conjugate_submaximal_split (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (Y A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H))
    (hYA : Y ≤ A) (hAQ : A ≤ pCore 2 H) (g : H) :
    (d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom =
      (d.transfer d' (Campbell.V H')).map (MulAut.conj g).toMonoidHom ⊔
        ((d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom ⊓ centralizer (Y : Set H)) := by
  let c := MulAut.conj g
  have hci : c.symm.toMonoidHom = (MulAut.conj g⁻¹).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change g⁻¹*x*g=g⁻¹*x*(g⁻¹)⁻¹
    rw [inv_inv]
  have hAm := max_core_conjugate d.sylow g⁻¹ A hA hAQ
  have hc := h'.paired_campbellF_submaximal_split hB' m' d d' (Y.map c.symm.toMonoidHom)
    (A.map c.symm.toMonoidHom) (by rwa [hci]) (map_mono hYA)
  have hh := congrArg (Subgroup.map c.toMonoidHom) hc
  rw [Subgroup.map_sup,map_inf_centralizer,map_roundtrip] at hh
  exact hh

theorem InLocalClass.paired_conjugate_centralizes_of_natural (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (Y A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H))
    (hYA : Y ≤ A) (hAQ : A ≤ pCore 2 H) (g : H)
    (hc : Y ≤ centralizer ((d.transfer d' (Campbell.V H')).map (MulAut.conj g).toMonoidHom : Set H)) :
    Y ≤ centralizer ((d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom : Set H) := by
  apply le_centralizer_iff.mpr
  rw [h'.paired_conjugate_submaximal_split hB' m' d d' Y A hA hYA hAQ g]
  exact sup_le (le_centralizer_iff.mp hc) inf_le_right

theorem InLocalClass.paired_conjugates_commute_of_natural (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H) (g k : H)
    (hc : ⁅(d.transfer d' (Campbell.V H')).map (MulAut.conj g).toMonoidHom,
      (d.transfer d' (Campbell.V H')).map (MulAut.conj k).toMonoidHom⁆=⊥) :
    ⁅(d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom,
      (d.transfer d' (Campbell.F H')).map (MulAut.conj k).toMonoidHom⁆=⊥ := by
  have hYQ := h.transferred_campbellF_le_core hB m h' hB' m' d d' hV
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty (d.sylow : Subgroup H)
  let A0 := (A ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H)
  have hA0 := h.omegaCore_replacement_maximal hB d A hA
  have hA0Q : A0 ≤ pCore 2 H := sup_le inf_le_right (fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).1)
  have hE (x:H) := h'.paired_conjugate_replacement hB' m' d d' hYQ A0 hA0 hA0Q x
  have hXQ (x:H) : (d.transfer d' (Campbell.F H')).map (MulAut.conj x).toMonoidHom ≤ pCore 2 H := by
    rintro z ⟨y,hy,rfl⟩
    exact (inferInstance : (pCore 2 H).Normal).conj_mem y (hYQ hy) x
  have hEQ (x:H) : (d.transfer d' (Campbell.F H')).map (MulAut.conj x).toMonoidHom ⊔
      (A0 ⊓ centralizer ((d.transfer d' (Campbell.F H')).map (MulAut.conj x).toMonoidHom : Set H)) ≤ pCore 2 H :=
    sup_le (hXQ x) (inf_le_left.trans hA0Q)
  have hVF (x:H) : (d.transfer d' (Campbell.V H')).map (MulAut.conj x).toMonoidHom ≤
      (d.transfer d' (Campbell.F H')).map (MulAut.conj x).toMonoidHom :=
    map_mono (map_mono (comap_mono Campbell.V_le_F))
  have hVgFk := h'.paired_conjugate_centralizes_of_natural hB' m' d d' _ _ (hE g)
    ((hVF g).trans le_sup_left) (hEQ g) k (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hFkFg := h'.paired_conjugate_centralizes_of_natural hB' m' d d' _ _ (hE k)
    le_sup_left (hEQ k) g (le_centralizer_iff.mp hVgFk)
  exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hFkFg)
end CFSG.Quasithin.ChapterC.GlaubermanNiles

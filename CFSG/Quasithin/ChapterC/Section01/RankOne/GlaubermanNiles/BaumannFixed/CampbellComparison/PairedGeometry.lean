module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellComparison.CorePlacement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.OmegaStructure.FixedPoints


/-!
# Paired replacement geometry on the common Thompson subgroup

The literal common markings preserve commutators, joins and relative
centralizers. The source replacement F C_A(F) is therefore a maximum
elementary subgroup in either marked Sylow group. A maximum subgroup's
commutator with the transferred F is either trivial or the transferred
fixed subgroup C_V(S).

When the transferred V lies in the first two-core, the transferred F and
all its conjugates lie in J(O₂(H)) and are normalized by that group.
The transferred F also centralizes the first F. These are the exact
paired subgroup and replacement inputs to Campbell II.5.2–5.4, preserving
both embeddings throughout.
Source: Campbell, *Pushing up in Finite Groups* (1979), II.4.4–5.3,
printed pp.26–28; Aschbacher–Smith C.1.17–18, printed p.126.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {J H H' : Type*} [Group J] [Group H] [Group H']

theorem Campbell.Embedding.thompson_normalizes_transfer (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (X : Subgroup H') [X.Normal] :
    Campbell.J (d.sylow : Subgroup H) ≤ normalizer (d.transfer d' X : Set H) := by
  let : (d'.pull X).Normal := inferInstanceAs (X.comap d'.marking).Normal
  have hh := (d'.pull X).le_normalizer_map d.marking
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,d.range_eq] at hh
  exact hh


theorem Campbell.Embedding.transfer_roundtrip (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (X : Subgroup H) (hX : X ≤ d.marking.range) : d.transfer d' (d'.transfer d X) = X := by
  unfold Campbell.Embedding.transfer Campbell.Embedding.pull
  rw [comap_map_eq_self_of_injective d'.injective]
  exact d.map_pull X hX

theorem Campbell.Embedding.transfer_commutator (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (X Y : Subgroup H') (hX : X ≤ d'.marking.range) (hY : Y ≤ d'.marking.range) :
    d.transfer d' ⁅X,Y⁆ = ⁅d.transfer d' X,d.transfer d' Y⁆ := by
  have he : (⁅X,Y⁆).comap d'.marking = ⁅X.comap d'.marking,Y.comap d'.marking⁆ := by
    apply map_injective d'.injective
    rw [map_comap_eq,inf_eq_right.mpr ((Subgroup.commutator_le_sup X Y).trans (sup_le hX hY)),map_commutator,
      map_comap_eq,map_comap_eq,inf_eq_right.mpr hX,inf_eq_right.mpr hY]
  unfold Campbell.Embedding.transfer Campbell.Embedding.pull
  rw [he,map_commutator]


theorem Campbell.Embedding.transfer_sup (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (X Y : Subgroup H') (hX : X ≤ d'.marking.range) (hY : Y ≤ d'.marking.range) :
    d.transfer d' (X ⊔ Y) = d.transfer d' X ⊔ d.transfer d' Y := by
  unfold Campbell.Embedding.transfer Campbell.Embedding.pull
  rw [←comap_sup_eq_of_le_range d'.marking hX hY,Subgroup.map_sup]

theorem Campbell.Embedding.transfer_inf_centralizer (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (A X : Subgroup H') (hX : X ≤ d'.marking.range) :
    d.transfer d' (A ⊓ centralizer (X : Set H')) =
      d.transfer d' A ⊓ centralizer (d.transfer d' X : Set H) := by
  apply le_antisymm
  · apply le_inf (map_mono (comap_mono inf_le_left))
    apply d.transfer_le_centralizer d' _ _ (map_le_range _ _)
    change A ⊓ centralizer (X : Set H') ≤ centralizer (d'.transfer d (d.transfer d' X) : Set H')
    rw [Campbell.Embedding.transfer_roundtrip d' d X hX]
    exact inf_le_right
  · rintro x ⟨⟨a,ha,rfl⟩,hc⟩
    refine ⟨a,⟨ha,?_⟩,rfl⟩
    intro y hy
    obtain ⟨b,rfl⟩ := hX hy
    have hh := hc (d.marking b) ⟨b,hy,rfl⟩
    have hab : b*a=a*b := d.injective (by simpa only [map_mul] using hh)
    rw [←map_mul,hab,map_mul]


theorem Campbell.core_thompson_normal : (Campbell.J (pCore 2 H)).Normal := by
  rw [normal_iff_map_conj_eq]
  intro g
  change (elementaryAbelianMaxJ (pCore 2 H)).map (MulAut.conj g).toMonoidHom = _
  rw [←elementaryAbelianMaxJ_map_equiv]
  have hQ : (pCore 2 H).map (MulAut.conj g).toMonoidHom = pCore 2 H :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  rw [hQ]
  rfl

variable [Finite H] [Finite H']
  {B B' : Type*} [Group B] [Finite B] [Group B'] [Finite B']
  {e : B →* H} {e' : B' →* H'}
  {F F' : Type} [Field F] [Finite F] [CharP F 2] [Field F'] [Finite F'] [CharP F' 2]

theorem InLocalClass.paired_core_geometry (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H) :
    d.transfer d' (Campbell.F H') ≤ pCore 2 H ∧
      d.transfer d' (Campbell.F H') ≤ centralizer (Campbell.F H : Set H) ∧
      Campbell.J (d.sylow : Subgroup H) ≤ normalizer (d.transfer d' (Campbell.F H') : Set H) ∧
      ∀ g : H, Campbell.J (pCore 2 H) ≤ normalizer
        ((d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom : Set H) := by
  let Y := d.transfer d' (Campbell.F H')
  have hYQ : Y ≤ pCore 2 H := h.transferred_campbellF_le_core hB m h' hB' m' d d' hV
  obtain ⟨A,hA,hFA⟩ := h'.campbellF_le_some_maxElementary hB' d'
  have hYA : Y ≤ d.transfer d' A := map_mono (comap_mono hFA)
  have hYC := (h.campbellF_submaximal_control hB m d Y _ (d.transfer_maxElementary d' A hA) hYA).1
  rw [inf_eq_left.mpr hYQ] at hYC
  let : (Campbell.F H').Normal := Campbell.F_normal
  have hJY := Campbell.Embedding.thompson_normalizes_transfer d d' (Campbell.F H')
  refine ⟨hYQ,hYC,hJY,?_⟩
  intro g
  have hRJ : Campbell.J (pCore 2 H) ≤ Campbell.J (d.sylow : Subgroup H) :=
    sSup_le fun A hA => le_sSup (d.core_maxFamily_subset_of_fixedIndex (h.omegaFixedIndexBound hB d) hA)
  have hRN : Campbell.J (pCore 2 H) ≤ normalizer (Y : Set H) := hRJ.trans hJY
  have hRm : (Campbell.J (pCore 2 H)).map (MulAut.conj g).toMonoidHom = Campbell.J (pCore 2 H) := by
    change (elementaryAbelianMaxJ (pCore 2 H)).map (MulAut.conj g).toMonoidHom = _
    rw [←elementaryAbelianMaxJ_map_equiv]
    have hQ : (pCore 2 H).map (MulAut.conj g).toMonoidHom = pCore 2 H :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
    rw [hQ]
    rfl
  calc
    _ = (Campbell.J (pCore 2 H)).map (MulAut.conj g).toMonoidHom := hRm.symm
    _ ≤ (normalizer (Y : Set H)).map (MulAut.conj g).toMonoidHom := map_mono hRN
    _ = _ := map_equiv_normalizer_eq Y (MulAut.conj g)



theorem InLocalClass.submaximal_core_le_thompson (h : InLocalClass e) (hB : IsBaumannFixed B)
    (d : Campbell.Embedding J H) (Y A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H))
    (hYA : Y ≤ A) (hYQ : Y ≤ pCore 2 H) : Y ≤ Campbell.J (pCore 2 H) := by
  have hr := h.omegaCore_replacement_maximal hB d A hA
  have hrQ : (A ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H) ≤ pCore 2 H :=
    sup_le inf_le_right (fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).1)
  have hrmax : (A ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H) ∈
      elementaryAbelianMaxSubgroups (pCore 2 H) :=
    ⟨hrQ,hr.2.1,fun C hC he => hr.2.2 C (hC.trans (pCore_isPGroup.le_sylow_of_normal d.sylow)) he⟩
  exact (le_inf hYA hYQ).trans (le_sup_left.trans (le_sSup hrmax))

theorem InLocalClass.paired_conjugates_in_core_thompson (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H) (g : H) :
    (d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom ≤ Campbell.J (pCore 2 H) ∧
      Campbell.J (pCore 2 H) ≤ normalizer
        ((d.transfer d' (Campbell.F H')).map (MulAut.conj g).toMonoidHom : Set H) := by
  have hc := InLocalClass.paired_core_geometry h hB m h' hB' m' d d' hV
  obtain ⟨A,hA,hFA⟩ := h'.campbellF_le_some_maxElementary hB' d'
  have hYJ := InLocalClass.submaximal_core_le_thompson h hB d _ _
    (d.transfer_maxElementary d' A hA) (map_mono (comap_mono hFA)) hc.1
  have hn : (Campbell.J (pCore 2 H)).Normal := Campbell.core_thompson_normal
  have hm : (Campbell.J (pCore 2 H)).map (MulAut.conj g).toMonoidHom = Campbell.J (pCore 2 H) :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  exact ⟨hm ▸ map_mono hYJ,hc.2.2.2 g⟩

theorem InLocalClass.campbellF_centralizer_replacement (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (d : Campbell.Embedding J H) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) :
    Campbell.F H ⊔ (A ⊓ centralizer (Campbell.F H : Set H)) ∈
      elementaryAbelianMaxSubgroups (d.sylow : Subgroup H) := by
  rw [h.maxElementary_centralizer_campbellF hB m d A hA,sup_comm,
    h.campbellF_replacement_eq_omegaCore hB d A hA]
  exact h.omegaCore_replacement_maximal hB d A hA

theorem InLocalClass.paired_campbellF_replacement (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) :
    d.transfer d' (Campbell.F H') ⊔ (A ⊓ centralizer (d.transfer d' (Campbell.F H') : Set H)) ∈
      elementaryAbelianMaxSubgroups (d.sylow : Subgroup H) := by
  have hAr : A ≤ d.marking.range := by rw [d.range_eq]; exact le_sSup hA
  have hFr := (h'.campbell_marked_containments hB' d').1
  have hAt : d'.transfer d A ≤ d'.marking.range := map_le_range _ _
  have hh := d.transfer_maxElementary d' _
    (InLocalClass.campbellF_centralizer_replacement h' hB' m' d' _ (d'.transfer_maxElementary d A hA))
  rw [Campbell.Embedding.transfer_sup d d' _ _ hFr (inf_le_left.trans hAt),
    Campbell.Embedding.transfer_inf_centralizer d d' _ _ hFr,Campbell.Embedding.transfer_roundtrip d d' A hAr] at hh
  exact hh

theorem InLocalClass.campbellF_commutator_dichotomy (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (d : Campbell.Embedding J H)
    (hS : (d.sylow : Subgroup H) = e.range) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) :
    ⁅A,Campbell.F H⁆ = ⊥ ∨ ⁅A,Campbell.F H⁆ = Campbell.V H ⊓ centralizer (d.sylow : Set H) := by
  by_cases hAQ : A ≤ pCore 2 H
  · left
    apply commutator_eq_bot_iff_le_centralizer.mpr
    have he := h.maxElementary_centralizer_campbellF hB m d A hA
    rw [inf_eq_left.mpr hAQ] at he
    exact he.ge.trans inf_le_right
  · exact Or.inr (h.campbell_fixed_commutator_identities hB m d hS A hA hAQ).1

theorem InLocalClass.paired_campbellF_commutator_dichotomy (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS' : (d'.sylow : Subgroup H') = e'.range) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) :
    ⁅A,d.transfer d' (Campbell.F H')⁆ = ⊥ ∨
      ⁅A,d.transfer d' (Campbell.F H')⁆ = d.transfer d'
        (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) := by
  have hAr : A ≤ d.marking.range := by rw [d.range_eq]; exact le_sSup hA
  have hAt : d'.transfer d A ≤ d'.marking.range := map_le_range _ _
  have hFr := (h'.campbell_marked_containments hB' d').1
  have ht := Campbell.Embedding.transfer_commutator d d' (d'.transfer d A) (Campbell.F H') hAt hFr
  rw [Campbell.Embedding.transfer_roundtrip d d' A hAr] at ht
  rcases InLocalClass.campbellF_commutator_dichotomy h' hB' m' d' hS' _ (d'.transfer_maxElementary d A hA) with hb | hz
  · left
    rw [←ht,hb]
    unfold Campbell.Embedding.transfer Campbell.Embedding.pull
    change d'.marking.ker.map d.marking = ⊥
    rw [d'.marking.ker_eq_bot d'.injective,Subgroup.map_bot]
  · exact Or.inr (ht.symm.trans (congrArg (d.transfer d') hz))

end CFSG.Quasithin.ChapterC.GlaubermanNiles

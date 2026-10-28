module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellComparison.PairedGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellComparison.MaximalGeometry

public import Theory.GroupTheory.CommutatorPreimage


/-!
# Campbell's paired replacement centralizers

The transferred fixed subgroup C_V′(S′) centralizes the common Thompson
group. Its containment in the first core Thompson group therefore puts
it in the first F=Ω₁(Z(J(O₂(H)))). For any maximum elementary A, form
A₀=(A∩O₂(H))F and A₁=F′ C_A₀(F′), using the literal transfer of F′.
Both are maximum elementary; A₁ lies in O₂(H), contains F and satisfies
[A,A₁]≤F. Every F′ conjugate lies in J(O₂(H)), so F centralizes it.
Consequently A normalizes C_A₁(F′ᵍ) for every g.

This is the part of Campbell II.5.2 used to construct the two competing
replacements in II.5.3. Source: *Pushing up in Finite Groups* (1979),
printed pp.27–28; Aschbacher–Smith C.1.17–18, printed p.126.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {J H H' : Type*} [Group J] [Group H] [Finite H] [Group H'] [Finite H']
  {B B' : Type*} [Group B] [Finite B] [Group B'] [Finite B']
  {e : B →* H} {e' : B' →* H'}
  {F F' : Type} [Field F] [Finite F] [CharP F 2] [Field F'] [Finite F'] [CharP F' 2]

theorem InLocalClass.paired_fixed_le_first_campbellF (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H) :
    d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H')) ≤ Campbell.F H := by
  let Y := d.transfer d' (Campbell.F H')
  let Z := d.transfer d' (Campbell.V H' ⊓ centralizer (d'.sylow : Set H'))
  have hZY : Z ≤ Y := map_mono (comap_mono (inf_le_left.trans Campbell.V_le_F))
  have hYR : Y ≤ Campbell.J (pCore 2 H) := by
    have hh := (h.paired_conjugates_in_core_thompson hB m h' hB' m' d d' hV 1).1
    intro y hy
    simpa using hh (mem_map_of_mem (MulAut.conj (1 : H)).toMonoidHom hy)
  have hRJ : Campbell.J (pCore 2 H) ≤ d.marking.range := by
    rw [d.range_eq]
    exact sSup_le fun A hA => le_sSup
      (d.core_maxFamily_subset_of_fixedIndex (h.omegaFixedIndexBound hB d) hA)
  rintro z ⟨a,ha,rfl⟩
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  refine ⟨hYR (hZY ⟨a,ha,rfl⟩),?_,?_⟩
  · have hp : (d'.marking a)^2=1 := by
      let : IsElementaryAbelian 2 (Campbell.F H') := omegaOneCenterAmbient_elementaryAbelian _
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (Campbell.V_le_F ha.1)
    have hpa : a^2=1 := d'.injective (by simpa only [map_pow,map_one] using hp)
    rw [←map_pow,hpa,map_one]
  · intro r hr
    obtain ⟨b,rfl⟩ := hRJ hr
    have hbs : d'.marking b ∈ d'.sylow := by
      have hj : d'.marking b ∈ Campbell.J (d'.sylow : Subgroup H') := d'.range_eq ▸ (show d'.marking b ∈ d'.marking.range from ⟨b,rfl⟩)
      exact (show Campbell.J (d'.sylow : Subgroup H') ≤ (d'.sylow : Subgroup H') from
        sSup_le fun _ hA => hA.1) hj
    have hh := ha.2 _ hbs
    have hba : b*a=a*b := d'.injective (by simpa only [map_mul] using hh)
    rw [←map_mul,hba,map_mul]


theorem InLocalClass.paired_replacement_geometry (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (h' : InLocalClass e') (hB' : IsBaumannFixed B')
    (m' : NaturalModel e' F') (d : Campbell.Embedding J H) (d' : Campbell.Embedding J H')
    (hS' : (d'.sylow : Subgroup H') = e'.range)
    (hV : d.transfer d' (Campbell.V H') ≤ pCore 2 H)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) :
    let Y := d.transfer d' (Campbell.F H')
    let A₀ := (A ⊓ pCore 2 H) ⊔ Campbell.F H
    let A₁ := Y ⊔ (A₀ ⊓ centralizer (Y : Set H))
    A₀ ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H) ∧
      A₁ ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H) ∧
      A₁ ≤ pCore 2 H ∧ Campbell.F H ≤ A₁ ∧ ⁅A,A₁⁆ ≤ Campbell.F H ∧
      ∀ g : H, A ≤ normalizer (A₁ ⊓ centralizer (Y.map (MulAut.conj g).toMonoidHom : Set H) : Set H) := by
  dsimp only
  let Y := d.transfer d' (Campbell.F H')
  let A₀ := (A ⊓ pCore 2 H) ⊔ Campbell.F H
  let A₁ := Y ⊔ (A₀ ⊓ centralizer (Y : Set H))
  have hc := h.paired_core_geometry hB m h' hB' m' d d' hV
  have hA₀ : A₀ ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H) := by
    rw [show A₀ = (A ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H) from
      h.campbellF_replacement_eq_omegaCore hB d A hA]
    exact h.omegaCore_replacement_maximal hB d A hA
  have hA₁ := h'.paired_campbellF_replacement hB' m' d d' A₀ hA₀
  have hA₀Q : A₀ ≤ pCore 2 H := sup_le inf_le_right Campbell.F_le_pCore
  have hA₁Q : A₁ ≤ pCore 2 H := sup_le hc.1 (inf_le_left.trans hA₀Q)
  have hFA₁ : Campbell.F H ≤ A₁ :=
    (le_inf le_sup_right (le_centralizer_iff.mp hc.2.1)).trans le_sup_right
  let : (Campbell.F H).Normal := Campbell.F_normal
  let D := commutatorPreimage (⊤ : Subgroup H) A (Campbell.F H)
  have hFD : Campbell.F H ≤ D := le_commutatorPreimage le_top (commutator_le_left _ _)
  have hAD : A ≤ D := by
    apply le_commutatorPreimage le_top
    let : IsElementaryAbelian 2 A := hA.2.1
    rw [commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff_isMulCommutative.mpr inferInstance)]
    exact bot_le
  have hA₀D : A₀ ≤ D := sup_le (inf_le_left.trans hAD) hFD
  have hYD : Y ≤ D := by
    apply le_commutatorPreimage le_top
    rw [commutator_comm]
    rcases h'.paired_campbellF_commutator_dichotomy hB' m' d d' hS' A hA with hz | hz
    · exact hz.le.trans bot_le
    · exact hz.le.trans (InLocalClass.paired_fixed_le_first_campbellF h hB m h' hB' m' d d' hV)
  have hA₁D : A₁ ≤ D := sup_le hYD (inf_le_left.trans hA₀D)
  have hcomm : ⁅A,A₁⁆ ≤ Campbell.F H := by
    rw [commutator_comm]
    exact (commutator_mono hA₁D le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)
  refine ⟨hA₀,hA₁,hA₁Q,hFA₁,hcomm,?_⟩
  intro g
  change A ≤ normalizer ((A₁ ⊓ centralizer (Y.map (MulAut.conj g).toMonoidHom : Set H) : Subgroup H) : Set H)
  apply le_normalizer_iff_commutator_le_right.mpr
  have hFR : Campbell.F H ≤ centralizer (Campbell.J (pCore 2 H) : Set H) :=
    fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).2.2
  have hFC : Campbell.F H ≤ centralizer (Y.map (MulAut.conj g).toMonoidHom : Set H) :=
    hFR.trans (centralizer_le (h.paired_conjugates_in_core_thompson hB m h' hB' m' d d' hV g).1)
  exact (commutator_mono le_rfl inf_le_left).trans (hcomm.trans (le_inf hFA₁ hFC))

end CFSG.Quasithin.ChapterC.GlaubermanNiles

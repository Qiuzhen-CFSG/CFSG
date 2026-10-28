module
public import Theory.GroupTheory.NormalSymmetricThreeEscape
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortBlock
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry

/-!
# Uniqueness of the original Thompson supplement

The already constructed local product and five-dimensional marking give
H/O₂(H)≅S₃×S₃, I/O₂(I)≅S₃ and (H∩M)/O₂(H∩M)≅S₃, for the literal
H=C_G(z), M=N_G(L) and I=⟨J(R₁)^H⟩. The two parabolics above the common
Sylow show that every overgroup of T in H escaping M contains IT.
Interval closure in the actual family H(T) then proves that IT belongs
to HStar(T,M) and is its unique member contained in H.

The final application supplies the product and quotient premises using
the checked short-block theorem. This proves the uniqueness clause of
13.4.8(3) on that branch without assuming minimality, uniqueness, or IT's
properness. The earlier Chapter12/13.3 and 13.4.2 inputs retain final
discharge with qt-d-1341-fixed-core-source. The larger-kernel exclusions,
original R₁ placement, marked C₃ chamber and ambient involution-fusion
assembly remain with qt-d-1341-solvable-source; full 13.4.8–9 is incomplete.

Source: Aschbacher–Smith 13.4.8(3), printed p.905; HStar is Definition3.0.1,
printed p.571, and interval closure is 3.1.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual local product has exactly the source minimal escaping overgroup IT. -/
theorem centralizer_thompson_unique_of_source_product
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcore : IsPGroup 2 (centralCore L)) (z : V)
    (hz : z.val ∉ centralizer (L : Set G))
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (R : Subgroup G) (hRT : R ≤ T)
    (hquot :
      let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z.val} : Set G))
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)))
    (hprod :
      let H := centralizer ({z.val} : Set G)
      H = firstCentralizerResidual L z.val ⊔
        conjugateSpanBy (elementaryAbelianMaxJ R) H ⊔ (T : Subgroup G))
    (hinter : centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G) =
      firstCentralizerResidual L z.val ⊔ (T : Subgroup G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    I ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ H →
        (Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ↔
          Y = I ⊔ (T : Subgroup G)) := by
  let H := centralizer ({z.val} : Set G)
  let K := H ⊓ normalizer (L : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hzT
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  have hKH : K ≤ H := inf_le_left
  let N := I.subgroupOf H
  let A := K.subgroupOf H
  let S := T.subtype hTH
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hIH).mpr
    (le_normalizer_conjugateSpanBy _ _)
  have hSA : (S : Subgroup H) ≤ A := by
    intro t ht
    change t.val ∈ K
    rw [show K = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) from hinter]
    exact (show (T : Subgroup G) ≤ firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
      from le_sup_right) ht
  have hA : A ≠ ⊤ := by
    intro he
    apply hout
    intro a ha
    exact (show (⟨a,ha⟩ : H) ∈ A from he ▸ mem_top _).2
  have hgen : N ⊔ A = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hIH,map_subgroupOf_eq_of_le hKH,
      ← MonoidHom.range_eq_map,range_subtype]
    rw [show K = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) from hinter,
      ← sup_assoc,sup_comm I]
    exact hprod.symm
  obtain ⟨eI⟩ := hquot
  let eN := subgroupOfEquivOfLe hIH
  obtain ⟨eK⟩ := normalizer_centralizer_quotient D m hcore z hz hinter
  let eA := subgroupOfEquivOfLe hKH
  obtain ⟨eH⟩ := centralizer_pair_quotient_of_source_product D m hcore z hz hzT
    R hRT ⟨eI⟩ hprod hinter hout
  obtain ⟨hn,_,hcontrol⟩ := normal_symmetricThree_supplement_controls_escape eH N A
    ((QuotientGroup.congr _ _ eN (pCore_map_iso 2 eN)).trans eI)
    ((QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans eK) S hSA hA hgen
  have hjoin : (N ⊔ (S : Subgroup H)).map H.subtype = I ⊔ (T : Subgroup G) := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hIH,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH]
  have hQH : I ⊔ (T : Subgroup G) ≤ H := sup_le hIH hTH
  have hQout : ¬ I ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) := by
    intro hh
    apply hn
    intro x hx
    exact ⟨x.property,hh (hjoin ▸ mem_map_of_mem H.subtype hx)⟩
  have hcontain (Y : Subgroup G) (hYH : Y ≤ H) (hTY : (T : Subgroup G) ≤ Y)
      (hYout : ¬ Y ≤ normalizer (L : Set G)) : I ⊔ (T : Subgroup G) ≤ Y := by
    have hi := hcontrol (Y.subgroupOf H) (fun x hx => hTY hx) (by
      intro hh
      apply hYout
      intro x hx
      exact (hh (show (⟨x,hYH hx⟩ : H) ∈ Y.subgroupOf H from hx)).2)
    have hm := map_mono (f := H.subtype) hi
    rwa [hjoin,map_subgroupOf_eq_of_le hYH] at hm
  have hQmem := Chapter3.mem_HOver_of_sylow_interval T
    (show (T : Subgroup G) ≤ I ⊔ (T : Subgroup G) from le_sup_right) hQH
    (centralizer_mem_HOver hzT (fun he => hz (he ▸ one_mem _)))
  have hstar : I ⊔ (T : Subgroup G) ∈ Chapter3.HStar
      (T : Subgroup G) (normalizer (L : Set G)) := by
    refine ⟨⟨hQmem,hQout⟩,?_⟩
    intro Y hY hYQ
    exact hcontain Y (hYQ.trans hQH) hY.1.2 hY.2
  refine ⟨hstar,?_⟩
  intro Y hYH
  constructor
  · intro hY
    have hQY := hcontain Y hYH hY.1.1.2 hY.1.2
    exact le_antisymm (hY.2 ⟨hQmem,hQout⟩ hQY) hQY
  · rintro rfl
    exact hstar


universe u

/-- The checked short-block product discharges all local premises for IT uniqueness. -/
theorem centralizer_thompson_unique_of_short_block
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z.val} : Set G)).pCoreIn 2 ≤ R)
    (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G)))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hAN : firstCentralizerResidual L z.val ≤ normalizer (R : Set G))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3)
    (h1342 : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    I ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ H →
        (Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ↔
          Y = I ⊔ (T : Subgroup G)) := by
  obtain ⟨_,hI,_,hprod,hinter,_⟩ := centralizer_pair_quotient_of_short_block
    h₀ h structural D m hb z hz hzL R hRT hnR hQR hVJ hsolv hkernel hout hindex
    hAN h1339 h1342
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_short_core_marking D m hb]
    exact pCore_isPGroup
  exact centralizer_thompson_unique_of_source_product D m hcore z hzL hz R hRT
    hI hprod hinter hout

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

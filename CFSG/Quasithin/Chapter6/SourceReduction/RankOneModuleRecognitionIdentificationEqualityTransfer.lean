module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityPreparation
public import Theory.GroupTheory.AbelianWeakClosureFusion
public import Theory.GroupTheory.InvolutionFusionCover

/-!
# Transfer exclusion for the elementary-four centralizer alternative

Write K = ⟨V^H⟩, P = O₂(K), D = C_H(K), Q = O₂(LT), and
T₀ = P(T ∩ L), with all displayed subgroups embedded in the original G.
The source's C_R(K), for R = C_H(P/Z(P)), is this same D.

When Q is elementary and weakly closed, Burnside fusion keeps a conjugate
of z inside V because N_G(Q) normalizes V. An involution r in D outside
⟨z⟩ lies outside V. If all involutions of the index-two subgroup T₀ are
conjugate to z, Thompson transfer gives the contradiction. The theorem
retains the exact weak-closure, normalization, index and fusion premises;
constructing them in the source configuration remains an obligation.

Source: Aschbacher--Smith, the last paragraph of 6.2.13, printed p.688.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

@[expose] def equalityTransferSubgroup (T L R : Subgroup G) (z : G) : Subgroup G :=
  (equalityCore L R z).map (centralizer ({z} : Set G)).subtype ⊔ T ⊓ L

@[expose] def equalityCentralizer (L R : Subgroup G) (z : G) : Subgroup G :=
  (centralizer (equalityLayerClosure L R z : Set (centralizer ({z} : Set G)))).map
    (centralizer ({z} : Set G)).subtype

theorem elementary_four_centralizer_excluded
    (h611 : Hypothesis611 κ T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hQ : IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2))
    (hDQ : equalityCentralizer L R z ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hDV : equalityCentralizer L R z ⊓ layer L R ≤ zpowers z)
    (hweak : ∀ g : G,
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).conjBy g ≤ (T : Subgroup G) →
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).conjBy g = (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hnorm : normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤
      normalizer (layer L R : Set G))
    (hindex : (equalityTransferSubgroup (T : Subgroup G) L R z).relIndex
      (T : Subgroup G) = 2)
    (hfusion : ∀ t ∈ equalityTransferSubgroup (T : Subgroup G) L R z,
      orderOf t = 2 → IsConj z t) :
    Nat.card (equalityCentralizer L R z) ≠ 4 := by
  intro hfour
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := equalityCentralizer L R z
  let : IsElementaryAbelian 2 Q := hQ
  let : IsSimpleGroup G := h611.simpleQTKE.simple
  have hZQ : ZS (T : Subgroup G) L R ≤ Q :=
    inf_le_left.trans (h611.layer_le_V.trans (reduced_le_core h611.V_mem))
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using hh
  have hnot : ¬ D ≤ zpowers z := by
    intro hd
    have hc := card_le_of_le hd
    rw [Nat.card_zpowers, horder, hfour] at hc
    omega
  obtain ⟨r, hrD, hrZ⟩ := SetLike.not_le_iff_exists.mp hnot
  have hrV : r ∉ layer L R := fun hr => hrZ (hDV ⟨hrD, hr⟩)
  have hrQ : r ∈ Q := hDQ hrD
  have hr2 : orderOf r = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian r hrQ)
    (fun hr => hrZ (hr ▸ (zpowers z).one_mem))
  have hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 :=
    index_ne_two_of_nonabelian_simple h611.simpleQTKE.nonabelian
  obtain ⟨t, ht, hrt⟩ := T.exists_isConj_mem_of_index_two_ambient hno
    ((equalityTransferSubgroup (T : Subgroup G) L R z).subgroupOf (T : Subgroup G))
    hindex r hr2
  have ht2 : orderOf (t : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hrt
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq r).trans hr2
  have hzr : IsConj z r := (hfusion t ht ht2).trans hrt.symm
  obtain ⟨g, hg, he⟩ := T.normalizer_fuses_of_abelian_weakly_closed Q hQT hweak
    (hZQ hz) hrQ hzr
  exact hrV (he ▸ ((mem_normalizer_iff_map_conj_eq.mp (hnorm hg)) ▸
    mem_map_of_mem (MulAut.conj g).toMonoidHom hz.1))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
